"""
ALims Conversation Memory System
Provides persistent chat history, context management, and intelligent
conversation continuity
"""

import uuid
from datetime import datetime, timedelta
from typing import List, Dict
from sqlalchemy import (
    create_engine, Column, String, Text, DateTime, Integer, Float, Boolean
)
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import sessionmaker, Session
from sqlalchemy.dialects.sqlite import JSON
import logging

logger = logging.getLogger(__name__)

Base = declarative_base()


class ConversationSession(Base):
    """Represents a conversation session"""
    __tablename__ = 'conversation_sessions'
    
    id = Column(String, primary_key=True, 
                default=lambda: str(uuid.uuid4()))
    user_id = Column(String, default="default_user")
    session_name = Column(String)
    created_at = Column(DateTime, default=datetime.utcnow)
    last_activity = Column(DateTime, default=datetime.utcnow)
    is_active = Column(Boolean, default=True)
    total_messages = Column(Integer, default=0)
    session_metadata = Column(JSON, default={})


class ConversationMessage(Base):
    """Represents a single message in a conversation"""
    __tablename__ = 'conversation_messages'
    
    id = Column(String, primary_key=True, 
                default=lambda: str(uuid.uuid4()))
    session_id = Column(String, nullable=False)
    message_index = Column(Integer, nullable=False)  # Order within session
    sender = Column(String, nullable=False)  # 'user' or 'ai'
    content = Column(Text, nullable=False)
    timestamp = Column(DateTime, default=datetime.utcnow)
    message_type = Column(String, default="text")  # text/visualization/system
    visualization_data = Column(JSON, nullable=True)
    context_used = Column(JSON, nullable=True)  # Context used for message
    response_time = Column(Float, nullable=True)
    tokens_used = Column(Integer, nullable=True)


class ConversationContext(Base):
    """Stores conversation context and topics"""
    __tablename__ = 'conversation_context'
    
    id = Column(String, primary_key=True, 
                default=lambda: str(uuid.uuid4()))
    session_id = Column(String, nullable=False)
    topic = Column(String, nullable=False)
    context_summary = Column(Text)
    importance_score = Column(Float, default=1.0)
    created_at = Column(DateTime, default=datetime.utcnow)
    last_referenced = Column(DateTime, default=datetime.utcnow)
    reference_count = Column(Integer, default=1)


class ConversationMemoryManager:
    """Manages conversation memory, context, and history"""
    
    def __init__(self, db_path: str = "data/conversations.db"):
        self.db_path = db_path
        self.engine = create_engine(f'sqlite:///{db_path}', echo=False)
        Base.metadata.create_all(self.engine)
        self.SessionLocal = sessionmaker(
            autocommit=False, autoflush=False, bind=self.engine
        )
        self.current_session_id = None
        
        logger.info(
            f"ConversationMemoryManager initialized with database: {db_path}"
        )
    
    def get_db_session(self) -> Session:
        """Get database session"""
        return self.SessionLocal()
    
    def create_session(self, user_id: str = "default_user", session_name: str = None) -> str:
        """Create a new conversation session"""
        db = self.get_db_session()
        try:
            session_name = session_name or f"Session {datetime.now().strftime('%Y-%m-%d %H:%M')}"
            
            session = ConversationSession(
                user_id=user_id,
                session_name=session_name,
                session_metadata={"created_via": "ai_chat"}
            )
            
            db.add(session)
            db.commit()
            db.refresh(session)
            
            self.current_session_id = session.id
            logger.info(f"Created new conversation session: {session.id}")
            return session.id
            
        except Exception as e:
            db.rollback()
            logger.error(f"Error creating session: {e}")
            raise
        finally:
            db.close()
    
    def get_or_create_session(self, user_id: str = "default_user") -> str:
        """Get active session or create new one"""
        if self.current_session_id:
            return self.current_session_id
            
        db = self.get_db_session()
        try:
            # Try to find an active session from today
            today = datetime.now().date()
            active_session = db.query(ConversationSession).filter(
                ConversationSession.user_id == user_id,
                ConversationSession.is_active.is_(True),
                ConversationSession.last_activity >= today
            ).first()
            
            if active_session:
                self.current_session_id = active_session.id
                return active_session.id
            else:
                return self.create_session(user_id)
                
        except Exception as e:
            logger.error(f"Error getting/creating session: {e}")
            return self.create_session(user_id)
        finally:
            db.close()
    
    def add_message(self, content: str, sender: str, session_id: str = None, 
                   message_type: str = "text", visualization_data: Dict = None,
                   response_time: float = None) -> str:
        """Add a message to the conversation"""
        session_id = session_id or self.current_session_id or self.get_or_create_session()
        
        db = self.get_db_session()
        try:
            # Get next message index
            last_message = db.query(ConversationMessage).filter(
                ConversationMessage.session_id == session_id
            ).order_by(ConversationMessage.message_index.desc()).first()
            
            next_index = (last_message.message_index + 1) if last_message else 0
            
            message = ConversationMessage(
                session_id=session_id,
                message_index=next_index,
                sender=sender,
                content=content,
                message_type=message_type,
                visualization_data=visualization_data,
                response_time=response_time
            )
            
            db.add(message)
            
            # Update session activity
            session = db.query(ConversationSession).filter(
                ConversationSession.id == session_id
            ).first()
            if session:
                session.last_activity = datetime.utcnow()
                session.total_messages += 1
            
            db.commit()
            db.refresh(message)
            
            logger.debug(f"Added message {message.id} to session {session_id}")
            return message.id
            
        except Exception as e:
            db.rollback()
            logger.error(f"Error adding message: {e}")
            raise
        finally:
            db.close()
    
    def get_conversation_history(self, session_id: str = None, limit: int = 50) -> List[Dict]:
        """Get conversation history for a session"""
        session_id = session_id or self.current_session_id
        if not session_id:
            return []
        
        db = self.get_db_session()
        try:
            messages = db.query(ConversationMessage).filter(
                ConversationMessage.session_id == session_id
            ).order_by(ConversationMessage.message_index.desc()).limit(limit).all()
            
            history = []
            for msg in reversed(messages):  # Reverse to get chronological order
                history.append({
                    "id": msg.id,
                    "sender": msg.sender,
                    "content": msg.content,
                    "timestamp": msg.timestamp.isoformat(),
                    "message_type": msg.message_type,
                    "visualization_data": msg.visualization_data,
                    "response_time": msg.response_time
                })
            
            return history
            
        except Exception as e:
            logger.error(f"Error getting conversation history: {e}")
            return []
        finally:
            db.close()
    
    def get_context_for_prompt(self, session_id: str = None, max_messages: int = 10) -> str:
        """Get formatted context for AI prompt"""
        history = self.get_conversation_history(session_id, max_messages)
        
        if not history:
            return "This is the start of a new conversation."
        
        context_parts = ["Previous conversation context:"]
        
        for msg in history[-max_messages:]:  # Get last N messages
            sender_label = "Human" if msg["sender"] == "user" else "Assistant"
            timestamp = datetime.fromisoformat(msg["timestamp"]).strftime("%H:%M")
            
            if msg["message_type"] == "visualization":
                viz_type = msg.get("visualization_data", {}).get("type", "unknown")
                context_parts.append(f"[{timestamp}] {sender_label}: {msg['content']} (Generated {viz_type} visualization)")
            else:
                context_parts.append(f"[{timestamp}] {sender_label}: {msg['content']}")
        
        return "\n".join(context_parts)
    
    def add_context_topic(self, topic: str, summary: str, session_id: str = None, importance: float = 1.0):
        """Add a context topic for better conversation tracking"""
        session_id = session_id or self.current_session_id
        if not session_id:
            return
        
        db = self.get_db_session()
        try:
            # Check if topic already exists
            existing = db.query(ConversationContext).filter(
                ConversationContext.session_id == session_id,
                ConversationContext.topic == topic
            ).first()
            
            if existing:
                existing.last_referenced = datetime.utcnow()
                existing.reference_count += 1
                existing.importance_score = max(existing.importance_score, importance)
            else:
                context = ConversationContext(
                    session_id=session_id,
                    topic=topic,
                    context_summary=summary,
                    importance_score=importance
                )
                db.add(context)
            
            db.commit()
            
        except Exception as e:
            db.rollback()
            logger.error(f"Error adding context topic: {e}")
        finally:
            db.close()
    
    def get_session_info(self, session_id: str = None) -> Dict:
        """Get information about the current session"""
        session_id = session_id or self.current_session_id
        if not session_id:
            return {"error": "No active session"}
        
        db = self.get_db_session()
        try:
            session = db.query(ConversationSession).filter(
                ConversationSession.id == session_id
            ).first()
            
            if not session:
                return {"error": "Session not found"}
            
            # Get recent topics
            topics = db.query(ConversationContext).filter(
                ConversationContext.session_id == session_id
            ).order_by(ConversationContext.importance_score.desc()).limit(5).all()
            
            return {
                "session_id": session.id,
                "session_name": session.session_name,
                "created_at": session.created_at.isoformat(),
                "last_activity": session.last_activity.isoformat(),
                "total_messages": session.total_messages,
                "active_topics": [{"topic": t.topic, "summary": t.context_summary} for t in topics]
            }
            
        except Exception as e:
            logger.error(f"Error getting session info: {e}")
            return {"error": str(e)}
        finally:
            db.close()
    
    def cleanup_old_sessions(self, days_old: int = 30):
        """Clean up old inactive sessions"""
        db = self.get_db_session()
        try:
            cutoff_date = datetime.utcnow() - timedelta(days=days_old)
            
            old_sessions = db.query(ConversationSession).filter(
                ConversationSession.last_activity < cutoff_date,
                ConversationSession.is_active == False
            ).all()
            
            for session in old_sessions:
                # Delete messages and context for this session
                db.query(ConversationMessage).filter(
                    ConversationMessage.session_id == session.id
                ).delete()
                
                db.query(ConversationContext).filter(
                    ConversationContext.session_id == session.id
                ).delete()
                
                db.delete(session)
            
            db.commit()
            logger.info(f"Cleaned up {len(old_sessions)} old sessions")
            
        except Exception as e:
            db.rollback()
            logger.error(f"Error cleaning up old sessions: {e}")
        finally:
            db.close()

# Global instance
conversation_memory = ConversationMemoryManager() 