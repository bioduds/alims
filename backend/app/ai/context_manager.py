"""
ALims Central AI Brain - Context Manager
Manages persistent context and memory for intelligent interactions
"""

import json
import logging
from typing import Dict, Any, List, Optional
from datetime import datetime, timedelta
from pathlib import Path
import sqlite3
from dataclasses import dataclass, asdict
from collections import deque

logger = logging.getLogger(__name__)


@dataclass
class ConversationExchange:
    """Single conversation exchange"""

    timestamp: datetime
    user_message: str
    assistant_response: str
    context_type: str
    metadata: Dict[str, Any]


@dataclass
class UserProfile:
    """User profile and preferences"""

    user_id: str = "default_user"
    preferences: Dict[str, Any] = None
    interaction_patterns: Dict[str, Any] = None
    created_at: datetime = None
    last_updated: datetime = None

    def __post_init__(self):
        if self.preferences is None:
            self.preferences = {}
        if self.interaction_patterns is None:
            self.interaction_patterns = {}
        if self.created_at is None:
            self.created_at = datetime.now()
        if self.last_updated is None:
            self.last_updated = datetime.now()


@dataclass
class SystemState:
    """Current system state information"""

    active_agents: List[str] = None
    system_health: Dict[str, Any] = None
    recent_activities: List[str] = None
    performance_metrics: Dict[str, Any] = None
    last_updated: datetime = None

    def __post_init__(self):
        if self.active_agents is None:
            self.active_agents = []
        if self.system_health is None:
            self.system_health = {"status": "operational"}
        if self.recent_activities is None:
            self.recent_activities = []
        if self.performance_metrics is None:
            self.performance_metrics = {}
        if self.last_updated is None:
            self.last_updated = datetime.now()


class ConversationHistory:
    """Manages conversation history with intelligent retrieval"""

    def __init__(self, max_size: int = 50):
        self.max_size = max_size
        self.exchanges = deque(maxlen=max_size)
        self.db_path = Path("data/context/conversation_history.db")
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self._init_database()

    def _init_database(self):
        """Initialize SQLite database for persistent storage"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                conn.execute(
                    """
                    CREATE TABLE IF NOT EXISTS conversations (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        timestamp TEXT NOT NULL,
                        user_message TEXT NOT NULL,
                        assistant_response TEXT NOT NULL,
                        context_type TEXT NOT NULL,
                        metadata TEXT NOT NULL
                    )
                """
                )
                conn.execute(
                    """
                    CREATE INDEX IF NOT EXISTS idx_timestamp 
                    ON conversations(timestamp)
                """
                )
                conn.execute(
                    """
                    CREATE INDEX IF NOT EXISTS idx_context_type 
                    ON conversations(context_type)
                """
                )
        except Exception as e:
            logger.error(f"Failed to initialize conversation database: {e}")

    def add_exchange(self, exchange: ConversationExchange):
        """Add new conversation exchange"""
        self.exchanges.append(exchange)
        self._persist_exchange(exchange)

    def _persist_exchange(self, exchange: ConversationExchange):
        """Persist exchange to database"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                conn.execute(
                    """
                    INSERT INTO conversations 
                    (timestamp, user_message, assistant_response, context_type, metadata)
                    VALUES (?, ?, ?, ?, ?)
                """,
                    (
                        exchange.timestamp.isoformat(),
                        exchange.user_message,
                        exchange.assistant_response,
                        exchange.context_type,
                        json.dumps(exchange.metadata),
                    ),
                )
        except Exception as e:
            logger.error(f"Failed to persist conversation exchange: {e}")

    def get_recent(self, limit: int = 10) -> List[ConversationExchange]:
        """Get recent conversation exchanges"""
        return list(self.exchanges)[-limit:]

    def search_by_content(
        self, query: str, limit: int = 5
    ) -> List[ConversationExchange]:
        """Search conversations by content"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                cursor = conn.execute(
                    """
                    SELECT timestamp, user_message, assistant_response, context_type, metadata
                    FROM conversations
                    WHERE user_message LIKE ? OR assistant_response LIKE ?
                    ORDER BY timestamp DESC
                    LIMIT ?
                """,
                    (f"%{query}%", f"%{query}%", limit),
                )

                results = []
                for row in cursor.fetchall():
                    results.append(
                        ConversationExchange(
                            timestamp=datetime.fromisoformat(row[0]),
                            user_message=row[1],
                            assistant_response=row[2],
                            context_type=row[3],
                            metadata=json.loads(row[4]),
                        )
                    )
                return results
        except Exception as e:
            logger.error(f"Failed to search conversations: {e}")
            return []

    def get_by_context_type(
        self, context_type: str, limit: int = 10
    ) -> List[ConversationExchange]:
        """Get conversations by context type"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                cursor = conn.execute(
                    """
                    SELECT timestamp, user_message, assistant_response, context_type, metadata
                    FROM conversations
                    WHERE context_type = ?
                    ORDER BY timestamp DESC
                    LIMIT ?
                """,
                    (context_type, limit),
                )

                results = []
                for row in cursor.fetchall():
                    results.append(
                        ConversationExchange(
                            timestamp=datetime.fromisoformat(row[0]),
                            user_message=row[1],
                            assistant_response=row[2],
                            context_type=row[3],
                            metadata=json.loads(row[4]),
                        )
                    )
                return results
        except Exception as e:
            logger.error(f"Failed to get conversations by context type: {e}")
            return []


class AgentKnowledge:
    """Manages knowledge about agents and their capabilities"""

    def __init__(self):
        self.agents_info = {}
        self.capabilities_map = {}
        self.performance_history = {}
        self.db_path = Path("data/context/agent_knowledge.db")
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self._init_database()
        self._load_agent_knowledge()

    def _init_database(self):
        """Initialize agent knowledge database"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                conn.execute(
                    """
                    CREATE TABLE IF NOT EXISTS agents (
                        agent_id TEXT PRIMARY KEY,
                        name TEXT NOT NULL,
                        specialization TEXT NOT NULL,
                        capabilities TEXT NOT NULL,
                        performance_metrics TEXT NOT NULL,
                        created_at TEXT NOT NULL,
                        last_updated TEXT NOT NULL
                    )
                """
                )
        except Exception as e:
            logger.error(f"Failed to initialize agent knowledge database: {e}")

    def _load_agent_knowledge(self):
        """Load agent knowledge from database"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                cursor = conn.execute("SELECT * FROM agents")
                for row in cursor.fetchall():
                    agent_id = row[0]
                    self.agents_info[agent_id] = {
                        "name": row[1],
                        "specialization": row[2],
                        "capabilities": json.loads(row[3]),
                        "performance_metrics": json.loads(row[4]),
                        "created_at": datetime.fromisoformat(row[5]),
                        "last_updated": datetime.fromisoformat(row[6]),
                    }
        except Exception as e:
            logger.error(f"Failed to load agent knowledge: {e}")

    def update_agent_info(self, agent_id: str, info: Dict[str, Any]):
        """Update information about an agent"""
        self.agents_info[agent_id] = info
        self._persist_agent_info(agent_id, info)

    def _persist_agent_info(self, agent_id: str, info: Dict[str, Any]):
        """Persist agent information to database"""
        try:
            with sqlite3.connect(self.db_path) as conn:
                conn.execute(
                    """
                    INSERT OR REPLACE INTO agents
                    (agent_id, name, specialization, capabilities, performance_metrics, created_at, last_updated)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                    (
                        agent_id,
                        info.get("name", "Unknown"),
                        info.get("specialization", "General"),
                        json.dumps(info.get("capabilities", [])),
                        json.dumps(info.get("performance_metrics", {})),
                        info.get("created_at", datetime.now()).isoformat(),
                        datetime.now().isoformat(),
                    ),
                )
        except Exception as e:
            logger.error(f"Failed to persist agent info: {e}")

    def get_agents_by_capability(self, capability: str) -> List[str]:
        """Get agents that have a specific capability"""
        matching_agents = []
        for agent_id, info in self.agents_info.items():
            if capability in info.get("capabilities", []):
                matching_agents.append(agent_id)
        return matching_agents


class ContextManager:
    """Manages persistent context and memory for Central AI Brain"""

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.max_conversation_history = config.get("max_conversation_history", 50)
        self.context_refresh_interval = config.get("context_refresh_interval", 3600)
        self.memory_persistence = config.get("memory_persistence", True)
        self.max_context_tokens = config.get("max_context_tokens", 6000)

        # Initialize components
        self.user_profile = UserProfile()
        self.conversation_history = ConversationHistory(self.max_conversation_history)
        self.system_state = SystemState()
        self.agent_knowledge = AgentKnowledge()

        # Context cache
        self.context_cache = {}
        self.last_context_refresh = datetime.now()

        logger.info("ContextManager initialized")

    async def build_context(self, interaction_type: str, **kwargs) -> str:
        """Build contextual prompt for different interaction types"""

        # Check if we need to refresh context
        if (
            datetime.now() - self.last_context_refresh
        ).seconds > self.context_refresh_interval:
            await self._refresh_context()

        context_parts = []

        # Add system state
        context_parts.append(
            f"System Status: {self.system_state.system_health.get('status', 'unknown')}"
        )
        context_parts.append(
            f"Active Agents: {', '.join(self.system_state.active_agents) if self.system_state.active_agents else 'None'}"
        )

        # Add user profile information
        if self.user_profile.preferences:
            context_parts.append(
                f"User Preferences: {json.dumps(self.user_profile.preferences)}"
            )

        # Add relevant conversation history
        if interaction_type in ["chat", "user_interface"]:
            recent_exchanges = self.conversation_history.get_recent(5)
            if recent_exchanges:
                context_parts.append("Recent Conversation:")
                for exchange in recent_exchanges[-3:]:  # Last 3 exchanges
                    context_parts.append(f"  User: {exchange.user_message[:100]}...")
                    context_parts.append(
                        f"  Assistant: {exchange.assistant_response[:100]}..."
                    )

        # Add agent knowledge for orchestration
        if interaction_type == "agent_orchestration":
            available_agents = list(self.agent_knowledge.agents_info.keys())
            if available_agents:
                context_parts.append(f"Available Agents: {', '.join(available_agents)}")

        # Add specific context from kwargs
        for key, value in kwargs.items():
            if key not in ["user_message", "system_prompt"]:
                context_parts.append(f"{key.replace('_', ' ').title()}: {value}")

        return "\n".join(context_parts)

    async def update_context(self, interaction: Dict[str, Any]):
        """Update persistent context with new information"""

        # Update conversation history
        if "user_message" in interaction and "assistant_response" in interaction:
            exchange = ConversationExchange(
                timestamp=datetime.now(),
                user_message=interaction["user_message"],
                assistant_response=interaction["assistant_response"],
                context_type=interaction.get("context_type", "general"),
                metadata=interaction.get("metadata", {}),
            )
            self.conversation_history.add_exchange(exchange)

        # Update system state if provided
        if "system_state" in interaction:
            self.system_state = SystemState(**interaction["system_state"])

        # Update agent knowledge if provided
        if "agent_info" in interaction:
            for agent_id, info in interaction["agent_info"].items():
                self.agent_knowledge.update_agent_info(agent_id, info)

        # Update user profile if provided
        if "user_preferences" in interaction:
            self.user_profile.preferences.update(interaction["user_preferences"])
            self.user_profile.last_updated = datetime.now()

    async def get_relevant_history(
        self, query: str, limit: int = 10
    ) -> List[ConversationExchange]:
        """Get relevant conversation history for current query"""

        # First try content-based search
        relevant_exchanges = self.conversation_history.search_by_content(
            query, limit // 2
        )

        # Add recent exchanges for context
        recent_exchanges = self.conversation_history.get_recent(limit // 2)

        # Combine and deduplicate
        all_exchanges = relevant_exchanges + recent_exchanges
        seen_timestamps = set()
        unique_exchanges = []

        for exchange in all_exchanges:
            if exchange.timestamp not in seen_timestamps:
                unique_exchanges.append(exchange)
                seen_timestamps.add(exchange.timestamp)

        # Sort by timestamp and return limited results
        unique_exchanges.sort(key=lambda x: x.timestamp, reverse=True)
        return unique_exchanges[:limit]

    async def _refresh_context(self):
        """Refresh context cache and system state"""
        try:
            # Update system state (this would integrate with actual system monitoring)
            self.system_state.last_updated = datetime.now()

            # Clear old context cache
            self.context_cache.clear()

            self.last_context_refresh = datetime.now()
            logger.info("Context refreshed successfully")

        except Exception as e:
            logger.error(f"Failed to refresh context: {e}")

    def get_context_summary(self) -> Dict[str, Any]:
        """Get summary of current context state"""
        return {
            "user_profile": {
                "user_id": self.user_profile.user_id,
                "preferences_count": len(self.user_profile.preferences),
                "last_updated": self.user_profile.last_updated.isoformat(),
            },
            "conversation_history": {
                "total_exchanges": len(self.conversation_history.exchanges),
                "recent_activity": len(self.conversation_history.get_recent(10)),
            },
            "system_state": {
                "active_agents": len(self.system_state.active_agents),
                "system_health": self.system_state.system_health.get(
                    "status", "unknown"
                ),
                "last_updated": self.system_state.last_updated.isoformat(),
            },
            "agent_knowledge": {
                "known_agents": len(self.agent_knowledge.agents_info),
                "capabilities_tracked": len(self.agent_knowledge.capabilities_map),
            },
        }

    async def cleanup_old_data(self, days_to_keep: int = 30):
        """Clean up old conversation data"""
        cutoff_date = datetime.now() - timedelta(days=days_to_keep)

        try:
            with sqlite3.connect(self.conversation_history.db_path) as conn:
                conn.execute(
                    """
                    DELETE FROM conversations 
                    WHERE timestamp < ?
                """,
                    (cutoff_date.isoformat(),),
                )

            logger.info(f"Cleaned up conversation data older than {days_to_keep} days")

        except Exception as e:
            logger.error(f"Failed to cleanup old data: {e}")


# Utility functions
async def create_context_manager(config: Dict[str, Any]) -> ContextManager:
    """Create and initialize a ContextManager"""
    return ContextManager(config)
