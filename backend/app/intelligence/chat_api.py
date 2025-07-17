"""
TLA+ Verified Main Interface Agent Chat API

This module provides a chat interface that uses the formally verified 
Main Interface Agent for all conversation handling and orchestration.
"""

import asyncio
import logging
from typing import Dict, List, Optional, Any
from datetime import datetime

from fastapi import FastAPI, HTTPException, WebSocket, WebSocketDisconnect
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
import json

from .main_interface_agent import (
    MainInterfaceAgent,
    RequestType,
    Priority,
    ConversationState,
    AgentState,
    CentralBrainState,
    create_main_interface_agent
)

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Global TLA+ verified agent instance
tla_agent: Optional[MainInterfaceAgent] = None

# Request/Response models
class ChatMessage(BaseModel):
    message: str
    conversation_id: Optional[str] = None
    user_id: Optional[str] = None
    request_type: Optional[str] = "SAMPLE_INQUIRY"
    priority: Optional[str] = "MEDIUM"

class ChatResponse(BaseModel):
    conversation_id: str
    response: str
    agent_info: Dict[str, Any]
    system_status: Dict[str, Any]
    timestamp: str

class SystemStatusResponse(BaseModel):
    status: Dict[str, Any]
    health: bool
    timestamp: str

# FastAPI app
app = FastAPI(
    title="ALIMS TLA+ Verified Chat API",
    description="Chat interface using formally verified Main Interface Agent",
    version="1.0.0"
)

# Configure CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

async def get_tla_agent() -> MainInterfaceAgent:
    """Get or create the TLA+ verified Main Interface Agent"""
    global tla_agent
    
    if tla_agent is None:
        logger.info("Initializing TLA+ verified Main Interface Agent...")
        tla_agent = await create_main_interface_agent(
            max_conversations=5,  # Allow more conversations for chat
            max_agents=4,
            max_requests=10,      # Allow more requests for chat
            max_responses=10
        )
        logger.info("TLA+ verified Main Interface Agent initialized successfully")
    
    return tla_agent

@app.on_event("startup")
async def startup_event():
    """Initialize the TLA+ verified agent on startup"""
    await get_tla_agent()
    logger.info("🚀 TLA+ Verified Chat API started successfully")

@app.post("/chat", response_model=ChatResponse)
async def chat_endpoint(message: ChatMessage):
    """
    Main chat endpoint using TLA+ verified Main Interface Agent
    
    This endpoint:
    1. Uses the TLA+ verified agent for all orchestration
    2. Follows formal specification for request processing
    3. Maintains conversation context with safety guarantees
    4. Provides real-time system status
    """
    try:
        agent = await get_tla_agent()
        
        # Start new conversation if none provided
        if not message.conversation_id:
            conversation_id = await agent.start_conversation(message.user_id)
        else:
            conversation_id = message.conversation_id
        
        # Convert string enums to proper enums
        request_type = RequestType(message.request_type)
        priority = Priority(message.priority)
        
        # Process the user request through TLA+ verified agent
        request_accepted = await agent.receive_user_request(
            conversation_id=conversation_id,
            content=message.message,
            request_type=request_type,
            priority=priority,
            user_id=message.user_id
        )
        
        if not request_accepted:
            raise HTTPException(
                status_code=503,
                detail="Request could not be processed - system at capacity"
            )
        
        # Process the request through TLA+ verified orchestration
        orchestrated = await agent.analyze_and_orchestrate()
        
        # Get conversation context
        conv_context = await agent.get_conversation_history(conversation_id)
        
        # Generate response based on conversation state
        response_text = await _generate_chat_response(agent, conversation_id, message.message, conv_context)
        
        # Get system status
        system_status = await agent.get_system_status()
        
        # Get active agent info
        agent_info = {
            "active_agents": list(conv_context.get("active_agents", [])) if conv_context else [],
            "request_count": conv_context.get("request_count", 0) if conv_context else 0,
            "response_count": conv_context.get("response_count", 0) if conv_context else 0
        }
        
        return ChatResponse(
            conversation_id=conversation_id,
            response=response_text,
            agent_info=agent_info,
            system_status=system_status,
            timestamp=datetime.now().isoformat()
        )
        
    except Exception as e:
        logger.error(f"Chat endpoint error: {e}")
        raise HTTPException(status_code=500, detail=str(e))

async def _generate_chat_response(
    agent: MainInterfaceAgent, 
    conversation_id: str, 
    user_message: str, 
    context: Optional[Dict[str, Any]]
) -> str:
    """
    Generate chat response using TLA+ verified agent orchestration
    """
    # Simulate agent responses for demonstration
    if context and context.get("active_agents"):
        active_agents = context["active_agents"]
        
        # Simulate responses from active agents
        for agent_id in active_agents:
            success = await agent.receive_agent_response(
                agent_id=agent_id,
                conversation_id=conversation_id,
                content=f"Processed request: {user_message[:50]}{'...' if len(user_message) > 50 else ''}",
                success=True,
                metadata={"processed_at": datetime.now().isoformat()}
            )
            
            if success:
                # Try to synthesize response
                synthesized = await agent.synthesize_and_respond()
                if synthesized:
                    return synthesized
    
    # Default response if no agents available
    return f"I'm analyzing your request: '{user_message}'. Let me connect you with the appropriate laboratory agents to help with your needs."

@app.get("/status", response_model=SystemStatusResponse)
async def get_system_status():
    """Get TLA+ verified system status"""
    try:
        agent = await get_tla_agent()
        status = await agent.get_system_status()
        health = agent.is_healthy()
        
        return SystemStatusResponse(
            status=status,
            health=health,
            timestamp=datetime.now().isoformat()
        )
    except Exception as e:
        logger.error(f"Status endpoint error: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/conversations")
async def get_active_conversations():
    """Get all active conversations"""
    try:
        agent = await get_tla_agent()
        conversations = await agent.get_active_conversations()
        return {
            "conversations": conversations,
            "total": len(conversations),
            "timestamp": datetime.now().isoformat()
        }
    except Exception as e:
        logger.error(f"Conversations endpoint error: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/conversations/{conversation_id}")
async def get_conversation_details(conversation_id: str):
    """Get detailed conversation information"""
    try:
        agent = await get_tla_agent()
        conversation = await agent.get_conversation_history(conversation_id)
        
        if not conversation:
            raise HTTPException(status_code=404, detail="Conversation not found")
        
        return conversation
    except Exception as e:
        logger.error(f"Conversation details error: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/conversations/{conversation_id}/complete")
async def complete_conversation(conversation_id: str):
    """Complete a conversation"""
    try:
        agent = await get_tla_agent()
        success = await agent.complete_conversation(conversation_id)
        
        if not success:
            raise HTTPException(status_code=404, detail="Conversation not found")
        
        return {
            "conversation_id": conversation_id,
            "status": "completed",
            "timestamp": datetime.now().isoformat()
        }
    except Exception as e:
        logger.error(f"Complete conversation error: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.websocket("/ws/chat")
async def websocket_chat(websocket: WebSocket):
    """
    WebSocket endpoint for real-time chat using TLA+ verified agent
    """
    await websocket.accept()
    agent = await get_tla_agent()
    conversation_id = None
    
    try:
        while True:
            # Receive message from client
            data = await websocket.receive_text()
            message_data = json.loads(data)
            
            user_message = message_data.get("message", "")
            user_id = message_data.get("user_id")
            
            # Start conversation if needed
            if not conversation_id:
                conversation_id = await agent.start_conversation(user_id)
            
            # Process message through TLA+ verified agent
            request_accepted = await agent.receive_user_request(
                conversation_id=conversation_id,
                content=user_message,
                request_type=RequestType.SAMPLE_INQUIRY,
                user_id=user_id
            )
            
            if request_accepted:
                # Process through orchestration
                await agent.analyze_and_orchestrate()
                
                # Get conversation context
                conv_context = await agent.get_conversation_history(conversation_id)
                
                # Generate response
                response = await _generate_chat_response(
                    agent, conversation_id, user_message, conv_context
                )
                
                # Send response
                await websocket.send_text(json.dumps({
                    "type": "response",
                    "conversation_id": conversation_id,
                    "response": response,
                    "timestamp": datetime.now().isoformat(),
                    "system_status": await agent.get_system_status()
                }))
            else:
                await websocket.send_text(json.dumps({
                    "type": "error",
                    "message": "System at capacity - please try again later",
                    "timestamp": datetime.now().isoformat()
                }))
                
    except WebSocketDisconnect:
        logger.info(f"WebSocket disconnected for conversation {conversation_id}")
    except Exception as e:
        logger.error(f"WebSocket error: {e}")
        await websocket.send_text(json.dumps({
            "type": "error",
            "message": str(e),
            "timestamp": datetime.now().isoformat()
        }))

@app.get("/health")
async def health_check():
    """Health check endpoint"""
    try:
        agent = await get_tla_agent()
        health = agent.is_healthy()
        status = await agent.get_system_status()
        
        return {
            "healthy": health,
            "tla_verified": True,
            "central_brain_state": status["central_brain_state"],
            "active_conversations": status["active_conversations"],
            "system_load": {
                "conversations": status["resource_usage"]["conversations"],
                "agents": status["resource_usage"]["agents"],
                "requests": status["resource_usage"]["requests"],
                "responses": status["resource_usage"]["responses"]
            },
            "timestamp": datetime.now().isoformat()
        }
    except Exception as e:
        logger.error(f"Health check error: {e}")
        return {
            "healthy": False,
            "error": str(e),
            "timestamp": datetime.now().isoformat()
        }

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
