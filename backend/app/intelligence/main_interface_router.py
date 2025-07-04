"""
FastAPI Router for Main Interface Agent

Provides REST API endpoints for the Tauri frontend to interact
with the Main Interface Agent.
"""

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel
from typing import Dict, List, Optional
import logging

from main_interface_service import (
    get_lims_interface_service,
    start_lims_conversation,
    send_lims_message,
    get_lims_conversation_messages,
    get_lims_system_status
)

logger = logging.getLogger(__name__)

router = APIRouter(prefix="/api/v1/interface", tags=["Main Interface"])

# Request/Response Models
class ConversationStartRequest(BaseModel):
    user_id: Optional[str] = None
    context: Optional[Dict] = None

class ConversationStartResponse(BaseModel):
    success: bool
    conversation_id: Optional[str] = None
    error: Optional[str] = None

class MessageSendRequest(BaseModel):
    conversation_id: str
    message: str
    message_type: str = "SAMPLE_INQUIRY"
    priority: str = "MEDIUM"

class MessageSendResponse(BaseModel):
    success: bool
    messages: Optional[List[Dict]] = None
    error: Optional[str] = None

class ConversationMessagesResponse(BaseModel):
    success: bool
    messages: Optional[List[Dict]] = None
    error: Optional[str] = None

class SystemStatusResponse(BaseModel):
    success: bool
    status: Optional[Dict] = None
    error: Optional[str] = None

# API Endpoints

@router.post("/conversations/start", response_model=ConversationStartResponse)
async def start_conversation(request: ConversationStartRequest):
    """Start a new conversation with the Main Interface Agent."""
    try:
        result = await start_lims_conversation()
        return ConversationStartResponse(**result)
    except Exception as e:
        logger.error(f"Error starting conversation: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.post("/conversations/message", response_model=MessageSendResponse)
async def send_message(request: MessageSendRequest):
    """Send a message to a conversation."""
    try:
        result = await send_lims_message(
            request.conversation_id,
            request.message,
            request.message_type
        )
        return MessageSendResponse(**result)
    except Exception as e:
        logger.error(f"Error sending message: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/conversations/{conversation_id}/messages", response_model=ConversationMessagesResponse)
async def get_conversation_messages(conversation_id: str):
    """Get all messages for a conversation."""
    try:
        result = await get_lims_conversation_messages(conversation_id)
        return ConversationMessagesResponse(**result)
    except Exception as e:
        logger.error(f"Error getting conversation messages: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/status", response_model=SystemStatusResponse)
async def get_system_status():
    """Get the current system status."""
    try:
        result = await get_lims_system_status()
        return SystemStatusResponse(**result)
    except Exception as e:
        logger.error(f"Error getting system status: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/conversations/active")
async def get_active_conversations():
    """Get all active conversations."""
    try:
        service = await get_lims_interface_service()
        conversations = await service.get_active_conversations()
        return {
            "success": True,
            "conversations": conversations
        }
    except Exception as e:
        logger.error(f"Error getting active conversations: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.post("/conversations/{conversation_id}/complete")
async def complete_conversation(conversation_id: str):
    """Mark a conversation as complete."""
    try:
        service = await get_lims_interface_service()
        success = await service.complete_conversation(conversation_id)
        return {
            "success": success,
            "message": "Conversation completed" if success else "Failed to complete conversation"
        }
    except Exception as e:
        logger.error(f"Error completing conversation: {e}")
        raise HTTPException(status_code=500, detail=str(e))

# Health check endpoint
@router.get("/health")
async def health_check():
    """Health check for the Main Interface Agent."""
    try:
        service = await get_lims_interface_service()
        status = await service.get_system_status()
        return {
            "status": "healthy",
            "agent_status": status.get("service_status", "unknown"),
            "initialized": status.get("initialized", False)
        }
    except Exception as e:
        logger.error(f"Health check failed: {e}")
        return {
            "status": "unhealthy",
            "error": str(e)
        }
