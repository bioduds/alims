"""
Enhanced Main Interface Agent API Router
Provides comprehensive REST API endpoints for the TLA+ validated agent system.
"""

import asyncio
import logging
from typing import Dict, List, Optional, Any
from datetime import datetime
from fastapi import APIRouter, HTTPException, BackgroundTasks, Depends
from pydantic import BaseModel, Field

from enhanced_main_interface_service import EnhancedLIMSMainInterfaceService

logger = logging.getLogger(__name__)

# Global service instance
enhanced_service: Optional[EnhancedLIMSMainInterfaceService] = None

# Request/Response models
class ConversationStartRequest(BaseModel):
    context: Optional[Dict[str, Any]] = None
    required_capability: str = Field(default="sample_analysis", description="Required agent capability")
    user_id: Optional[str] = None

class MessageRequest(BaseModel):
    conversation_id: str
    message: str
    user_id: Optional[str] = None

class KnowledgeQueryRequest(BaseModel):
    predicate: str
    args: List[str]
    conversation_id: Optional[str] = None

class ConversationResponse(BaseModel):
    conversation_id: str
    status: str
    message: str
    agent_id: Optional[str] = None

class MessageResponse(BaseModel):
    response: str
    status: str
    conversation_id: str
    processing_time: float
    agent_responses: List[Dict[str, Any]] = []

class KnowledgeQueryResponse(BaseModel):
    results: List[Dict[str, Any]]
    query_time: float
    total_results: int

class SystemStatusResponse(BaseModel):
    status: str
    central_brain_state: str
    dispatcher_state: str
    active_conversations: int
    active_queries: int
    registered_agents: int
    system_metrics: Dict[str, Any]
    lims_agents: Dict[str, Any]
    uptime: float

class AgentStatusResponse(BaseModel):
    agent_id: str
    state: str
    capabilities: List[str]
    current_conversation: Optional[str]
    load_factor: int
    error_count: int

# FastAPI router
router = APIRouter(prefix="/enhanced-intelligence", tags=["enhanced-intelligence"])

async def get_service() -> EnhancedLIMSMainInterfaceService:
    """Dependency to get the enhanced service instance."""
    global enhanced_service
    if not enhanced_service or not enhanced_service.is_initialized():
        raise HTTPException(status_code=503, detail="Enhanced Main Interface Service not initialized")
    return enhanced_service

async def initialize_enhanced_service(config: Optional[Dict[str, Any]] = None):
    """Initialize the enhanced main interface service."""
    global enhanced_service
    try:
        if enhanced_service and enhanced_service.is_initialized():
            logger.info("Enhanced service already initialized")
            return
        
        enhanced_service = EnhancedLIMSMainInterfaceService(config)
        success = await enhanced_service.initialize()
        
        if not success:
            raise RuntimeError("Failed to initialize enhanced service")
        
        logger.info("Enhanced Main Interface Service initialized successfully")
        
    except Exception as e:
        logger.error(f"Failed to initialize enhanced service: {e}")
        raise

@router.post("/initialize", response_model=Dict[str, str])
async def initialize_system(
    config: Optional[Dict[str, Any]] = None,
    background_tasks: BackgroundTasks = BackgroundTasks()
):
    """Initialize the enhanced main interface agent system."""
    try:
        background_tasks.add_task(initialize_enhanced_service, config)
        return {"status": "initializing", "message": "Enhanced system initialization started"}
    except Exception as e:
        logger.error(f"Error starting initialization: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.post("/conversations/start", response_model=ConversationResponse)
async def start_conversation(
    request: ConversationStartRequest,
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Start a new conversation with the enhanced agent system."""
    try:
        conversation_id = await service.start_conversation(
            context=request.context,
            required_capability=request.required_capability
        )
        
        return ConversationResponse(
            conversation_id=conversation_id,
            status="started",
            message=f"Conversation started with capability: {request.required_capability}",
            agent_id=None  # Will be assigned by dispatcher
        )
        
    except Exception as e:
        logger.error(f"Error starting conversation: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.post("/conversations/message", response_model=MessageResponse)
async def send_message(
    request: MessageRequest,
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Send a message to an existing conversation."""
    try:
        start_time = asyncio.get_event_loop().time()
        
        response = await service.send_message(
            conversation_id=request.conversation_id,
            message=request.message,
            user_id=request.user_id
        )
        
        processing_time = asyncio.get_event_loop().time() - start_time
        
        return MessageResponse(
            response=response.get("response", ""),
            status=response.get("status", "processed"),
            conversation_id=request.conversation_id,
            processing_time=processing_time,
            agent_responses=response.get("agent_responses", [])
        )
        
    except Exception as e:
        logger.error(f"Error processing message: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/conversations/{conversation_id}/status")
async def get_conversation_status(
    conversation_id: str,
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Get the status of a specific conversation."""
    try:
        if not service.agent_system:
            raise HTTPException(status_code=503, detail="Agent system not available")
        
        conversation = service.agent_system.conversations.get(conversation_id)
        if not conversation:
            raise HTTPException(status_code=404, detail="Conversation not found")
        
        return {
            "conversation_id": conversation_id,
            "state": conversation.state.value,
            "agent_id": conversation.agent_id,
            "start_time": conversation.start_time,
            "user_count": len(conversation.users),
            "message_count": len(conversation.messages)
        }
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error getting conversation status: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.post("/knowledge/query", response_model=KnowledgeQueryResponse)
async def query_knowledge_base(
    request: KnowledgeQueryRequest,
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Query the LIMS knowledge base using Prolog reasoning."""
    try:
        start_time = asyncio.get_event_loop().time()
        
        results = await service.query_knowledge_base(
            predicate=request.predicate,
            args=request.args,
            conversation_id=request.conversation_id
        )
        
        query_time = asyncio.get_event_loop().time() - start_time
        
        return KnowledgeQueryResponse(
            results=results,
            query_time=query_time,
            total_results=len(results)
        )
        
    except Exception as e:
        logger.error(f"Error querying knowledge base: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/system/status", response_model=SystemStatusResponse)
async def get_system_status(
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Get comprehensive system status."""
    try:
        status = await service.get_system_status()
        
        return SystemStatusResponse(
            status=status.get("status", "unknown"),
            central_brain_state=status.get("central_brain_state", "unknown"),
            dispatcher_state=status.get("dispatcher_state", "unknown"),
            active_conversations=status.get("active_conversations", 0),
            active_queries=status.get("active_queries", 0),
            registered_agents=status.get("registered_agents", 0),
            system_metrics=status.get("system_metrics", {}),
            lims_agents=status.get("lims_agents", {}),
            uptime=status.get("uptime", 0.0)
        )
        
    except Exception as e:
        logger.error(f"Error getting system status: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/agents", response_model=List[AgentStatusResponse])
async def get_agents_status(
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Get status of all registered agents."""
    try:
        if not service.agent_system:
            raise HTTPException(status_code=503, detail="Agent system not available")
        
        agents_status = []
        for agent_id, agent in service.agent_system.dispatcher.agents.items():
            agents_status.append(AgentStatusResponse(
                agent_id=agent_id,
                state=agent.state.value,
                capabilities=list(agent.capabilities),
                current_conversation=agent.current_conversation,
                load_factor=agent.load_factor,
                error_count=agent.error_count
            ))
        
        return agents_status
        
    except Exception as e:
        logger.error(f"Error getting agents status: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/agents/{agent_id}/status", response_model=AgentStatusResponse)
async def get_agent_status(
    agent_id: str,
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Get status of a specific agent."""
    try:
        if not service.agent_system:
            raise HTTPException(status_code=503, detail="Agent system not available")
        
        agent = service.agent_system.dispatcher.agents.get(agent_id)
        if not agent:
            raise HTTPException(status_code=404, detail="Agent not found")
        
        return AgentStatusResponse(
            agent_id=agent_id,
            state=agent.state.value,
            capabilities=list(agent.capabilities),
            current_conversation=agent.current_conversation,
            load_factor=agent.load_factor,
            error_count=agent.error_count
        )
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error getting agent status: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.post("/agents/{agent_id}/reset")
async def reset_agent(
    agent_id: str,
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Reset an agent's state and error count."""
    try:
        if not service.agent_system:
            raise HTTPException(status_code=503, detail="Agent system not available")
        
        agent = service.agent_system.dispatcher.agents.get(agent_id)
        if not agent:
            raise HTTPException(status_code=404, detail="Agent not found")
        
        # Reset agent state
        await service.agent_system.dispatcher._handle_agent_error(agent_id, "Manual reset")
        
        return {"status": "success", "message": f"Agent {agent_id} reset successfully"}
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error resetting agent: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/knowledge/facts")
async def get_knowledge_facts(
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Get all facts in the knowledge base."""
    try:
        if not service.agent_system:
            raise HTTPException(status_code=503, detail="Agent system not available")
        
        facts = []
        for entry in service.agent_system.prolog_engine.knowledge_base.values():
            if entry.type == "FACT":
                facts.append({
                    "id": entry.id,
                    "predicate": entry.predicate,
                    "args": entry.args
                })
        
        return {"facts": facts, "total": len(facts)}
        
    except Exception as e:
        logger.error(f"Error getting knowledge facts: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/knowledge/rules")
async def get_knowledge_rules(
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Get all rules in the knowledge base."""
    try:
        if not service.agent_system:
            raise HTTPException(status_code=503, detail="Agent system not available")
        
        rules = []
        for entry in service.agent_system.prolog_engine.knowledge_base.values():
            if entry.type == "RULE":
                rules.append({
                    "id": entry.id,
                    "predicate": entry.predicate,
                    "args": entry.args,
                    "body": entry.body
                })
        
        return {"rules": rules, "total": len(rules)}
        
    except Exception as e:
        logger.error(f"Error getting knowledge rules: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.get("/audit/events")
async def get_audit_events(
    limit: int = 100,
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Get recent audit events."""
    try:
        if not service.agent_system:
            raise HTTPException(status_code=503, detail="Agent system not available")
        
        # Get recent audit events
        recent_events = sorted(
            service.agent_system.audit_log,
            key=lambda e: e.timestamp,
            reverse=True
        )[:limit]
        
        events = []
        for event in recent_events:
            events.append({
                "action": event.action,
                "timestamp": event.timestamp,
                "conversation_id": event.conversation_id,
                "agent_id": event.agent_id,
                "query_id": event.query_id,
                "details": event.details
            })
        
        return {"events": events, "total": len(events)}
        
    except Exception as e:
        logger.error(f"Error getting audit events: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@router.post("/shutdown")
async def shutdown_system(
    service: EnhancedLIMSMainInterfaceService = Depends(get_service)
):
    """Shutdown the enhanced main interface system."""
    try:
        await service.shutdown()
        global enhanced_service
        enhanced_service = None
        
        return {"status": "success", "message": "Enhanced system shutdown completed"}
        
    except Exception as e:
        logger.error(f"Error during shutdown: {e}")
        raise HTTPException(status_code=500, detail=str(e))

# Legacy compatibility endpoints for existing frontend
legacy_router = APIRouter(prefix="/api/v1/interface", tags=["legacy-interface"])

@legacy_router.post("/conversations/start")
async def legacy_start_conversation():
    """Legacy endpoint for starting conversations - redirects to enhanced API."""
    service = await get_service()
    if not service:
        raise HTTPException(status_code=503, detail="Service not available")
    
    try:
        conversation_id = await service.start_conversation(
            context={"legacy_client": True},
            required_capability="sample_analysis"
        )
        return {
            "success": True,
            "conversation_id": conversation_id,
            "message": "Conversation started"
        }
    except Exception as e:
        logger.error(f"Error starting legacy conversation: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@legacy_router.post("/conversations/message")
async def legacy_send_message(request: dict):
    """Legacy endpoint for sending messages - redirects to enhanced API."""
    service = await get_service()
    if not service:
        raise HTTPException(status_code=503, detail="Service not available")
    
    try:
        response = await service.send_message(
            conversation_id=request.get("conversation_id"),
            message=request.get("message"),
            user_id=request.get("user_id", "legacy_user")
        )
        return {
            "success": True,
            "messages": [
                {
                    "role": "agent",
                    "content": response.get("response", ""),
                    "timestamp": datetime.now().isoformat(),
                    "agent_source": response.get("agent_id", "main_interface")
                }
            ]
        }
    except Exception as e:
        logger.error(f"Error sending legacy message: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@legacy_router.get("/conversations/{conversation_id}/status")
async def legacy_conversation_status(conversation_id: str):
    """Legacy endpoint for conversation status."""
    service = await get_service()
    if not service:
        raise HTTPException(status_code=503, detail="Service not available")
    
    try:
        # Get conversation info from the agent system
        conversation = service.agent_system.conversations.get(conversation_id)
        if not conversation:
            raise HTTPException(status_code=404, detail="Conversation not found")
        
        return {
            "success": True,
            "conversation_id": conversation_id,
            "state": conversation.state.value,
            "message_count": len(conversation.context.get("messages", []))
        }
    except Exception as e:
        logger.error(f"Error getting legacy conversation status: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@legacy_router.get("/status")
async def legacy_system_status():
    """Legacy endpoint for system status."""
    service = await get_service()
    if not service:
        return {
            "initialized": False,
            "service_status": "not_available"
        }
    
    try:
        status = await service.get_system_status()
        return {
            "initialized": True,
            "service_status": "running",
            "central_brain_state": status.get("status", "unknown"),
            "active_conversations": status.get("active_conversations", 0),
            "total_conversations": status.get("total_conversations", 0),
            "available_agents": status.get("available_agents", 0),
            "busy_agents": status.get("busy_agents", 0),
            "error_agents": status.get("error_agents", 0),
            "pending_requests": 0,
            "pending_responses": 0
        }
    except Exception as e:
        logger.error(f"Error getting legacy system status: {e}")
        return {
            "initialized": False,
            "service_status": "error",
            "error": str(e)
        }
router.include_router(legacy_router)
