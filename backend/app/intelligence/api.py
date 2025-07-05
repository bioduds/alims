"""
Main Interface Agent Integration for ALIMS
Integrates the formal TLA+ based agent system with the existing ALIMS architecture.
"""

import asyncio
import logging
from typing import Dict, Any, Optional
from fastapi import APIRouter, HTTPException, BackgroundTasks
from pydantic import BaseModel

from .main_interface_agent import MainInterfaceAgent, SystemConfiguration

# Configure logging
logger = logging.getLogger(__name__)

# Global agent system instance
agent_system: Optional[MainInterfaceAgent] = None

# Request/Response models
class ConversationRequest(BaseModel):
    context: Optional[Dict[str, Any]] = None
    required_capability: Optional[str] = "sample_analysis"

class QueryRequest(BaseModel):
    conversation_id: str
    predicate: str
    args: list[str]

class ConversationResponse(BaseModel):
    conversation_id: str
    status: str
    message: str

class QueryResponse(BaseModel):
    query_id: str
    status: str
    results: Optional[list] = None

class SystemStatusResponse(BaseModel):
    status: Dict[str, Any]
    message: str

# FastAPI router
router = APIRouter(prefix="/intelligence", tags=["intelligence"])


async def initialize_agent_system():
    """Initialize the Main Interface Agent System"""
    global agent_system
    
    if agent_system is None:
        logger.info("Initializing Main Interface Agent System...")
        config = SystemConfiguration()
        agent_system = MainInterfaceAgent(config)
        
        # Initialize the system
        success = await agent_system.initialize_system()
        if not success:
            raise RuntimeError("Failed to initialize Main Interface Agent System")
        
        logger.info("Main Interface Agent System initialized successfully")
    
    return agent_system


@router.on_event("startup")
async def startup_event():
    """Initialize agent system on startup"""
    await initialize_agent_system()


@router.post("/conversations", response_model=ConversationResponse)
async def start_conversation(request: ConversationRequest):
    """
    Start a new conversation with the Main Interface Agent
    
    Based on TLA+ specification:
    - Creates new conversation record
    - Assigns suitable agent based on capability
    - Returns conversation ID for further interactions
    """
    try:
        system = await initialize_agent_system()
        
        # Start conversation
        conversation_id = await system.start_conversation(request.context)
        
        # Assign agent based on required capability
        assigned = await system.assign_agent_to_conversation(
            conversation_id, 
            request.required_capability
        )
        
        if not assigned:
            raise HTTPException(
                status_code=503, 
                detail=f"No available agent with capability: {request.required_capability}"
            )
        
        return ConversationResponse(
            conversation_id=conversation_id,
            status="active",
            message=f"Conversation started with {request.required_capability} agent"
        )
    
    except Exception as e:
        logger.error(f"Failed to start conversation: {e}")
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/conversations/{conversation_id}/queries", response_model=QueryResponse)
async def start_query(conversation_id: str, request: QueryRequest):
    """
    Start a Prolog-style logical reasoning query
    
    Based on TLA+ specification:
    - Creates query record
    - Processes inference using knowledge base
    - Returns results or failure information
    """
    try:
        system = await initialize_agent_system()
        
        # Start Prolog query
        query_id = await system.start_prolog_query(
            conversation_id,
            request.predicate,
            request.args
        )
        
        # Process the inference
        success = await system.process_inference(query_id)
        
        # Get query results
        query = system.active_queries.get(query_id)
        if not query:
            raise HTTPException(status_code=404, detail="Query not found")
        
        return QueryResponse(
            query_id=query_id,
            status=query.state.value,
            results=query.result if success else None
        )
    
    except Exception as e:
        logger.error(f"Failed to process query: {e}")
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/conversations/{conversation_id}/complete")
async def complete_conversation(conversation_id: str):
    """
    Complete inference processing and clean up resources
    
    Based on TLA+ specification:
    - Completes all pending queries
    - Garbage collects query resources
    - Returns conversation to active state
    """
    try:
        system = await initialize_agent_system()
        
        success = await system.complete_inference(conversation_id)
        
        if not success:
            raise HTTPException(
                status_code=400, 
                detail="Cannot complete conversation - pending queries exist"
            )
        
        # Release agent
        conversation = system.conversations.get(conversation_id)
        if conversation and conversation.assigned_agent:
            system.dispatcher.release_agent(conversation.assigned_agent)
        
        return {"status": "completed", "message": "Conversation completed successfully"}
    
    except Exception as e:
        logger.error(f"Failed to complete conversation: {e}")
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/status", response_model=SystemStatusResponse)
async def get_system_status():
    """
    Get comprehensive system status and metrics
    
    Returns:
    - Central brain state
    - Active conversations and queries
    - Agent availability
    - System metrics
    - Knowledge base status
    """
    try:
        system = await initialize_agent_system()
        
        status = system.get_system_status()
        
        return SystemStatusResponse(
            status=status,
            message="System status retrieved successfully"
        )
    
    except Exception as e:
        logger.error(f"Failed to get system status: {e}")
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/conversations/{conversation_id}")
async def get_conversation_status(conversation_id: str):
    """Get detailed conversation status"""
    try:
        system = await initialize_agent_system()
        
        conversation = system.conversations.get(conversation_id)
        if not conversation:
            raise HTTPException(status_code=404, detail="Conversation not found")
        
        # Get associated queries
        queries = [
            {
                "id": q.id,
                "predicate": q.predicate,
                "args": q.args,
                "state": q.state.value,
                "result": q.result
            }
            for q in system.active_queries.values()
            if q.conversation_id == conversation_id
        ]
        
        return {
            "conversation_id": conversation.id,
            "state": conversation.state.value,
            "assigned_agent": conversation.assigned_agent,
            "start_time": conversation.start_time,
            "timeout_deadline": conversation.timeout_deadline,
            "retry_count": conversation.retry_count,
            "context": conversation.context,
            "queries": queries
        }
    
    except Exception as e:
        logger.error(f"Failed to get conversation status: {e}")
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/knowledge-base")
async def get_knowledge_base():
    """Get current knowledge base contents"""
    try:
        system = await initialize_agent_system()
        
        knowledge_entries = []
        for entry in system.prolog_engine.knowledge_base.values():
            knowledge_entries.append({
                "id": entry.id,
                "type": entry.type,
                "predicate": entry.predicate,
                "args": entry.args,
                "body": entry.body
            })
        
        return {
            "knowledge_base": knowledge_entries,
            "size": len(knowledge_entries),
            "max_size": system.config.MAX_KNOWLEDGE_BASE_SIZE
        }
    
    except Exception as e:
        logger.error(f"Failed to get knowledge base: {e}")
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/agents")
async def get_agents_status():
    """Get all agents status"""
    try:
        system = await initialize_agent_system()
        
        agents = []
        for agent in system.dispatcher.agents.values():
            agents.append({
                "id": agent.id,
                "state": agent.state.value,
                "capabilities": list(agent.capabilities),
                "current_conversation": agent.current_conversation,
                "load_factor": agent.load_factor,
                "error_count": agent.error_count
            })
        
        return {
            "agents": agents,
            "total_agents": len(agents),
            "idle_agents": len([a for a in agents if a["state"] == "IDLE"]),
            "busy_agents": len([a for a in agents if a["state"] == "BUSY"])
        }
    
    except Exception as e:
        logger.error(f"Failed to get agents status: {e}")
        raise HTTPException(status_code=500, detail=str(e))


# Background task for monitoring timeouts
async def monitor_timeouts():
    """Background task to monitor and handle query timeouts"""
    while True:
        try:
            if agent_system:
                # Check for timed out queries
                current_queries = list(agent_system.active_queries.keys())
                for query_id in current_queries:
                    await agent_system.timeout_query(query_id)
            
            await asyncio.sleep(1)  # Check every second
            
        except Exception as e:
            logger.error(f"Timeout monitoring error: {e}")
            await asyncio.sleep(5)  # Wait longer on error


# Add background task startup
@router.on_event("startup")
async def start_background_tasks():
    """Start background monitoring tasks"""
    asyncio.create_task(monitor_timeouts())


# Integration with existing ALIMS chat interface
@router.post("/chat")
async def intelligent_chat(message: str, conversation_id: Optional[str] = None):
    """
    Intelligent chat interface that uses the Main Interface Agent
    for logical reasoning and decision making
    """
    try:
        system = await initialize_agent_system()
        
        # Start new conversation if none provided
        if not conversation_id:
            conversation_id = await system.start_conversation({
                "user_message": message,
                "chat_type": "intelligent"
            })
            
            # Assign logical reasoning agent
            await system.assign_agent_to_conversation(conversation_id, "logical_reasoning")
        
        # Analyze message for logical queries
        response = await _process_intelligent_message(system, conversation_id, message)
        
        return {
            "conversation_id": conversation_id,
            "response": response,
            "reasoning_used": True
        }
    
    except Exception as e:
        logger.error(f"Intelligent chat error: {e}")
        raise HTTPException(status_code=500, detail=str(e))


async def _process_intelligent_message(system: MainInterfaceAgent, 
                                     conversation_id: str, 
                                     message: str) -> str:
    """Process message using intelligent reasoning"""
    
    # Simple intent detection for demonstration
    if "analyze" in message.lower() and "sample" in message.lower():
        # Query for suitable agent
        query_id = await system.start_prolog_query(
            conversation_id,
            "suitable_agent",
            ["?Agent", "sample_analysis_task"]
        )
        
        success = await system.process_inference(query_id)
        
        if success:
            query = system.active_queries.get(query_id)
            if query and query.result:
                return f"I'll help you with sample analysis. Based on logical reasoning, I've identified the suitable agent for this task. The system found {len(query.result)} matching capabilities."
            else:
                return "I can help with sample analysis, but I need to check available resources."
        else:
            return "I understand you need sample analysis. Let me check our available capabilities."
    
    elif "workflow" in message.lower():
        return "I can help with workflow management. Let me connect you with our workflow control capabilities."
    
    else:
        return "I'm analyzing your request using logical reasoning. How can I assist you with laboratory operations?"


# Make the router available for import
__all__ = ["router", "initialize_agent_system"]
