"""
Standalone Main Interface Agent Server

A standalone FastAPI server that runs the Main Interface Agent
independently from the main ALIMS application.
"""

import asyncio
import logging
import sys
import os
from typing import Dict, List, Optional
from datetime import datetime

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
import uvicorn

# Add the main interface agent to the path
agent_path = os.path.join(os.path.dirname(__file__), '..', 'plans', 
                          'feature-2025010301-main-interface-agent', 'implementation')
sys.path.insert(0, agent_path)

from main_interface_agent import (
    MainInterfaceAgent,
    RequestType,
    Priority,
    ConversationState,
    AgentState,
    create_main_interface_agent
)

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)

logger = logging.getLogger(__name__)

# Create FastAPI app
app = FastAPI(
    title="ALIMS Main Interface Agent API",
    description="Central orchestration API for LIMS conversations and agent management",
    version="1.0.0"
)

# Configure CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # Allow all origins for development
    allow_credentials=True,
    allow_methods=["*"],  # Allow all methods
    allow_headers=["*"],  # Allow all headers
)

# Global service instance
_main_interface_agent: Optional[MainInterfaceAgent] = None

async def get_agent() -> MainInterfaceAgent:
    """Get or create the global Main Interface Agent."""
    global _main_interface_agent
    
    if _main_interface_agent is None:
        _main_interface_agent = await create_main_interface_agent()
        
        # Register core LIMS agents
        core_agents = [
            ("sample_tracker_001", "sample_tracker"),
            ("workflow_manager_001", "workflow_manager"),
            ("lims_coordinator_001", "lims_coordinator"),
            ("system_monitor_001", "system_monitor"),
            ("qc_manager_001", "qc_manager"),
            ("report_generator_001", "report_generator")
        ]
        
        for agent_id, capabilities in core_agents:
            await _main_interface_agent.register_agent(agent_id, capabilities)
            logger.info(f"Registered agent {agent_id} with capabilities {capabilities}")
    
    return _main_interface_agent

# Request/Response Models
class ConversationStartRequest(BaseModel):
    user_id: Optional[str] = None
    context: Optional[Dict] = None

class MessageSendRequest(BaseModel):
    conversation_id: str
    message: str
    message_type: str = "SAMPLE_INQUIRY"
    priority: str = "MEDIUM"

# API Endpoints

@app.get("/")
async def root():
    """Root endpoint with API information."""
    return {
        "name": "ALIMS Main Interface Agent API",
        "version": "1.0.0",
        "status": "running",
        "docs_url": "/docs"
    }

@app.get("/health")
async def health():
    """Health check endpoint."""
    try:
        agent = await get_agent()
        status = agent.get_system_status()
        return {
            "status": "healthy",
            "agent_status": status.get("central_brain_state", "unknown"),
            "initialized": True
        }
    except Exception as e:
        logger.error(f"Health check failed: {e}")
        return {
            "status": "unhealthy",
            "error": str(e)
        }

@app.post("/api/v1/interface/conversations/start")
async def start_conversation(request: ConversationStartRequest):
    """Start a new conversation with the Main Interface Agent."""
    try:
        agent = await get_agent()
        conv_id = await agent.start_conversation()
        
        if conv_id:
            logger.info(f"Started new conversation: {conv_id}")
            return {
                "success": True,
                "conversation_id": conv_id,
                "message": "Conversation started successfully"
            }
        else:
            return {
                "success": False,
                "error": "Failed to start conversation"
            }
    except Exception as e:
        logger.error(f"Error starting conversation: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/api/v1/interface/conversations/message")
async def send_message(request: MessageSendRequest):
    """Send a message to a conversation."""
    try:
        agent = await get_agent()
        
        # Map string types to enums
        request_type = RequestType(request.message_type)
        priority_enum = Priority(request.priority)
        
        # Send the message
        success = await agent.receive_user_request(
            request.conversation_id, request.message, request_type, priority_enum
        )
        
        if success:
            # Process the request
            await agent.process_next_request()
            
            # Auto-complete agent work with intelligent responses
            if request.conversation_id in agent.conversation_contexts:
                context = agent.conversation_contexts[request.conversation_id]
                logger.info(
                    f"Processing intelligent response for message: {request.message}")

                # Generate intelligent response based on the user's message
                response_content = generate_intelligent_response(
                    request.message)
                logger.info(f"Generated response: {response_content[:100]}...")

                # Create and add the agent response directly to the conversation history
                from datetime import datetime
                agent_msg = type('Message', (), {
                    'role': 'assistant',
                    'content': response_content,
                    'timestamp': datetime.now(),
                    'agent_source': 'main_interface_agent'
                })()
                context.messages.append(agent_msg)
                logger.info("Agent response added to conversation history")

            # Get updated messages
            history = agent.get_conversation_history(request.conversation_id)
            messages = []
            for msg in history:
                messages.append({
                    'role': msg.role,
                    'content': msg.content,
                    'timestamp': msg.timestamp.isoformat(),
                    'agent_source': getattr(msg, 'agent_source', None)
                })
            
            return {
                "success": True,
                "messages": messages
            }
        else:
            return {
                "success": False,
                "error": "Failed to send message"
            }
    except Exception as e:
        logger.error(f"Error sending message: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/api/v1/interface/conversations/{conversation_id}/messages")
async def get_conversation_messages(conversation_id: str):
    """Get all messages for a conversation."""
    try:
        agent = await get_agent()
        history = agent.get_conversation_history(conversation_id)
        
        messages = []
        for msg in history:
            messages.append({
                'role': msg.role,
                'content': msg.content,
                'timestamp': msg.timestamp.isoformat(),
                'agent_source': getattr(msg, 'agent_source', None)
            })
        
        return {
            "success": True,
            "messages": messages
        }
    except Exception as e:
        logger.error(f"Error getting conversation messages: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/api/v1/interface/conversations/active")
async def get_active_conversations():
    """Get all active conversations."""
    try:
        agent = await get_agent()
        active_conv_ids = agent.get_active_conversations()
        
        conversations = []
        for conv_id in active_conv_ids:
            state = agent.conversations.get(conv_id, ConversationState.ACTIVE)
            
            # Safely get message count
            if conv_id in agent.conversation_contexts:
                message_count = len(agent.conversation_contexts[conv_id].messages)
            else:
                message_count = 0
                
            conversations.append({
                'conversation_id': conv_id,
                'state': state.value,
                'message_count': message_count
            })
        
        return {
            "success": True,
            "conversations": conversations
        }
    except Exception as e:
        logger.error(f"Error getting active conversations: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/api/v1/interface/status")
async def get_system_status():
    """Get the current system status."""
    try:
        agent = await get_agent()
        status = agent.get_system_status()
        status['initialized'] = True
        status['service_status'] = 'ready'
        
        return {
            "success": True,
            "status": status
        }
    except Exception as e:
        logger.error(f"Error getting system status: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/api/v1/interface/conversations/{conversation_id}/complete")
async def complete_conversation(conversation_id: str):
    """Mark a conversation as complete."""
    try:
        agent = await get_agent()
        success = await agent.complete_conversation(conversation_id)
        
        return {
            "success": success,
            "message": "Conversation completed" if success else "Failed to complete conversation"
        }
    except Exception as e:
        logger.error(f"Error completing conversation: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/api/v1/interface/conversations/{conversation_id}/simulate-agent-work")
async def simulate_agent_work(conversation_id: str):
    """Debug endpoint to simulate agent work completion for testing."""
    try:
        agent = await get_agent()
        
        # Check if conversation exists
        if conversation_id not in agent.conversations:
            return {"success": False, "error": "Conversation not found"}
        
        # Get conversation context
        if conversation_id not in agent.conversation_contexts:
            return {"success": False, "error": "Conversation context not found"}
        
        context = agent.conversation_contexts[conversation_id]
        active_agents = list(context.active_agents)
        
        if not active_agents:
            return {"success": True, "message": "No active agents to simulate"}
        
        # First mark agents as busy (this should happen in orchestration but isn't)
        for agent_id in active_agents:
            if agent_id in agent.available_agents:
                agent.available_agents[agent_id].state = AgentState.BUSY
        
        # Simulate each active agent completing their work
        responses_sent = 0
        for agent_id in active_agents:
            # Simulate agent response
            success = await agent.receive_agent_response(
                agent_id=agent_id,
                response_content=f"Simulated response from agent {agent_id} for {context.user_intent}",
                success=True
            )
            if success:
                responses_sent += 1
        
        # Process the responses
        await agent.synthesize_and_respond()
        
        # Clear active agents from conversation context
        context.active_agents.clear()
        
        return {
            "success": True,
            "message": f"Simulated {responses_sent} agent responses",
            "active_agents_processed": len(active_agents)
        }
        
    except Exception as e:
        logger.error(f"Error simulating agent work: {e}")
        raise HTTPException(status_code=500, detail=str(e))


def generate_intelligent_response(user_message: str) -> str:
    """Generate an intelligent response based on the user's message content."""
    user_msg_lower = user_message.lower()

    # Sample tracking related responses
    if any(keyword in user_msg_lower for keyword in ['sample', 'samples', 'register', 'track', 'tracking']):
        if 'register' in user_msg_lower:
            return """I can help you register new samples in the ALIMS system. To register samples, I'll need:

• Sample ID or batch number
• Sample type (blood, tissue, chemical, etc.)
• Collection date and time
• Storage requirements
• Any special handling instructions

Would you like to start the sample registration process? Please provide the sample details or let me know if you'd like me to guide you through the registration workflow."""

        elif 'track' in user_msg_lower:
            return """I can help you track samples throughout their lifecycle in the laboratory. The ALIMS system provides:

• Real-time sample location tracking
• Chain of custody documentation
• Processing status updates
• Quality control checkpoints
• Storage condition monitoring

Please provide a sample ID or batch number to track, or let me know what specific tracking information you need."""

    # Analysis related responses
    elif any(keyword in user_msg_lower for keyword in ['analysis', 'analyze', 'test', 'results']):
        return """I can assist with laboratory analysis workflows including:

• Scheduling analytical tests
• Managing test protocols
• Monitoring analysis progress
• Reviewing and approving results
• Generating analytical reports

What type of analysis are you looking to perform? Please specify the sample type and analysis requirements."""

    # Quality control responses
    elif any(keyword in user_msg_lower for keyword in ['qc', 'quality', 'control', 'validation']):
        return """I can help with quality control processes:

• QC sample preparation and testing
• Method validation procedures
• Control chart monitoring
• Out-of-specification investigations
• Compliance documentation

What QC activities do you need assistance with?"""

    # Data and reporting
    elif any(keyword in user_msg_lower for keyword in ['data', 'report', 'export', 'chart', 'graph']):
        return """I can help with data management and reporting:

• Generate analytical reports
• Export data in various formats
• Create visualizations and charts
• Trend analysis
• Compliance reporting

What type of data or report do you need? I can create visualizations on the analysis stage."""

    # Equipment and instruments
    elif any(keyword in user_msg_lower for keyword in ['instrument', 'equipment', 'calibration', 'maintenance']):
        return """I can assist with instrument management:

• Equipment calibration scheduling
• Maintenance tracking
• Performance monitoring
• Qualification protocols
• Usage logs

Which instruments do you need help with?"""

    # General greeting or help
    elif any(keyword in user_msg_lower for keyword in ['hello', 'hi', 'help', 'assist']):
        return """Hello! I'm the ALIMS Main Interface Agent. I can help you with:

🔬 **Sample Management**: Register, track, and manage laboratory samples
📊 **Analysis Workflows**: Schedule tests, monitor progress, review results  
📈 **Data & Reports**: Generate reports, create visualizations, export data
🛠️ **Quality Control**: QC testing, validation, compliance monitoring
⚙️ **Instrument Management**: Calibration, maintenance, performance tracking

What would you like to work on today?"""

    # Default response
    else:
        return f"""I understand you mentioned: "{user_message}"

As the ALIMS Main Interface Agent, I can help with laboratory information management including sample tracking, analysis workflows, quality control, data management, and reporting.

Could you please clarify what specific LIMS task you'd like assistance with? I'm here to help streamline your laboratory operations."""

if __name__ == "__main__":
    uvicorn.run(
        app,
        host="0.0.0.0",  # Bind to all interfaces
        port=8001,
        log_level="info"
    )
