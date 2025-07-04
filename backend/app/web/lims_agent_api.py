#!/usr/bin/env python3
"""
LIMS Agent API Server

FastAPI server that provides endpoints for the Tauri frontend
to interact with LIMS agents and the Agent Creator.
"""

import asyncio
import logging
import uuid
from datetime import datetime
from typing import Dict, List, Optional, Any
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

from backend.app.core.agent_creator import AgentCreator, AgentBlueprint
from backend.app.lims.agents.sample_reception import SampleReceptionAgent
from backend.app.lims.agents.sample_accessioning import SampleAccessioningAgent
from backend.app.lims.models import Sample, SampleState, Priority
from backend.app.lims.workflows.core_workflow import LIMSWorkflow

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("LIMSAgentAPI")

app = FastAPI(title="ALIMS Agent API", version="1.0.0")

# Enable CORS for Tauri frontend
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # In production, specify exact origins
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Global state
agent_creator = AgentCreator({"model_name": "llama3.2", "temperature": 0.7})
workflow = LIMSWorkflow()
active_conversations: Dict[str, Dict[str, Any]] = {}

# Pydantic models for API
class SampleData(BaseModel):
    sample_id: str
    patient_id: str
    sample_type: str
    tests_requested: List[str]
    priority: str = "ROUTINE"

class SampleModel(BaseModel):
    sample_id: str
    patient_id: str
    state: str
    barcode: Optional[str] = None
    accession_number: Optional[str] = None
    received_at: str
    sample_type: str
    tests_requested: List[str]
    priority: str
    location: Optional[str] = None

class LIMSAgentModel(BaseModel):
    agent_id: str
    name: str
    specialization: str
    state_handled: str
    personality_traits: Dict[str, float]
    status: str
    current_tasks: int

class NotificationModel(BaseModel):
    id: str
    notification_type: str
    message: str
    sample_id: Optional[str] = None
    timestamp: str
    priority: str
    requires_action: bool

class MessageRequest(BaseModel):
    conversation_id: str
    message: str
    agent_id: str
    sample_context: Optional[Dict[str, Any]] = None

class WorkflowContext(BaseModel):
    current_state: str
    next_states: List[str]
    required_actions: List[str]

class MessageResponse(BaseModel):
    content: str
    action_suggestions: List[str]
    workflow_context: WorkflowContext
    sample_update: Optional[SampleModel] = None

@app.get("/")
async def root():
    return {"message": "ALIMS Agent API Server", "version": "1.0.0"}

@app.get("/health")
async def health_check():
    return {
        "status": "healthy",
        "timestamp": datetime.now().isoformat(),
        "active_conversations": len(active_conversations),
        "agents_created": len(agent_creator.get_all_agents())
    }

@app.get("/lims/agents", response_model=List[LIMSAgentModel])
async def get_lims_agents():
    """Get available LIMS agents"""
    # For demo, return mock agents - in production this would come from agent registry
    agents = [
        LIMSAgentModel(
            agent_id="reception_001",
            name="Sam the Sample Reception Agent",
            specialization="sample_reception",
            state_handled="RECEIVED",
            personality_traits={"friendliness": 0.8, "precision": 0.9, "efficiency": 0.85},
            status="IDLE",
            current_tasks=0
        ),
        LIMSAgentModel(
            agent_id="accessioning_001", 
            name="Alex the Accessioning Agent",
            specialization="sample_accessioning",
            state_handled="ACCESSIONED",
            personality_traits={"thoroughness": 0.9, "patience": 0.7, "accuracy": 0.95},
            status="IDLE",
            current_tasks=0
        )
    ]
    
    # Add any dynamically created agents
    for agent_blueprint in agent_creator.get_all_agents():
        agents.append(LIMSAgentModel(
            agent_id=agent_blueprint.agent_id,
            name=agent_blueprint.name,
            specialization=agent_blueprint.specialization,
            state_handled=agent_blueprint.specialization.upper(),
            personality_traits=agent_blueprint.personality_traits,
            status="ACTIVE",
            current_tasks=1
        ))
    
    return agents

@app.get("/lims/samples/pending", response_model=List[SampleModel])
async def get_pending_samples():
    """Get pending samples"""
    # For demo, return empty list - in production this would query the database
    return []

@app.get("/lims/notifications", response_model=List[NotificationModel])
async def get_sample_notifications():
    """Get sample notifications"""
    # For demo, return mock notifications
    notifications = []
    
    # Add notifications based on active conversations
    for conv_id, conv_data in active_conversations.items():
        if "sample" in conv_data:
            sample = conv_data["sample"]
            priority = "CRITICAL" if sample.priority == Priority.STAT else "MEDIUM"
            notifications.append(NotificationModel(
                id=f"notif_{conv_id}",
                notification_type="SAMPLE_ACTIVE",
                message=f"Sample {sample.sample_id} is being processed",
                sample_id=sample.sample_id,
                timestamp=datetime.now().isoformat(),
                priority=priority,
                requires_action=False
            ))
    
    return notifications

@app.post("/lims/samples/register", response_model=SampleModel)
async def register_new_sample(sample_data: SampleData):
    """Register a new sample"""
    try:
        # Create sample
        sample = Sample(
            sample_id=sample_data.sample_id,
            patient_id=sample_data.patient_id,
            state=SampleState.RECEIVED,
            received_at=datetime.now(),
            sample_type=sample_data.sample_type,
            tests_requested=sample_data.tests_requested,
            priority=Priority[sample_data.priority]
        )
        
        logger.info(f"Registered new sample: {sample.sample_id}")
        
        return SampleModel(
            sample_id=sample.sample_id,
            patient_id=sample.patient_id,
            state=sample.state.value,
            barcode=sample.barcode,
            accession_number=sample.accession_number,
            received_at=sample.received_at.isoformat(),
            sample_type=sample.sample_type,
            tests_requested=sample.tests_requested,
            priority=sample.priority.value,
            location=sample.location
        )
        
    except Exception as e:
        logger.error(f"Failed to register sample: {e}")
        raise HTTPException(status_code=400, detail=str(e))

@app.post("/lims/messages/send", response_model=MessageResponse)
async def send_lims_message(request: MessageRequest):
    """Send a message to a LIMS agent"""
    try:
        conversation_id = request.conversation_id
        message = request.message
        agent_id = request.agent_id
        sample_context = request.sample_context
        
        # Get or create conversation
        if conversation_id not in active_conversations:
            active_conversations[conversation_id] = {
                "agent_id": agent_id,
                "messages": [],
                "created_at": datetime.now()
            }
        
        conversation = active_conversations[conversation_id]
        
        # Add human message to conversation
        conversation["messages"].append({
            "role": "user",
            "content": message,
            "timestamp": datetime.now()
        })
        
        # Get appropriate LIMS agent
        if "reception" in agent_id:
            lims_agent = SampleReceptionAgent()
        elif "accessioning" in agent_id:
            lims_agent = SampleAccessioningAgent()
        else:
            lims_agent = SampleReceptionAgent()  # Default
        
        # Process the message
        try:
            if sample_context:
                # Create sample object from context
                sample = Sample(
                    sample_id=sample_context["sample_id"],
                    patient_id=sample_context["patient_id"],
                    state=SampleState(sample_context["state"]),
                    received_at=datetime.fromisoformat(sample_context["received_at"].replace("Z", "+00:00")),
                    sample_type=sample_context["sample_type"],
                    tests_requested=sample_context["tests_requested"],
                    priority=Priority(sample_context["priority"])
                )
                
                # Store sample in conversation
                conversation["sample"] = sample
                
                # Process with context
                response = await lims_agent.process_sample(sample, message)
            else:
                # Process without context
                response = await lims_agent.process_message(message)
            
            # Create response
            agent_response = response.get("message", "I understand. Let me help you with that.")
            
            # Add agent response to conversation
            conversation["messages"].append({
                "role": "agent",
                "content": agent_response,
                "timestamp": datetime.now()
            })
            
            # Prepare sample update if any
            sample_update = None
            if "updated_sample" in response and response["updated_sample"]:
                updated_sample = response["updated_sample"]
                sample_update = SampleModel(
                    sample_id=updated_sample["sample_id"],
                    patient_id=updated_sample["patient_id"],
                    state=updated_sample["state"],
                    barcode=updated_sample.get("barcode"),
                    accession_number=updated_sample.get("accession_number"),
                    received_at=updated_sample["received_at"],
                    sample_type=updated_sample["sample_type"],
                    tests_requested=updated_sample["tests_requested"],
                    priority=updated_sample["priority"],
                    location=updated_sample.get("location")
                )
            
            return MessageResponse(
                content=agent_response,
                action_suggestions=response.get("suggested_actions", [
                    "Verify sample information",
                    "Generate barcode",
                    "Move to next step",
                    "Need help"
                ]),
                workflow_context=WorkflowContext(
                    current_state=response.get("current_state", "RECEIVED"),
                    next_states=response.get("next_states", ["ACCESSIONED"]),
                    required_actions=response.get("required_actions", ["Verify information"])
                ),
                sample_update=sample_update
            )
            
        except Exception as e:
            # Fallback response
            logger.warning(f"Agent processing error: {e}")
            
            fallback_response = f"I understand your request about: {message}. I'm here to help you process this sample through our LIMS workflow. What specific action would you like to take?"
            
            conversation["messages"].append({
                "role": "agent",
                "content": fallback_response,
                "timestamp": datetime.now()
            })
            
            return MessageResponse(
                content=fallback_response,
                action_suggestions=[
                    "Verify sample information",
                    "Generate barcode",
                    "Move to accessioning",
                    "Flag for review"
                ],
                workflow_context=WorkflowContext(
                    current_state="RECEIVED",
                    next_states=["ACCESSIONED"],
                    required_actions=["Verify patient info", "Generate barcode"]
                ),
                sample_update=None
            )
            
    except Exception as e:
        logger.error(f"Failed to send LIMS message: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/lims/agents/create")
async def create_specialized_agent(sample_data: SampleData):
    """Create a specialized agent using the Agent Creator"""
    try:
        # Create embryo data based on sample characteristics
        embryo_data = {
            "embryo_id": f"embryo_{sample_data.sample_id}",
            "specialization_scores": {
                "sample_reception": 0.9,
                "sample_accessioning": 0.8,
                "urgent_processing": 0.9 if sample_data.priority == "STAT" else 0.3,
                "routine_processing": 0.7 if sample_data.priority == "ROUTINE" else 0.2,
                "quality_control": 0.6,
                "communication": 0.7
            },
            "patterns_detected": 85,
            "dominant_specialization": "sample_reception",
            "fitness_score": 0.85,
            "sample_context": {
                "priority": sample_data.priority,
                "tests_count": len(sample_data.tests_requested),
                "complexity": "high" if len(sample_data.tests_requested) > 3 else "standard"
            }
        }
        
        # Create agent using Agent Creator
        agent_blueprint = await agent_creator.create_agent(embryo_data)
        
        if agent_blueprint:
            logger.info(f"Created specialized agent: {agent_blueprint.name}")
            return {
                "success": True,
                "agent": {
                    "agent_id": agent_blueprint.agent_id,
                    "name": agent_blueprint.name,
                    "specialization": agent_blueprint.specialization,
                    "autonomy_level": agent_blueprint.autonomy_level,
                    "introduction_message": agent_blueprint.introduction_message
                }
            }
        else:
            raise HTTPException(status_code=500, detail="Failed to create agent")
            
    except Exception as e:
        logger.error(f"Failed to create specialized agent: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/lims/conversations/{conversation_id}")
async def get_conversation(conversation_id: str):
    """Get conversation history"""
    if conversation_id not in active_conversations:
        raise HTTPException(status_code=404, detail="Conversation not found")
    
    return active_conversations[conversation_id]

@app.get("/stats/agent_creator")
async def get_agent_creator_stats():
    """Get Agent Creator statistics"""
    return agent_creator.get_creation_stats()

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="127.0.0.1", port=8001, log_level="info")
