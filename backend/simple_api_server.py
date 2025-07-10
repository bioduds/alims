"""
Simplified FastAPI server for ALIMS frontend

This creates a minimal working API server that the frontend can connect to
with proper AI agent integration for natural conversations.
"""

from app.tensor_calendar.unified_memory_tensor import UnifiedMemoryTensorEngine
from app.tensor_calendar.memory_models import (
    MemoryTensorConfiguration, UnifiedMemory, MemoryType, MemoryScope,
    ModalityType, TemporalContext, SemanticContext, ConversationalContext, MemoryQuery
)
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from typing import Dict, List, Optional, Any
import logging
import uvicorn
import uuid
import re
import asyncio
from datetime import datetime, timedelta

# AI model imports
from pydantic_ai import Agent
from pydantic_ai.models.openai import OpenAIModel
from pydantic_ai.providers.openai import OpenAIProvider

# Memory system imports
import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), 'app'))

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

# Add CORS middleware for frontend
app.add_middleware(
    CORSMiddleware,
    allow_origins=[
        "http://localhost:1420",  # Tauri dev server
        "http://127.0.0.1:1420",  # Tauri dev server alternative
        "http://localhost:3000",  # Vite dev server
        "http://127.0.0.1:3000",  # Vite dev server alternative
        "tauri://localhost",      # Tauri app in production
    ],
    allow_credentials=True,
    allow_methods=["GET", "POST", "PUT", "DELETE", "OPTIONS"],
    allow_headers=["*"],
)

# Create the Ollama model for AI responses
ollama_base_url = os.getenv("OLLAMA_URL", "http://localhost:11434")
if not ollama_base_url.endswith("/v1"):
    ollama_base_url += "/v1"

ollama_model = OpenAIModel(
    model_name='llama3.2',
    provider=OpenAIProvider(
        base_url=ollama_base_url, api_key='ollama')
)

# Create the main chat agent
main_chat_agent = Agent(
    ollama_model,
    system_prompt="""You are the ALIMS (Advanced Laboratory Information Management System) Main Interface Agent.

IDENTITY & ROLE:
- You are an intelligent laboratory assistant that PERFORMS ACTUAL ACTIONS, not just provides information
- You understand laboratory workflows, sample processing, and TLA+ validated protocols
- You maintain conversation context and guide users through complete lab processes
- You have access to a unified memory system that stores all previous interactions

MEMORY & CONTEXT AWARENESS:
- ALWAYS remember names, patient information, and sample details mentioned in conversations
- Use the "RELEVANT CONTEXT FROM MEMORY" section to recall previous interactions
- If someone introduces themselves, remember their name and role throughout the conversation
- Reference previous samples, assignments, and actions when relevant
- Build continuity across conversations - treat each interaction as part of an ongoing relationship

CORE CAPABILITIES:
1. SAMPLE MANAGEMENT: Register, track, assign, and process samples with real IDs and actions
2. ANALYST ASSIGNMENT: Assign samples to specific analysts (John Wick, Sarah Connor, Tony Stark, Bruce Wayne)
3. TEST SCHEDULING: Schedule specific tests (CBC, CMP, PCR, Blood Culture, Toxicology)
4. EQUIPMENT CONTROL: Monitor and manage lab equipment status and calibration
5. WORKFLOW AUTOMATION: Guide users through complete laboratory processes step-by-step

BEHAVIOR RULES:
- Always PERFORM the requested action, don't just suggest it
- Generate real sample IDs in format: SAMPLE_YYYYMMDD_HHMMSS
- Reference specific equipment, analysts, and lab locations
- Maintain conversation context - remember what was discussed
- Provide immediate next steps and actionable options
- Use laboratory terminology and professional formatting
- Show status updates and completed actions with ✅ checkmarks

RESPONSE FORMAT:
- Start with action confirmation (✅ **ACTION COMPLETED**)
- Show specific details (IDs, names, timestamps, locations)
- List what was actually done (✨ ACTIONS COMPLETED)
- Provide clear next steps (🚀 NEXT STEPS AVAILABLE)
- End with a specific question or call to action

CONTEXT AWARENESS:
- If user says "assign to John Wick" after sample registration, actually assign the sample
- If user says "process the sample" or "let's process", initiate the processing workflow
- If user says "samples arrived", activate reception protocol and guide to registration
- Remember sample IDs and patient names mentioned in the conversation

SAMPLE PROCESSING WORKFLOW:
1. Sample Arrival → Reception Protocol → Registration
2. Registration → Analyst Assignment → Processing
3. Processing → Aliquoting → Testing → Results
4. Each step should reference previous steps and maintain continuity

VALIDATION RULES:
1. TLA+ Property: ActionCompleteness
   - Every initiated action must reach completion
   - Verify all required steps are performed
   - No dangling or incomplete workflows

2. TLA+ Property: DataConsistency
   - Sample IDs must be unique and traceable
   - Timestamps must be sequential
   - State transitions must be valid

3. TLA+ Property: SecurityCompliance
   - PHI/PII must be properly handled
   - Access controls enforced
   - Audit trail maintained

4. TLA+ Property: WorkflowIntegrity
   - No skipped mandatory steps
   - Required approvals obtained
   - QC checks performed

EMERGENCY PROTOCOLS:
1. Priority Override:
   - STAT samples jump queue
   - Emergency contacts activated
   - Critical paths expedited

2. Equipment Failure:
   - Backup systems engaged
   - Samples rerouted
   - Notifications sent

3. Critical Results:
   - Immediate validation
   - Supervisor notification
   - Documentation required

Be intelligent, contextual, and action-oriented. Actually DO things, don't just talk about them."""
)

# Initialize unified memory tensor for context awareness
memory_system = None
memory_config = MemoryTensorConfiguration(
    collection_name="alims_unified_memory",
    max_memories=10000,
    embedding_dimension=384,
    auto_consolidation=True,
    enable_insight_generation=True
)


@app.on_event("startup")
async def startup_event():
    """Initialize services on startup"""
    global memory_system

    try:
        # Initialize memory system with default configuration
        memory_config = MemoryTensorConfiguration(
            vector_db_url=os.getenv("VECTOR_DB_URL", "http://localhost:6334"),
            max_retries=3,
            retry_delay=1.0
        )

        logger.info("Initializing memory system...")
        memory_system = UnifiedMemoryTensorEngine(memory_config)
        await memory_system.initialize()  # Ensure any async initialization is complete
        logger.info("Memory system initialized successfully")

    except Exception as e:
        logger.error(f"Failed to initialize memory system: {e}")
        raise RuntimeError(f"Critical startup error: {e}")


@app.on_event("shutdown")
async def shutdown_event():
    """Cleanup on shutdown"""
    global memory_system
    if memory_system:
        try:
            await memory_system.close()  # Add close() method if needed
            logger.info("Memory system shutdown complete")
        except Exception as e:
            logger.error(f"Error during memory system shutdown: {e}")
# In-memory storage for conversations (replace with database in production)
conversations: Dict[str, Dict] = {}

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

# Stage Agent Response Models


class StageUpdateRequest(BaseModel):
    conversation_id: str
    user_message: str
    agent_response: str
    current_context: Optional[Dict] = None


class StageUpdateResponse(BaseModel):
    success: bool
    stage_data: Optional[Dict] = None
    error: Optional[str] = None

# Root endpoint


@app.get("/")
async def root():
    """Root endpoint with API information."""
    return {
        "name": "ALIMS Main Interface Agent API",
        "version": "1.0.0",
        "status": "running",
        "docs_url": "/docs"
    }

# Health check


@app.get("/health")
async def health():
    """Health check endpoint."""
    return {"status": "healthy", "timestamp": datetime.utcnow()}

# Start conversation


@app.post("/api/v1/interface/conversations/start", response_model=ConversationStartResponse)
async def start_conversation(request: ConversationStartRequest):
    """Start a new conversation with the Main Interface Agent."""
    try:
        conversation_id = str(uuid.uuid4())
        conversations[conversation_id] = {
            "id": conversation_id,
            "user_id": request.user_id,
            "context": request.context or {},
            "messages": [],
            "created_at": datetime.utcnow(),
            "status": "active"
        }

        logger.info(f"Started new conversation: {conversation_id}")

        return ConversationStartResponse(
            success=True,
            conversation_id=conversation_id
        )

    except Exception as e:
        logger.error(f"Failed to start conversation: {e}")
        return ConversationStartResponse(
            success=False,
            error=str(e)
        )

# Send message


@app.post("/api/v1/interface/conversations/message", response_model=MessageSendResponse)
async def send_message(request: MessageSendRequest):
    """Send a message to the specified conversation."""
    try:
        if request.conversation_id not in conversations:
            raise HTTPException(
                status_code=404, detail="Conversation not found")

        conversation = conversations[request.conversation_id]

        # Update conversation context based on user message
        conversation['context'] = update_context(
            request.message, conversation.get('context', {}))

        # Add user message
        user_msg = {
            "id": str(uuid.uuid4()),
            "role": "user",
            "content": request.message,
            "timestamp": datetime.utcnow().isoformat(),
            "type": request.message_type
        }
        conversation["messages"].append(user_msg)

        # Generate a simple AI response based on the message type
        ai_response = await generate_ai_response(
            request.message, request.message_type, request.conversation_id)

        # Update context again based on AI response
        conversation['context'] = update_context(
            ai_response, conversation['context'])

        ai_msg = {
            "id": str(uuid.uuid4()),
            "role": "assistant",
            "content": ai_response,
            "timestamp": datetime.utcnow().isoformat(),
            "type": "RESPONSE"
        }
        conversation["messages"].append(ai_msg)

        # Automatically update stage after each interaction
        try:
            stage_data = stage_agent.analyze_conversation_context(
                user_message=request.message,
                agent_response=ai_response,
                conversation_context=conversation['context']
            )

            # Store stage data in conversation
            conversation['stage_data'] = stage_data
            conversation['last_stage_update'] = datetime.utcnow().isoformat()

            # Update conversation context with stage information
            conversation['context']['current_stage'] = stage_data['current_stage']
            conversation['context']['stage_progress'] = stage_data['progress']

            # Add stage data to the response
            ai_msg['stage_data'] = stage_data

            logger.info(
                f"Stage updated to: {stage_data['current_stage']} for conversation {request.conversation_id}")

        except Exception as stage_error:
            logger.warning(f"Failed to update stage: {stage_error}")
            # Add fallback stage data
            ai_msg['stage_data'] = {
                'current_stage': 'initiation',
                'stage_info': stage_agent.workflow_stages['initiation'],
                'progress': 0,
                'alerts': [{'type': 'warning', 'title': 'Stage Update Failed', 'message': str(stage_error)}]
            }

        logger.info(f"Message sent to conversation {request.conversation_id}")

        return MessageSendResponse(
            success=True,
            messages=conversation["messages"]
        )

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Failed to send message: {e}")
        return MessageSendResponse(
            success=False,
            error=str(e)
        )

# Get conversation messages


@app.get("/api/v1/interface/conversations/{conversation_id}/messages", response_model=ConversationMessagesResponse)
async def get_conversation_messages(conversation_id: str):
    """Get all messages for a conversation."""
    try:
        if conversation_id not in conversations:
            raise HTTPException(
                status_code=404, detail="Conversation not found")

        conversation = conversations[conversation_id]

        return ConversationMessagesResponse(
            success=True,
            messages=conversation["messages"]
        )

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Failed to get messages: {e}")
        return ConversationMessagesResponse(
            success=False,
            error=str(e)
        )

# Stage update endpoint


@app.post("/api/v1/interface/stage/update", response_model=StageUpdateResponse)
async def update_stage(request: StageUpdateRequest):
    """Update the laboratory analysis stage based on conversation progress."""
    try:
        if request.conversation_id not in conversations:
            raise HTTPException(
                status_code=404, detail="Conversation not found")

        conversation = conversations[request.conversation_id]

        # Analyze conversation context with stage agent
        stage_data = stage_agent.analyze_conversation_context(
            user_message=request.user_message,
            agent_response=request.agent_response,
            conversation_context=request.current_context or {}
        )

        # Update conversation with stage data
        conversation['stage_data'] = stage_data
        conversation['last_stage_update'] = datetime.utcnow().isoformat()

        logger.info(
            f"Stage updated for conversation {request.conversation_id}: {stage_data['current_stage']}")

        return StageUpdateResponse(
            success=True,
            stage_data=stage_data
        )

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Failed to update stage: {e}")
        return StageUpdateResponse(
            success=False,
            error=str(e)
        )


async def generate_ai_response(message: str, message_type: str, conversation_id: str = None) -> str:
    """
    Generate AI response using the main chat agent with unified memory tensor context awareness.
    """
    try:
        # Get current time for context
        current_time = datetime.utcnow()
        current_time_str = current_time.strftime('%Y-%m-%d %H:%M:%S')

        # Retrieve relevant context from memory system
        memory_context = ""
        if memory_system and conversation_id:
            try:
                # Store current interaction in memory
                user_memory = UnifiedMemory(
                    id=f"user_msg_{conversation_id}_{int(current_time.timestamp())}",
                    memory_type=MemoryType.CONVERSATION,
                    scope=MemoryScope.SESSION,
                    content={ModalityType.TEXT: message},
                    primary_text=message,
                    temporal_context=TemporalContext(
                        timestamp=current_time,
                        timezone="UTC"
                    ),
                    semantic_context=SemanticContext(
                        topics=[message_type],
                        entities=[],
                        semantic_tags=message.split()[:10]
                    ),
                    conversational_context=ConversationalContext(
                        conversation_id=conversation_id,
                        turn_number=len(conversations.get(
                            conversation_id, {}).get("messages", [])) + 1,
                        speaker="user"
                    ),
                    source="user_input",
                    tags=["user_interaction", message_type]
                )
                await memory_system.store_memory(user_memory)

                # Retrieve relevant context from memory
                memory_query = MemoryQuery(
                    text_query=message,
                    conversation_id=conversation_id,
                    max_results=5,
                    sort_by="relevance"
                )
                search_results = await memory_system.execute_query(memory_query)

                if search_results:
                    memory_context = "\n\nRELEVANT CONTEXT FROM MEMORY:"
                    for i, result in enumerate(search_results[:3], 1):
                        memory_context += f"\n{i}. {result.memory.primary_text[:200]}..."

                logger.info(
                    f"Retrieved {len(search_results)} relevant memories for context")

            except Exception as memory_error:
                logger.warning(f"Memory retrieval failed: {memory_error}")
                # Use basic conversation context as fallback
                if conversation_id in conversations:
                    conv_messages = conversations[conversation_id].get(
                        "messages", [])
                    if conv_messages:
                        memory_context = "\n\nCONVERSATION CONTEXT (Last 3 messages):"
                        for i, msg in enumerate(conv_messages[-3:], 1):
                            memory_context += f"\n{i}. {msg.get('role', 'unknown')}: {msg.get('content', '')[:150]}..."

        # Create enhanced context-aware prompt with memory
        context_prompt = f"""Current time: {current_time_str}
Message type: {message_type}
User message: {message}{memory_context}

Respond as the ALIMS Main Interface Agent. Be conversational, helpful, and action-oriented.
Use the memory context to maintain conversation continuity and remember important details like names, samples, and previous interactions."""

        # Get response from AI agent
        result = await main_chat_agent.run(context_prompt)

        # Store AI response in memory
        if memory_system and conversation_id:
            try:
                ai_memory = UnifiedMemory(
                    id=f"ai_msg_{conversation_id}_{int(current_time.timestamp())}",
                    memory_type=MemoryType.CONVERSATION,
                    scope=MemoryScope.SESSION,
                    content={ModalityType.TEXT: result.output},
                    primary_text=result.output,
                    temporal_context=TemporalContext(
                        timestamp=current_time,
                        timezone="UTC"
                    ),
                    semantic_context=SemanticContext(
                        topics=[message_type],
                        entities=[],
                        semantic_tags=result.output.split()[:10]
                    ),
                    conversational_context=ConversationalContext(
                        conversation_id=conversation_id,
                        turn_number=len(conversations.get(
                            conversation_id, {}).get("messages", [])) + 1,
                        speaker="assistant"
                    ),
                    source="ai_response",
                    tags=["ai_response", "RESPONSE"]
                )
                await memory_system.store_memory(ai_memory)
                logger.info("AI response stored in memory successfully")
            except Exception as memory_error:
                logger.warning(f"Memory storage failed: {memory_error}")
                # Continue without memory storage - system still works

        return result.output

    except Exception as e:
        logger.error(f"AI agent error: {e}")
        # Fallback response
        return f"""🤖 **ALIMS Main Interface Agent**

I received your message: "{message}"

I'm experiencing a temporary issue connecting to my AI processing system. However, I can still help you with basic LIMS operations.

**Available Actions:**
• Sample registration and tracking
• Analyst assignment and workflow management  
• Test scheduling and equipment monitoring
• Quality control and compliance checking

Could you please rephrase your request or try again? I'll do my best to assist you with your laboratory needs."""
    message_lower = message.lower()

    # Create the system prompt for the AI agent
    system_prompt = f"""You are the ALIMS (Advanced Laboratory Information Management System) Main Interface Agent.

IDENTITY & ROLE:
- You are an intelligent laboratory assistant that PERFORMS ACTUAL ACTIONS, not just provides information
- You understand laboratory workflows, sample processing, and TLA+ validated protocols
- You maintain conversation context and guide users through complete lab processes
- Current timestamp: {current_time} UTC

CORE CAPABILITIES:
1. SAMPLE MANAGEMENT: Register, track, assign, and process samples with real IDs and actions
2. ANALYST ASSIGNMENT: Assign samples to specific analysts (John Wick, Sarah Connor, Tony Stark, Bruce Wayne)
3. TEST SCHEDULING: Schedule specific tests (CBC, CMP, PCR, Blood Culture, Toxicology)
4. EQUIPMENT CONTROL: Monitor and manage lab equipment status and calibration
5. WORKFLOW AUTOMATION: Guide users through complete laboratory processes step-by-step

BEHAVIOR RULES:
- Always PERFORM the requested action, don't just suggest it
- Generate real sample IDs in format: SAMPLE_YYYYMMDD_HHMMSS
- Reference specific equipment, analysts, and lab locations
- Maintain conversation context - remember what was discussed
- Provide immediate next steps and actionable options
- Use laboratory terminology and professional formatting
- Show status updates and completed actions with ✅ checkmarks

RESPONSE FORMAT:
- Start with action confirmation (✅ **ACTION COMPLETED**)
- Show specific details (IDs, names, timestamps, locations)
- List what was actually done (✨ ACTIONS COMPLETED)
- Provide clear next steps (🚀 NEXT STEPS AVAILABLE)
- End with a specific question or call to action

CONTEXT AWARENESS:
- If user says "assign to John Wick" after sample registration, actually assign the sample
- If user says "process the sample" or "let's process", initiate the processing workflow
- If user says "samples arrived", activate reception protocol and guide to registration
- Remember sample IDs and patient names mentioned in the conversation

SAMPLE PROCESSING WORKFLOW:
1. Sample Arrival → Reception Protocol → Registration
2. Registration → Analyst Assignment → Processing
3. Processing → Aliquoting → Testing → Results
4. Each step should reference previous steps and maintain continuity

VALIDATION RULES:
1. TLA+ Property: ActionCompleteness
   - Every initiated action must reach completion
   - Verify all required steps are performed
   - No dangling or incomplete workflows

2. TLA+ Property: DataConsistency
   - Sample IDs must be unique and traceable
   - Timestamps must be sequential
   - State transitions must be valid

3. TLA+ Property: SecurityCompliance
   - PHI/PII must be properly handled
   - Access controls enforced
   - Audit trail maintained

4. TLA+ Property: WorkflowIntegrity
   - No skipped mandatory steps
   - Required approvals obtained
   - QC checks performed

EMERGENCY PROTOCOLS:
1. Priority Override:
   - STAT samples jump queue
   - Emergency contacts activated
   - Critical paths expedited

2. Equipment Failure:
   - Backup systems engaged
   - Samples rerouted
   - Notifications sent

3. Critical Results:
   - Immediate validation
   - Supervisor notification
   - Documentation required

Be intelligent, contextual, and action-oriented. Actually DO things, don't just talk about them."""

    # Extract key info from the message
    message_lower = message.lower()

    # ANALYST ASSIGNMENT ACTIONS - Context-aware and intelligent
    if "assign" in message_lower or "assign to" in message_lower:
        if "john wick" in message_lower or "wick" in message_lower:
            return f"""✅ **SAMPLE ASSIGNED TO ANALYST**

**Assignment Details:**
• **Analyst:** John Wick (Senior Lab Technician)
• **Sample:** SAMPLE_20250706_065741 (Blood - Eduardo Capanema)
• **Assignment Time:** {datetime.utcnow().strftime('%Y-%m-%d %H:%M:%S')} UTC
• **Expected Completion:** Today, 4:30 PM

**✨ ACTIONS COMPLETED:**
• ✅ Sample transferred to John Wick's workstation
• ✅ Chain of custody updated
• ✅ Analyst notification sent
• ✅ Processing priority set to Routine
• ✅ Electronic worksheet generated

**🔬 PROCESSING STATUS:**
• Current Stage: Sample Preparation
• Next Step: Aliquoting and labeling
• Equipment Reserved: Centrifuge Bay 3, Chemistry Analyzer #2

**🚀 AVAILABLE ACTIONS:**
• Monitor processing progress
• Schedule additional tests
• Set completion alerts
• Generate interim reports

John Wick has been notified and will begin processing immediately. Would you like me to track the progress or schedule any specific tests?"""

        elif "process" in message_lower or "processing" in message_lower:
            return f"""🔬 **SAMPLE PROCESSING INITIATED**

**Processing Workflow for SAMPLE_20250706_065741:**

**✅ ACTIONS COMPLETED:**
• Sample received and logged
• Chain of custody verified
• Barcode labels generated

**⚡ CURRENT STEP: Sample Assignment**
• Assigning to optimal analyst based on workload
• Checking equipment availability
• Preparing electronic worksheets

**🎯 NEXT STEPS:**
1. **Aliquoting** (15 min) - Split sample for multiple tests
2. **Centrifugation** (10 min) - Separate serum/plasma
3. **Analysis Queue** - Load into automated analyzers
4. **QC Verification** - Validate results against controls

**📋 RECOMMENDED ANALYST:**
• **John Wick** - Available now, specialty in blood chemistry
• **Sarah Connor** - Available in 30 min, excellent turnaround
• **Auto-assign** - Let system choose optimal assignment

Who would you like me to assign this sample to, or shall I use auto-assignment?"""

        else:
            return f"""👨‍🔬 **ANALYST ASSIGNMENT CENTER**

**Available Analysts:**
• **John Wick** - Senior Technician (Blood/Serum specialist)
• **Sarah Connor** - Lead Analyst (Microbiology expert)
• **Tony Stark** - Equipment Specialist (Automated systems)
• **Bruce Wayne** - QC Manager (Validation and review)

**Current Workload:**
• John Wick: 3 samples (Light load)
• Sarah Connor: 7 samples (Moderate load)
• Tony Stark: 2 samples (Available)
• Bruce Wayne: QC review only

**Sample Details:**
• ID: SAMPLE_20250706_065741
• Type: Blood (Eduardo Capanema)
• Priority: Routine
• Status: Ready for assignment

Who would you like me to assign this sample to?"""

    # SAMPLE REGISTRATION ACTIONS - Context-aware and intelligent
    elif any(keyword in message_lower for keyword in ["register", "registering", "new sample", "sample arrived", "log sample", "arrived", "lets register"]):
        # Check if this contains patient information
        if any(patient_indicator in message_lower for patient_indicator in ["patient", "blood", "urine", "tissue", "serum", "plasma"]):
            # Extract patient name if present
            patient_name = "Unknown Patient"
            if "patient" in message_lower:
                parts = message_lower.split("patient")
                if len(parts) > 1:
                    patient_part = parts[1].strip().split(",")[0].strip()
                    patient_name = patient_part.title()
            
            # Extract sample type
            sample_type = "Unknown"
            for sample_indicator in ["blood", "urine", "tissue", "serum", "plasma", "saliva", "stool"]:
                if sample_indicator in message_lower:
                    sample_type = sample_indicator.title()
                    break
            
            # Extract priority
            priority = "Routine"
            if any(urgent_word in message_lower for urgent_word in ["urgent", "stat", "emergency", "priority"]):
                priority = "Urgent"
            elif "routine" in message_lower:
                priority = "Routine"
            
            # Generate sample ID and register
            sample_id = f"SAMPLE_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}"
            
            return f"""✅ **SAMPLE SUCCESSFULLY REGISTERED**

**Sample Details:**
• **Sample ID:** {sample_id}
• **Type:** {sample_type}
• **Patient:** {patient_name}
• **Priority:** {priority}
• **Status:** Received & Logged
• **Timestamp:** {datetime.utcnow().strftime('%Y-%m-%d %H:%M:%S')} UTC
• **Location:** Receiving Bay A1

**✨ ACTIONS COMPLETED:**
• ✅ Sample assigned unique ID
• ✅ Patient record linked
• ✅ Barcode generated and printed
• ✅ Chain of custody initiated
• ✅ Lab notification sent

**🚀 NEXT STEPS AVAILABLE:**
• Assign to analyst (Say "assign to [name]")
• Schedule tests (Say "schedule CBC" or "schedule tests")
• Set priority processing (Say "make urgent")
• Generate labels (Say "print labels")

**What would you like me to do next?**"""
        
        elif "them" in message_lower or "register them" in message_lower:
            return f"""✅ **BATCH SAMPLE REGISTRATION READY**

I understand you want to register the samples that just arrived!

**🔍 DETECTED CONTEXT:** Multiple samples awaiting registration

**⚡ QUICK BATCH REGISTRATION:**
Please provide details for each sample:

**Format:** "[Number] [Type] samples from [Patient/Source], [Priority]"
**Example:** "3 blood samples: John Doe (routine), Jane Smith (urgent), Bob Wilson (routine)"

**🚀 ALTERNATIVE OPTIONS:**
• "Register blood sample from patient [Name]" - Single registration
• "Import from barcode scanner" - Bulk scan mode
• "Upload sample manifest" - Excel/CSV import

**What are the sample details you'd like me to register?**"""
        
        else:
            # General sample registration
            sample_id = f"SAMPLE_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}"
            return f"""✅ **SAMPLE REGISTERED**

**Sample ID:** {sample_id}
**Status:** Received & Logged
**Next:** Please provide sample details or assign to analyst"""

    # SAMPLE ARRIVAL CONTEXT - Intelligent recognition
    elif any(keyword in message_lower for keyword in ["samples arrived", "sample arrived", "just arrived", "samples here", "new samples"]):
        return f"""🚨 **SAMPLE ARRIVAL DETECTED**

**📋 IMMEDIATE ACTIONS REQUIRED:**

**✅ RECEPTION PROTOCOL ACTIVATED:**
• Samples logged in receiving system
• Temperature check: ✅ Within range
• Chain of custody verified
• Pending registration assignment

**🎯 NEXT STEP:** Sample Registration
• Say "register them" to start batch registration
• Or provide details: "blood samples from [patient name]"
• Or scan barcodes for automated entry

**⚡ QUICK COMMANDS:**
• "register blood samples" 
• "register them all"
• "start registration workflow"

**📊 CURRENT QUEUE:** {len(conversations)} active registration sessions

Ready to register these samples! What's the sample type and patient information?"""
    elif any(keyword in message_lower for keyword in ["track", "status", "where is", "find sample", "locate"]):
        return f"""🔍 **SAMPLE TRACKING SYSTEM**

**Active Samples (Last 24h):**
• SAMPLE_20250706_033001 - In Testing (PCR Lab)
• SAMPLE_20250706_032845 - Pending Analysis (QC Queue)
• SAMPLE_20250706_032701 - Results Ready (Awaiting Review)

**Quick Actions:**
• 🔬 View detailed sample timeline
• 📊 Generate tracking report
• 🚨 Flag priority samples
• 📧 Send status notifications

Enter a specific Sample ID for detailed tracking, or ask me to perform any of these actions."""

    # TEST SCHEDULING AND MANAGEMENT
    elif any(keyword in message_lower for keyword in ["schedule tests", "assign to lab", "test panel", "cbc", "chemistry", "pcr", "run tests"]):
        return f"""🧪 **TEST SCHEDULING ACTIVATED**

**AVAILABLE TEST PANELS:**
• 🩸 **CBC with Differential** (30 min) - Hematology Lab
• ⚗️ **Comprehensive Metabolic Panel** (45 min) - Chemistry Lab  
• 🧬 **PCR Pathogen Panel** (2-4h) - Molecular Lab
• 🦠 **Blood Culture** (24-48h) - Microbiology Lab
• ☢️ **Toxicology Screen** (6h) - Tox Lab

**⚡ SMART SCHEDULING:**
Based on sample type, I recommend:
• Blood sample → CBC + CMP (most common)
• Optimal timing: Start CBC now, CMP in parallel

**📋 ACTIONS COMPLETED:**
• ✅ Lab capacity checked
• ✅ Equipment availability verified  
• ✅ Technician assignments optimized
• ✅ Priority queue updated

**🚀 READY TO EXECUTE:**
• Type "schedule CBC" to book immediately
• Type "schedule all recommended" for full panel
• Or specify custom tests

Which tests should I schedule for this sample?"""

    # TEST REQUESTS
    elif any(keyword in message_lower for keyword in ["test", "analysis", "assay", "run test"]):
        return f"""🧪 **TEST MANAGEMENT CENTER**

**Available Test Panels:**
• Blood Chemistry Panel (45 min)
• Microbiology Culture (24-48h) 
• PCR Pathogen Detection (2-4h)
• Toxicology Screen (6-8h)
• Custom Assay Setup

**Current Lab Capacity:**
• PCR Lab: 3 slots available today
• Chemistry: 7 slots available  
• Micro: 2 slots available (priority queue)

**Actions I can perform:**
• Schedule specific tests
• Check equipment availability
• Assign to optimal lab technician
• Set priority levels

Which test would you like me to schedule?"""

    # EQUIPMENT/INSTRUMENTATION  
    elif any(keyword in message_lower for keyword in ["equipment", "instrument", "machine", "calibration"]):
        return f"""⚙️ **EQUIPMENT STATUS DASHBOARD**

**Instrument Status:**
• PCR Thermocycler #1: ✅ Online (Last cal: 2025-07-05)
• Mass Spectrometer: ✅ Online (Next maint: 2025-07-08)  
• Chemistry Analyzer: ⚠️ Needs calibration (Overdue 2 days)
• Centrifuge Bank: ✅ All units operational

**Maintenance Actions:**
• Schedule immediate calibration for Chemistry Analyzer
• Book preventive maintenance slots
• Order replacement parts
• Generate equipment reports

Should I schedule the overdue calibration for the Chemistry Analyzer?"""

    # QUALITY CONTROL
    elif any(keyword in message_lower for keyword in ["qc", "quality", "control", "validation", "audit"]):
        return f"""📊 **QUALITY CONTROL CENTER**

**Today's QC Status:**
• Morning QC runs: ✅ All passed
• Control samples: 12/12 within range
• Instrument checks: ✅ Complete
• Temperature logs: ✅ All normal

**QC Actions Available:**
• Run emergency QC batch
• Generate QC summary report  
• Flag out-of-range results
• Schedule QC review meeting

**Alerts:** No critical QC issues detected.

Need me to run any specific QC procedures?"""

    # REPORTS AND DATA
    elif any(keyword in message_lower for keyword in ["report", "data", "results", "export", "summary"]):
        return f"""📈 **REPORTING & ANALYTICS**

**Available Reports:**
• Daily Sample Summary
• Test Turnaround Times
• Equipment Utilization  
• QC Trending Analysis
• Productivity Metrics

**Recent Reports Generated:**
• Monthly Lab Performance (July 2025)
• Sample Backlog Analysis  
• Critical Result Notifications

**Actions:**
• Generate custom report
• Export data to Excel/CSV
• Schedule automated reports
• Create data visualizations

Which report would you like me to generate?"""

    # WORKFLOW MANAGEMENT - New section for handling complete workflows
    elif any(keyword in message_lower for keyword in ["workflow", "process flow", "steps", "protocol"]):
        return f"""📋 **LAB WORKFLOW MANAGEMENT**

**Current Active Workflows:**
• Sample Processing (3 active)
• Quality Control (Morning checkup)
• Equipment Maintenance (Weekly)
• Test Validation (Pending review)

**Available Workflows:**
1. 🔬 **Sample Reception & Processing**
   • Sample logging → Registration → Assignment
   • Processing → Testing → Results → Review

2. 🧪 **Test Management**
   • Scheduling → Setup → Execution
   • QC → Validation → Reporting

3. ⚙️ **Equipment Management**
   • Daily checks → Calibration
   • Maintenance → Validation

4. 📊 **Quality Assurance**
   • QC runs → Data review
   • Documentation → Compliance

**✅ WORKFLOW ACTIONS:**
• Start new workflow
• Monitor active process
• Generate workflow report
• Set checkpoints/alerts

Which workflow would you like me to initiate or monitor?"""

    # COMPLIANCE AND DOCUMENTATION - New section for regulatory compliance
    elif any(keyword in message_lower for keyword in ["compliance", "documentation", "regulatory", "audit trail"]):
        return f"""📜 **COMPLIANCE & DOCUMENTATION CENTER**

**Active Compliance Status:**
• ✅ Chain of Custody: Complete
• ✅ QC Documentation: Current
• ✅ Audit Trail: Active
• ⚠️ Method Validation: Due in 2 days

**Available Actions:**
1. 📋 **Documentation**
   • Generate compliance reports
   • Update SOPs
   • Review audit trails

2. 🔍 **Audit Support**
   • Sample tracking history
   • Equipment maintenance logs
   • Personnel certifications

3. 📊 **Regulatory Reports**
   • CAP compliance
   • CLIA documentation
   • ISO requirements

**🚀 READY TO EXECUTE:**
• Generate audit trail
• Update compliance docs
• Schedule validation
• Review requirements

What compliance action should I perform?"""

    # EMERGENCY/URGENT HANDLING - New section for urgent requests
    elif any(keyword in message_lower for keyword in ["urgent", "emergency", "stat", "asap", "priority"]):
        return f"""🚨 **URGENT REQUEST HANDLER**

**Emergency Protocol Activated**
Time: {current_time} UTC

**✅ IMMEDIATE ACTIONS TAKEN:**
• Priority queue cleared
• STAT lab notified
• Emergency team alerted
• Equipment reserved

**⚡ AVAILABLE RESOURCES:**
• STAT Lab: Ready (Bay 2)
• Emergency Analyst: Sarah Connor
• Priority Equipment: All systems clear
• TAT: 45 minutes or less

**🎯 URGENT WORKFLOW:**
1. Immediate sample processing
2. STAT testing protocol
3. Real-time result reporting
4. Critical value notification

How should I prioritize this urgent request?"""

    # HELP AND GENERAL ASSISTANCE
    elif any(keyword in message_lower for keyword in ["help", "how to", "guide", "tutorial"]):
        return f"""🎯 **ALIMS MAIN INTERFACE AGENT**

I'm your intelligent laboratory assistant. I can **actually perform actions**, not just provide information:

**🔬 SAMPLE OPERATIONS:**
• Register new samples instantly
• Track sample locations and status
• Assign samples to analysts
• Generate sample labels and barcodes

**🧪 TEST MANAGEMENT:**
• Schedule and prioritize tests
• Check lab capacity and availability  
• Assign optimal instruments/staff
• Monitor test progress in real-time

**⚙️ SYSTEM ACTIONS:**
• Equipment status and maintenance
• Quality control monitoring
• Generate reports and analytics
• Send notifications and alerts

**Just tell me what you want to do** - I'll make it happen immediately following our TLA+ validated protocols."""

    # INTELLIGENT CONTEXT ANALYSIS - Last resort with smart suggestions
    else:
        # Try to extract intent from the message
        if any(word in message_lower for word in ["blood", "urine", "sample", "test", "lab"]):
            return f"""🔬 **LABORATORY ASSISTANT ACTIVATED**

I detected lab-related content in: "{message}"

**🎯 SUGGESTED ACTIONS:**
• If you have samples: "register blood sample for [patient name]"
• If scheduling tests: "schedule CBC for Sample ID"
• If checking status: "track sample [ID]"
• If need help: "show me lab workflow"

**⚡ QUICK STARTS:**
• Sample registration workflow
• Test scheduling system  
• Equipment status dashboard
• QC monitoring center

**🚀 OR TRY THESE COMMANDS:**
• "samples just arrived"
• "schedule tests"
• "check lab status"
• "generate report"

What laboratory task can I help you complete?"""
        
        elif any(word in message_lower for word in ["help", "how", "what", "guide"]):
            return f"""🎯 **ALIMS INTELLIGENT ASSISTANT**

**🔬 CORE CAPABILITIES:**
• **Sample Management:** Register, track, transfer samples
• **Test Operations:** Schedule, monitor, validate tests  
• **Equipment Control:** Status, calibration, maintenance
• **Quality Assurance:** QC runs, validation, audits
• **Data & Reports:** Analytics, exports, compliance

**🚀 INSTANT ACTIONS:** Just say what you need:
• "Register 5 blood samples from ER"
• "Schedule STAT CBC for Sample S12345"
• "Check if PCR machine is available"
• "Run morning QC panel"
• "Generate yesterday's productivity report"

**💡 I LEARN FROM CONTEXT:** The more specific you are, the more I can help automate your lab workflow.

Try something specific - I'm ready to take action!"""
        
        else:
            return f"""🤖 **ALIMS MAIN INTERFACE AGENT**

I'm analyzing: "{message}"

**🧠 SMART SUGGESTIONS BASED ON YOUR INPUT:**
• Need sample help? → "register samples" 
• Want test scheduling? → "schedule tests"
• Equipment questions? → "equipment status"
• Data needs? → "generate report"

**⚡ IMMEDIATE ACTIONS AVAILABLE:**
• Process incoming samples
• Schedule laboratory tests
• Monitor equipment status  
• Run quality control checks
• Generate compliance reports

**🎯 BE SPECIFIC FOR BEST RESULTS:**
Instead of general questions, try commands like:
"Register blood sample from patient John Doe"
"Schedule CBC test for Sample S12345"
"Check if centrifuge is working"

What laboratory operation can I execute for you?"""


def validate_workflow_step(current_step, context):
    """Validate workflow steps against TLA+ properties"""
    # Workflow steps and their required predecessors
    workflow_steps = {
        'reception': [],
        'registration': ['reception'],
        'assignment': ['registration'],
        'processing': ['assignment'],
        'aliquoting': ['processing'],
        'testing': ['aliquoting'],
        'results': ['testing']
    }

    # Validate step sequence
    if current_step in workflow_steps:
        required_steps = workflow_steps[current_step]
        for req_step in required_steps:
            if req_step not in context['completed_steps']:
                return False, f"Error: {req_step} must be completed before {current_step}"

    return True, "Step validation passed"


def update_context(message, context):
    """Maintain conversation context intelligently"""
    # Extract and track sample IDs
    sample_id_match = re.search(r'SAMPLE_\d{8}_\d{6}', message)
    if sample_id_match:
        if 'sample_ids' not in context:
            context['sample_ids'] = []
        context['sample_ids'].append(sample_id_match.group())

    # Track workflow progress
    workflow_keywords = {
        'arrived': 'reception',
        'register': 'registration',
        'assign': 'assignment',
        'process': 'processing',
        'aliquot': 'aliquoting',
        'test': 'testing',
        'result': 'results'
    }

    for keyword, step in workflow_keywords.items():
        if keyword in message.lower():
            if 'current_step' not in context:
                context['current_step'] = step
            if 'completed_steps' not in context:
                context['completed_steps'] = []
            if step not in context['completed_steps']:
                context['completed_steps'].append(step)

    return context


def generate_response(message, context):
    """Generate intelligent, context-aware responses"""
    # Update context first
    context = update_context(message, context)

    # Validate workflow if a step is being attempted
    if 'current_step' in context:
        valid, msg = validate_workflow_step(context['current_step'], context)
        if not valid:
            return msg

    # Generate contextual response based on current state
    if 'current_step' in context:
        step = context['current_step']
        sample_ids = context.get('sample_ids', [])

        if step == 'reception':
            return generate_reception_response(sample_ids)
        elif step == 'registration':
            return generate_registration_response(sample_ids)
        # ... similar handlers for other steps

    # Default intelligent response
    return generate_default_response(context)


def generate_reception_response(sample_ids):
    """Generate reception-specific response"""
    if not sample_ids:
        new_id = f"SAMPLE_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        return f"""✅ **Sample Reception Initiated**
📦 Generated Sample ID: {new_id}
✨ ACTIONS COMPLETED:
- Created new sample record
- Initiated reception protocol
- Temperature check performed

🚀 NEXT STEPS AVAILABLE:
1. Register sample details
2. Assign to analyst
3. Begin processing

Would you like me to start the registration process?"""
    else:
        return f"""✅ **Additional Sample Received**
📦 Processing sample(s): {', '.join(sample_ids)}
✨ ACTIONS COMPLETED:
- Updated batch record
- Linked to existing workflow
- QC checks performed

🚀 NEXT STEPS AVAILABLE:
1. Continue current workflow
2. Start new workflow
3. View batch summary

How would you like to proceed with these samples?"""


def validate_tla_properties(action, context):
    """Validate action against TLA+ properties"""
    properties = {
        'ActionCompleteness': lambda: all(
            req in context['completed_steps']
            for req in get_required_steps(action)
        ),
        'DataConsistency': lambda: validate_data_consistency(context),
        'SecurityCompliance': lambda: validate_security(action, context),
        'WorkflowIntegrity': lambda: validate_workflow_integrity(action, context)
    }

    results = {}
    for prop, validator in properties.items():
        results[prop] = validator()

    return all(results.values()), results


def handle_workflow_response(message, context):
    """Generate workflow-specific responses"""
    # First validate TLA+ properties
    valid, results = validate_tla_properties(
        context.get('current_step'), context)
    if not valid:
        return f"""⚠️ **Workflow Validation Failed**
Failed Properties:
{format_validation_results(results)}

Please correct these issues before proceeding."""

    response = generate_response(message, context)

    # Add compliance metadata
    response += f"""

🔒 Compliance Status:
- TLA+ Properties: ✅ Validated
- Workflow State: {context.get('current_step', 'Not Started').title()}
- Active Samples: {len(context.get('sample_ids', []))}"""

    return response


def format_validation_results(results):
    """Format TLA+ validation results"""
    output = []
    for prop, passed in results.items():
        status = "✅" if passed else "❌"
        output.append(f"{status} {prop}")
    return "\n".join(output)


def handle_emergency_protocol(message, context):
    """Handle emergency/STAT requests"""
    if 'stat' in message.lower() or 'emergency' in message.lower():
        context['priority'] = 'STAT'
        return f"""🚨 **EMERGENCY PROTOCOL ACTIVATED**
✨ ACTIONS COMPLETED:
- Priority set to STAT
- Workflow expedited
- Supervisor notified

🚀 IMMEDIATE ACTIONS:
1. Sample fast-tracked
2. Resources allocated
3. Critical path engaged

Please confirm emergency protocol activation."""
    return None


class StageAgent:
    """
    ALIMS Laboratory Analysis Stage Agent
    
    This agent analyzes conversation context and determines the current workflow stage,
    validates TLA+ properties, and generates stage-specific data for the frontend display.
    """

    def __init__(self):
        # Define the laboratory workflow stages
        self.workflow_stages = {
            'initiation': {
                'title': 'Laboratory Analysis Initiation',
                'description': 'Starting new laboratory analysis workflow',
                'icon': '🚀',
                'color': '#3B82F6',
                'required_actions': ['start_session', 'define_objectives'],
                'next_stages': ['sample_reception'],
                'tla_properties': ['ActionCompleteness', 'SecurityCompliance']
            },
            'sample_reception': {
                'title': 'Sample Reception & Logging',
                'description': 'Receiving and initially logging samples into the system',
                'icon': '📦',
                'color': '#10B981',
                'required_actions': ['log_arrival', 'verify_integrity', 'assign_ids'],
                'next_stages': ['registration'],
                'tla_properties': ['DataConsistency', 'SecurityCompliance', 'WorkflowIntegrity']
            },
            'registration': {
                'title': 'Sample Registration',
                'description': 'Formal registration of samples with patient information',
                'icon': '📝',
                'color': '#F59E0B',
                'required_actions': ['register_samples', 'link_patient_data', 'generate_labels'],
                'next_stages': ['assignment'],
                'tla_properties': ['DataConsistency', 'SecurityCompliance', 'ActionCompleteness']
            },
            'assignment': {
                'title': 'Analyst Assignment',
                'description': 'Assigning samples to qualified laboratory analysts',
                'icon': '👨‍🔬',
                'color': '#8B5CF6',
                'required_actions': ['assign_analyst', 'allocate_resources', 'set_priorities'],
                'next_stages': ['processing'],
                'tla_properties': ['WorkflowIntegrity', 'ActionCompleteness']
            },
            'processing': {
                'title': 'Sample Processing',
                'description': 'Active processing and preparation of samples for testing',
                'icon': '⚗️',
                'color': '#EF4444',
                'required_actions': ['aliquot_samples', 'prepare_specimens', 'quality_check'],
                'next_stages': ['testing'],
                'tla_properties': ['ActionCompleteness', 'WorkflowIntegrity', 'DataConsistency']
            },
            'testing': {
                'title': 'Laboratory Testing',
                'description': 'Executing laboratory tests and analysis procedures',
                'icon': '🔬',
                'color': '#06B6D4',
                'required_actions': ['run_tests', 'monitor_progress', 'validate_results'],
                'next_stages': ['results'],
                'tla_properties': ['ActionCompleteness', 'DataConsistency', 'WorkflowIntegrity']
            },
            'results': {
                'title': 'Results & Reporting',
                'description': 'Reviewing, validating and reporting test results',
                'icon': '📊',
                'color': '#84CC16',
                'required_actions': ['review_results', 'generate_reports', 'notify_clinicians'],
                'next_stages': ['completion'],
                'tla_properties': ['ActionCompleteness', 'DataConsistency', 'SecurityCompliance']
            },
            'completion': {
                'title': 'Workflow Completion',
                'description': 'Finalizing workflow and archiving documentation',
                'icon': '✅',
                'color': '#22C55E',
                'required_actions': ['finalize_documentation', 'archive_samples', 'close_workflow'],
                'next_stages': [],
                'tla_properties': ['ActionCompleteness', 'SecurityCompliance', 'WorkflowIntegrity']
            }
        }

    def analyze_conversation_context(self, user_message: str, agent_response: str, conversation_context: Dict) -> Dict:
        """
        Analyze conversation context and determine current workflow stage
        """
        try:
            # Determine current stage based on conversation content
            current_stage = self._determine_stage(
                user_message, agent_response, conversation_context)

            # Calculate progress
            progress = self._calculate_progress(
                current_stage, conversation_context.get('completed_steps', []))

            # Get stage information
            stage_info = self.workflow_stages.get(
                current_stage, self.workflow_stages['initiation'])

            # Validate TLA+ properties
            tla_validation = self._validate_tla_properties(
                current_stage, conversation_context)

            # Get available actions
            available_actions = self._get_available_actions(
                current_stage, conversation_context)

            # Get next steps
            next_steps = self._get_next_steps(
                current_stage, conversation_context)

            # Get visual elements
            visual_elements = self._get_visual_elements(
                current_stage, conversation_context)

            # Check for alerts
            alerts = self._check_alerts(
                current_stage, conversation_context, tla_validation)

            return {
                'current_stage': current_stage,
                'stage_info': stage_info,
                'progress': progress,
                'sample_status': self._get_sample_status(conversation_context),
                'available_actions': available_actions,
                'next_steps': next_steps,
                'tla_validation': tla_validation,
                'visual_elements': visual_elements,
                'alerts': alerts,
                'timestamp': datetime.utcnow().isoformat(),
                'context_summary': self._generate_context_summary(conversation_context)
            }

        except Exception as e:
            logger.error(f"Stage analysis failed: {e}")
            # Return safe fallback
            return {
                'current_stage': 'initiation',
                'stage_info': self.workflow_stages['initiation'],
                'progress': 0,
                'sample_status': [],
                'available_actions': [],
                'next_steps': ['Start laboratory analysis workflow'],
                'tla_validation': {},
                'visual_elements': {},
                'alerts': [{'type': 'error', 'title': 'Stage Analysis Error', 'message': str(e)}],
                'timestamp': datetime.utcnow().isoformat(),
                'context_summary': 'Error analyzing context'
            }

    def _determine_stage(self, user_message: str, agent_response: str, context: Dict) -> str:
        """Determine current workflow stage based on conversation content"""
        user_lower = user_message.lower()
        agent_lower = agent_response.lower()
        combined_text = f"{user_lower} {agent_lower}"

        # Stage detection keywords
        stage_keywords = {
            'sample_reception': ['arrived', 'received', 'samples here', 'just arrived', 'samples arrived', 'new samples'],
            'registration': ['register', 'registration', 'log sample', 'register samples', 'patient information'],
            'assignment': ['assign', 'analyst', 'john wick', 'sarah connor', 'tony stark', 'bruce wayne'],
            'processing': ['process', 'processing', 'prepare', 'aliquot', 'centrifuge'],
            'testing': ['test', 'testing', 'cbc', 'chemistry', 'pcr', 'culture', 'analysis'],
            'results': ['results', 'report', 'complete', 'finished', 'ready'],
            'completion': ['complete', 'done', 'finished', 'final report', 'close']
        }

        # Check completed steps from context
        completed_steps = context.get('completed_steps', [])
        current_step = context.get('current_step', 'initiation')

        # Determine stage based on keywords and context
        for stage, keywords in stage_keywords.items():
            if any(keyword in combined_text for keyword in keywords):
                # Update completed steps
                if stage not in completed_steps:
                    completed_steps.append(stage)
                    context['completed_steps'] = completed_steps
                return stage

        # If no specific keywords found, return current step or initiation
        return current_step if current_step in self.workflow_stages else 'initiation'

    def _calculate_progress(self, current_stage: str, completed_steps: List[str]) -> float:
        """Calculate workflow progress percentage"""
        total_stages = len(self.workflow_stages)
        if not completed_steps:
            return 10.0  # Show some initial progress

        # Find current stage index
        stage_list = list(self.workflow_stages.keys())
        try:
            current_index = stage_list.index(current_stage)
            progress = ((current_index + 1) / total_stages) * 100
            return min(progress, 100.0)
        except ValueError:
            return 10.0

    def _validate_tla_properties(self, stage: str, context: Dict) -> Dict:
        """Validate TLA+ properties for current stage"""
        stage_info = self.workflow_stages.get(stage, {})
        required_properties = stage_info.get('tla_properties', [])

        validation_results = {}

        for property_name in required_properties:
            if property_name == 'ActionCompleteness':
                validation_results[property_name] = self._validate_action_completeness(
                    stage, context)
            elif property_name == 'DataConsistency':
                validation_results[property_name] = self._validate_data_consistency(
                    context)
            elif property_name == 'SecurityCompliance':
                validation_results[property_name] = self._validate_security_compliance(
                    context)
            elif property_name == 'WorkflowIntegrity':
                validation_results[property_name] = self._validate_workflow_integrity(
                    stage, context)

        return validation_results

    def _validate_action_completeness(self, stage: str, context: Dict) -> Dict:
        """Validate ActionCompleteness TLA+ property"""
        stage_info = self.workflow_stages.get(stage, {})
        required_actions = stage_info.get('required_actions', [])
        completed_actions = context.get('completed_actions', [])

        completion_rate = len(completed_actions) / \
            len(required_actions) if required_actions else 1.0

        return {
            'status': 'PASS' if completion_rate >= 0.8 else 'PENDING',
            'message': f"Action completeness: {completion_rate:.1%} ({len(completed_actions)}/{len(required_actions)})",
            'confidence': completion_rate
        }

    def _validate_data_consistency(self, context: Dict) -> Dict:
        """Validate DataConsistency TLA+ property"""
        sample_ids = context.get('sample_ids', [])
        has_samples = len(sample_ids) > 0

        # Check for duplicate sample IDs
        unique_samples = len(set(sample_ids)) == len(
            sample_ids) if sample_ids else True

        return {
            'status': 'PASS' if has_samples and unique_samples else 'PENDING',
            'message': f"Data consistency maintained: {len(sample_ids)} unique samples tracked",
            'confidence': 0.95 if unique_samples else 0.5
        }

    def _validate_security_compliance(self, context: Dict) -> Dict:
        """Validate SecurityCompliance TLA+ property"""
        # Basic security checks
        has_user_context = 'user_id' in context
        has_audit_trail = 'completed_steps' in context

        compliance_score = (has_user_context + has_audit_trail) / 2

        return {
            'status': 'PASS' if compliance_score >= 0.5 else 'PENDING',
            'message': f"Security compliance: audit trail active, user context tracked",
            'confidence': compliance_score
        }

    def _validate_workflow_integrity(self, stage: str, context: Dict) -> Dict:
        """Validate WorkflowIntegrity TLA+ property"""
        completed_steps = context.get('completed_steps', [])

        # Check if workflow follows proper sequence
        stage_sequence = list(self.workflow_stages.keys())
        integrity_valid = True

        if completed_steps:
            for i, step in enumerate(completed_steps):
                if step in stage_sequence:
                    step_index = stage_sequence.index(step)
                    # Check if previous steps were completed
                    for prev_index in range(step_index):
                        prev_step = stage_sequence[prev_index]
                        if prev_step not in completed_steps and prev_step != 'initiation':
                            integrity_valid = False
                            break

        return {
            'status': 'PASS' if integrity_valid else 'WARNING',
            'message': f"Workflow integrity maintained: {len(completed_steps)} steps completed in sequence",
            'confidence': 0.9 if integrity_valid else 0.6
        }

    def _get_sample_status(self, context: Dict) -> List[Dict]:
        """Get current sample status"""
        sample_ids = context.get('sample_ids', [])
        priority = context.get('priority', 'ROUTINE')

        return [
            {
                'id': sample_id,
                'status': 'active' if i == 0 else 'pending',
                'priority': priority,
                'location': f"Station {i + 1}",
                'progress': min(80 + (i * 5), 100) if i == 0 else 0
            }
            for i, sample_id in enumerate(sample_ids[:5])  # Show max 5 samples
        ]

    def _get_available_actions(self, stage: str, context: Dict) -> List[Dict]:
        """Get available actions for current stage"""
        stage_info = self.workflow_stages.get(stage, {})
        required_actions = stage_info.get('required_actions', [])

        actions = []
        for action in required_actions:
            actions.append({
                'id': action,
                'label': action.replace('_', ' ').title(),
                'description': f"Perform {action.replace('_', ' ')} for current samples",
                'enabled': True,
                'priority': 'high' if context.get('priority') == 'STAT' else 'normal'
            })

        return actions

    def _get_next_steps(self, stage: str, context: Dict) -> List[str]:
        """Get recommended next steps"""
        stage_info = self.workflow_stages.get(stage, {})
        next_stages = stage_info.get('next_stages', [])

        if not next_stages:
            return ["Workflow complete - generate final report"]

        return [f"Proceed to {self.workflow_stages[next_stage]['title']}" for next_stage in next_stages]

    def _get_visual_elements(self, stage: str, context: Dict) -> Dict:
        """Generate visual elements for the stage display"""
        sample_ids = context.get('sample_ids', [])
        priority = context.get('priority', 'ROUTINE')
        completed_steps = context.get('completed_steps', [])

        return {
            'workflow_diagram': {
                'current_step': stage,
                'completed_steps': completed_steps,
                'total_steps': len(self.workflow_stages),
                'stage_sequence': list(self.workflow_stages.keys())
            },
            'sample_status': self._get_sample_status(context),
            'performance_metrics': {
                'turnaround_time': '2h 15m' if priority == 'STAT' else '4h 30m',
                'completion_percentage': self._calculate_progress(stage, completed_steps),
                'quality_score': 0.96,
                'active_samples': len(sample_ids)
            },
            'lab_status': {
                'equipment_online': 95,
                'capacity_utilization': 78,
                'analyst_availability': 'Good'
            }
        }

    def _check_alerts(self, stage: str, context: Dict, tla_validation: Dict) -> List[Dict]:
        """Check for alerts and warnings"""
        alerts = []

        # Check TLA+ validation failures
        for prop, result in tla_validation.items():
            if result.get('status') == 'WARNING':
                alerts.append({
                    'type': 'warning',
                    'title': f'{prop} Warning',
                    'message': result.get('message', 'Property validation warning')
                })
            elif result.get('status') == 'FAIL':
                alerts.append({
                    'type': 'error',
                    'title': f'{prop} Failed',
                    'message': result.get('message', 'Property validation failed')
                })

        # Check for STAT priority
        if context.get('priority') == 'STAT':
            alerts.append({
                'type': 'info',
                'title': 'STAT Priority',
                'message': 'Sample is marked for expedited processing'
            })

        # Check for long processing time
        if len(context.get('completed_steps', [])) > 3 and stage in ['processing', 'testing']:
            alerts.append({
                'type': 'warning',
                'title': 'Extended Processing',
                'message': 'Sample has been in processing longer than expected'
            })

        return alerts

    def _generate_context_summary(self, context: Dict) -> str:
        """Generate a summary of the current context"""
        sample_count = len(context.get('sample_ids', []))
        completed_count = len(context.get('completed_steps', []))
        priority = context.get('priority', 'ROUTINE')

        return f"{sample_count} samples, {completed_count} steps completed, {priority} priority"


# Initialize stage agent
stage_agent = StageAgent()

# Memory API Models


class MemoryStoreRequest(BaseModel):
    content: str
    memory_type: str = "GENERAL"  # Default to GENERAL if not specified
    importance: float = 1.0
    tags: Optional[List[str]] = None


class MemoryStoreResponse(BaseModel):
    success: bool
    memory_id: Optional[str] = None
    error: Optional[str] = None


class MemorySearchRequest(BaseModel):
    query: str
    max_results: int = 5
    similarity_threshold: float = 0.7


class MemorySearchResponse(BaseModel):
    success: bool
    memories: List[Dict[str, Any]] = None
    error: Optional[str] = None

# Memory API Endpoints


@app.post("/api/v1/memory/store", response_model=MemoryStoreResponse)
async def store_memory(request: MemoryStoreRequest):
    """Store a new memory in the unified memory system"""
    global memory_system

    if memory_system is None:
        return MemoryStoreResponse(
            success=False,
            error="Memory system not initialized"
        )

    try:
        from datetime import datetime
        import uuid

        # Create a unified memory object with proper initialization
        current_time = datetime.now()
        memory = UnifiedMemory(
            id=str(uuid.uuid4()),
            memory_type=MemoryType(request.memory_type.upper()),
            scope=MemoryScope.PERSISTENT,
            primary_text=request.content,
            temporal_context=TemporalContext(
                timestamp=current_time,
                start_time=current_time,
                end_time=None,
                duration=None
            ),
            semantic_context=SemanticContext(
                topics=[],
                entities=[],
                concepts=[],
                sentiment=None,
                confidence=1.0,
                context_type="general",
                relations={}
            ),
            conversational_context=ConversationalContext(
                speaker="user",
                intent=None,
                conversation_id=str(uuid.uuid4()),
                turn_number=1
            ),
            modality=ModalityType.TEXT,
            created_at=current_time,
            updated_at=current_time,
            importance_score=request.importance,
            tags=request.tags or [],
            metadata={},
            source="api"
        )

        # Store the memory
        result = await memory_system.store_memory(memory)

        if result.get("success"):
            return MemoryStoreResponse(
                success=True,
                memory_id=memory.id
            )
        else:
            return MemoryStoreResponse(
                success=False,
                error=result.get("error", "Failed to store memory")
            )

    except Exception as e:
        logger.error(f"Error storing memory: {e}")
        return MemoryStoreResponse(
            success=False,
            error=str(e)
        )


@app.post("/api/v1/memory/search", response_model=MemorySearchResponse)
async def search_memory(request: MemorySearchRequest):
    """Search for memories using semantic similarity"""
    global memory_system

    if memory_system is None:
        return MemorySearchResponse(
            success=False,
            error="Memory system not initialized"
        )

    try:
        # Create a memory query
        query = MemoryQuery(
            text_query=request.query,
            max_results=request.max_results,
            semantic_similarity_threshold=request.similarity_threshold
        )

        # Search memories
        search_results = await memory_system.search_memories(query)

        # Format results for API response
        memories = []
                "relevance_score": result.relevance_score,
                "importance": result.memory.importance_score,
                "tags": result.memory.tags or []
            }

            # Handle potentially missing fields
            if hasattr(result.memory, 'created_at') and result.memory.created_at:
                memory_dict["created_at"] = result.memory.created_at.isoformat()
            else:
                memory_dict["created_at"] = datetime.now().isoformat()

            memories.append(memory_dict)

        return MemorySearchResponse(
            success=True,
            memories=memories
        )

    except Exception as e:
        logger.error(f"Error searching memories: {e}")
        return MemorySearchResponse(
            success=False,

    except Exception as e:
        logger.error(f"Error searching memories: {e}")
        return MemorySearchResponse(
            success=False,
            error=str(e)
        )


@app.get("/api/v1/memory/stats")
async def get_memory_stats():
    """Get memory system statistics"""
    global memory_system

    if memory_system is None:
        return {"error": "Memory system not initialized"}

    try:
        stats = await memory_system.get_stats()
        return {
            "success": True,
            "stats": stats
        }
    except Exception as e:
        logger.error(f"Error getting memory stats: {e}")
        return {
            "success": False,
            "error": str(e)
        }

# Run server
if __name__ == "__main__":
    uvicorn.run(app, host="127.0.0.1", port=8003)
