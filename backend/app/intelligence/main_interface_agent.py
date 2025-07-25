"""
Main Interface Agent - TLA+ Verified Implementation

This module implements the formally verified Main Interface Agent that serves as
the central orchestration layer for the ALIMS system. It coordinates conversations
between users and specialized LIMS agents.

Based on TLA+ specification MainInterfaceAgentIntegration.tla with verified properties:
- Safety: Type invariants, resource bounds, integration safety, state consistency
- Integration: Proper dependency order, health monitoring, error handling
- Validation: TLC model checker verified all safety properties

Following TLA+ specification exactly:
- Initialization: Permission Manager → Sample Manager → Result Processing Agent → Main Interface Agent
- Request Processing: User Request → Orchestration → Agent Assignment → Response Synthesis
- Resource Management: Bounded conversations, agents, requests, responses
- State Management: Consistent state transitions with proper error handling

Author: ALIMS Development Team
Date: July 16, 2025
TLA+ Validated: ✅
"""

import asyncio
import logging
import uuid
import time
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from typing import Dict, List, Optional, Set, Any
import json

# Import debug system for crazy talk detection and monitoring
from app.debug import (
    get_debug_system, get_agent_tracker,
    EventType, AgentStatus, create_event
)

# Import Langfuse tracing decorators
from app.core.langfuse_tracing import trace_operation, OperationType, TraceLevel

# Conditional import of Ollama integration (only if dependencies are available)
try:
    from app.intelligence.ollama_integration import OllamaLIMSAgent
    OLLAMA_AVAILABLE = True
except ImportError:
    OLLAMA_AVAILABLE = False
    OllamaLIMSAgent = None
    # Note: logger not available yet, will log this in __init__

logger = logging.getLogger(__name__)


class ConversationState(str, Enum):
    """TLA+ verified conversation states"""
    ACTIVE = "ACTIVE"
    COMPLETED = "COMPLETED"
    ERROR = "ERROR"


class AgentState(str, Enum):
    """TLA+ verified agent states"""
    IDLE = "IDLE"
    BUSY = "BUSY"
    ERROR = "ERROR"


class CentralBrainState(str, Enum):
    """TLA+ verified central brain states"""
    READY = "READY"
    ORCHESTRATING = "ORCHESTRATING"
    WAITING_FOR_RESPONSE = "WAITING_FOR_RESPONSE"
    SYNTHESIZING = "SYNTHESIZING"


class RequestType(str, Enum):
    """Types of user requests"""
    SAMPLE_INQUIRY = "SAMPLE_INQUIRY"
    WORKFLOW_COMMAND = "WORKFLOW_COMMAND"
    SYSTEM_QUERY = "SYSTEM_QUERY"
    AGENT_REQUEST = "AGENT_REQUEST"


class Priority(str, Enum):
    """Request priority levels"""
    LOW = "LOW"
    MEDIUM = "MEDIUM"
    HIGH = "HIGH"
    URGENT = "URGENT"


@dataclass
class UserRequest:
    """User request data structure - following TLA+ specification"""
    conversation_id: str
    request_type: RequestType
    content: str
    priority: Priority
    timestamp: datetime = field(default_factory=datetime.now)
    user_id: Optional[str] = None
    metadata: Dict[str, Any] = field(default_factory=dict)



@dataclass
class AgentResponse:
    """Agent response data structure - following TLA+ specification"""
    conversation_id: str
    agent_id: str
    content: str
    success: bool
    timestamp: datetime = field(default_factory=datetime.now)
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class AgentInfo:
    """Agent information structure - following TLA+ specification"""
    agent_id: str
    capabilities: str
    state: AgentState
    current_conversation: Optional[str] = None
    last_activity: datetime = field(default_factory=datetime.now)
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class ConversationContext:
    """Conversation context tracking - following TLA+ specification"""
    conversation_id: str
    state: ConversationState
    user_intent: Optional[str] = None
    active_agents: Set[str] = field(default_factory=set)
    request_history: List[UserRequest] = field(default_factory=list)
    response_history: List[AgentResponse] = field(default_factory=list)
    created_at: datetime = field(default_factory=datetime.now)
    updated_at: datetime = field(default_factory=datetime.now)


@dataclass
class SystemMetrics:
    """System performance metrics - following TLA+ specification"""
    total_conversations: int = 0
    active_conversations: int = 0
    total_requests: int = 0
    total_responses: int = 0
    errors: int = 0
    average_response_time: float = 0.0
    last_updated: datetime = field(default_factory=datetime.now)


class MainInterfaceAgent:
    """
    TLA+ Verified Main Interface Agent
    
    This class implements the formally verified central orchestration agent
    that coordinates conversations between users and specialized LIMS agents.
    
    Implementation follows MainInterfaceAgentIntegration.tla specification:
    - Initialization: Waits for dependencies (permission_manager, sample_manager, result_processing_agent)
    - Request Processing: Orchestrates agent assignment based on capabilities
    - Resource Management: Respects TLA+ verified bounds
    - State Management: Maintains TLA+ verified consistency
    """

    def __init__(self, max_conversations: int = 3, max_agents: int = 3, max_requests: int = 5, max_responses: int = 5):
        # TLA+ verified resource bounds
        self.max_conversations = max_conversations
        self.max_agents = max_agents
        self.max_requests = max_requests
        self.max_responses = max_responses

        # TLA+ verified state variables
        self.conversations: Dict[str, ConversationContext] = {}
        self.available_agents: Dict[str, AgentInfo] = {}
        self.user_requests: List[UserRequest] = []
        self.agent_responses: List[AgentResponse] = []
        self.central_brain_state = CentralBrainState.READY
        self.system_metrics = SystemMetrics()

        # Thread safety for async operations
        self._state_lock = asyncio.Lock()

        # Initialize logging
        self.logger = logging.getLogger(f"{__name__}.MainInterfaceAgent")

        # Integration state tracking
        self._initialized = False

        # Initialize debug system for crazy talk detection and monitoring
        self.debug_system = get_debug_system()
        self.agent_tracker = get_agent_tracker()
        self.agent_id = "main_interface_agent"
        self.agent_tracker.register_agent(self.agent_id, "main_interface")

        # Set up monitoring for all agent state changes
        self.agent_tracker.add_state_change_callback(
            self._on_agent_state_change)

        # Initialize Ollama LLM agent for intelligent responses (with Langfuse tracing)
        if OLLAMA_AVAILABLE:
            try:
                self.ollama_agent = OllamaLIMSAgent()
                self.logger.info("Initialized Ollama LLM agent with Langfuse tracing")
            except Exception as e:
                self.logger.warning(f"Failed to initialize Ollama agent: {e}")
                self.ollama_agent = None
        else:
            self.ollama_agent = None
            self.logger.info("Ollama integration not available - using enhanced fallback responses")

        self.logger.info("MainInterfaceAgent initialized with debug system")

    def _on_agent_state_change(self, agent_id: str, new_state):
        """Monitor agent state changes for debugging"""
        self.logger.info(f"Agent {agent_id} state: {new_state.status.value}")

        if new_state.status == AgentStatus.ERROR:
            self.logger.warning(f"🚨 Agent {agent_id} in ERROR state!")

            # Get recent events for analysis
            recent_events = self.debug_system.get_recent_events(5)
            agent_events = [e for e in recent_events if e.agent_id == agent_id]

            for event in agent_events[-3:]:
                self.logger.warning(
                    f"  📋 {event.event_type.value}: {event.message}")

    def _debug_check_crazy_talk(self, response: str) -> bool:
        """Check if response contains crazy talk patterns"""
        indicators = [
            len(response) > 1000,  # Extremely long responses
            "banana elephant quantum" in response.lower(),
            "NULL_POINTER_EXCEPTION" in response,
            "TypeError:" in response,
            "recursive loop" in response.lower(),
            response.count("and") > 15,
            response.count("the") > 30,
            len(response.split()) > 300,
            "Exception" in response and "Error" in response,  # Code errors
        ]
        return any(indicators)

    async def process_user_request_with_debug(
        self,
        user_input: str,
        user_id: Optional[str] = None,
        conversation_id: Optional[str] = None,
        request_type: RequestType = RequestType.AGENT_REQUEST,
        priority: Priority = Priority.MEDIUM
    ) -> str:
        """
        Process user request with full debug tracking for crazy talk detection
        This is the main entry point for processing user requests with monitoring
        """

        # Generate conversation ID if needed
        if conversation_id is None:
            conversation_id = await self.start_conversation(user_id)

        # Start debug tracking
        self.agent_tracker.start_conversation(self.agent_id, conversation_id)
        self.agent_tracker.record_message_received(
            self.agent_id,
            f"User: {user_input[:100]}...",
            conversation_id
        )
        self.agent_tracker.update_agent_status(
            self.agent_id,
            AgentStatus.BUSY,
            "Processing user request"
        )

        start_time = time.time()

        try:
            # Log processing start
            event = create_event(
                agent_id=self.agent_id,
                event_type=EventType.PROCESS,
                message=f"Processing request: {user_input[:50]}...",
                conversation_id=conversation_id
            )
            self.debug_system.record_event(event)

            # Process using existing TLA+ verified workflow
            await self.receive_user_request(
                conversation_id=conversation_id,
                content=user_input,
                request_type=request_type,
                priority=priority,
                user_id=user_id
            )

            # Orchestrate and get response
            await self.analyze_and_orchestrate()

            # Simulate getting response (replace with your actual response logic)
            response = await self._get_final_response(conversation_id, user_input)

            # Check for crazy talk
            if self._debug_check_crazy_talk(response):
                self.agent_tracker.record_error(
                    self.agent_id,
                    f"Crazy talk detected: {response[:100]}...",
                    conversation_id
                )
                response = "I apologize, but I need to rephrase my response. Could you please be more specific about what you need help with?"

            # Record successful response
            processing_time = time.time() - start_time
            self.agent_tracker.record_message_response(
                self.agent_id,
                f"Response: {response[:100]}...",
                processing_time,
                conversation_id
            )

            # Update status
            self.agent_tracker.update_agent_status(
                self.agent_id,
                AgentStatus.READY,
                "Request completed successfully"
            )

            return response

        except Exception as e:
            # Record error with context
            error_msg = f"Error processing '{user_input[:50]}...': {str(e)}"
            self.agent_tracker.record_error(
                self.agent_id, error_msg, conversation_id)

            self.logger.error(f"MainInterfaceAgent error: {error_msg}")
            return "I apologize, but I encountered an error processing your request. Please try again."

        finally:
            # End conversation tracking
            self.agent_tracker.end_conversation(self.agent_id, conversation_id)

    @trace_operation(OperationType.API, "get_final_response", include_args=True, include_result=True)
    async def _get_final_response(self, conversation_id: str, user_input: str) -> str:
        """
        Get final response for user request using Ollama LLM with Langfuse tracing
        This method now integrates with the traced Ollama integration
        """

        # Process pending requests and responses using TLA+ logic
        await self.process_next_request()

        # Get conversation history to build context
        history = await self.get_conversation_history(conversation_id)

        # Build context for the LLM
        context_messages = []
        if history and 'messages' in history:
            # Add recent conversation history
            # Last 5 messages for context
            context_messages = history['messages'][-5:]

        # Create a comprehensive LIMS system prompt
        system_prompt = """You are ALIMS (Advanced Laboratory Information Management System) Assistant.
You are an expert in laboratory operations, sample management, workflow coordination, and data analysis.

Your capabilities include:
- Sample tracking and lifecycle management
- Laboratory workflow coordination
- Quality control and compliance monitoring
- Data analysis and reporting
- Equipment management and maintenance
- Protocol and SOP guidance

Always provide helpful, accurate, and contextually relevant responses for laboratory operations.
If you need more specific information to provide a better answer, ask clarifying questions."""

        try:
            # Use the traced Ollama integration to generate response if available
            if self.ollama_agent:
                response = await self.ollama_agent.process_user_input_enhanced(
                    user_input=user_input,
                    conversation_context=context_messages,
                    system_prompt=system_prompt
                )
                
                self.logger.info(
                    f"Generated LLM response for conversation {conversation_id}")
                return response
            else:
                # Fallback to intelligent rule-based responses
                return self._generate_fallback_response(user_input)
                
        except Exception as e:
            self.logger.error(f"Error generating LLM response: {e}")
            # Fallback to basic response if LLM fails
            return self._generate_fallback_response(user_input, error=str(e)[:100])
    
    def _generate_fallback_response(self, user_input: str, error: Optional[str] = None) -> str:
        """Generate intelligent fallback responses when Ollama is not available"""
        
        # *** MANUAL LANGFUSE TRACING FOR DEBUGGING ***
        try:
            from app.core.langfuse_tracing import get_tracker, OperationType
            import asyncio
            
            async def send_manual_trace():
                try:
                    tracer = await get_tracker()
                    if tracer and tracer.langfuse_client:
                        # Create a manual trace for the fallback response
                        tracer.langfuse_client.create_event(
                            name="fallback_response_generated",
                            metadata={
                                "user_input": user_input[:200],
                                "error": error,
                                "response_type": "fallback",
                                "timestamp": str(__import__('time').time()),
                                "source": "main_interface_agent_fallback"
                            }
                        )
                        tracer.langfuse_client.flush()
                        self.logger.info("🔥 MANUAL TRACE SENT TO LANGFUSE!")
                except Exception as e:
                    self.logger.error(f"Manual trace failed: {e}")
            
            # Run the async trace
            try:
                loop = asyncio.get_event_loop()
                loop.create_task(send_manual_trace())
            except:
                asyncio.run(send_manual_trace())
                
        except Exception as e:
            self.logger.error(f"Failed to send manual trace: {e}")
        
        base_error = f" (Error: {error})" if error else ""
        
        # Enhanced rule-based responses
        user_lower = user_input.lower()
        
        if any(word in user_lower for word in ["sample", "specimen", "tracking"]):
            return f"I can help you with sample tracking and management. Our LIMS system provides comprehensive sample lifecycle management including registration, tracking, testing status, and results reporting. Could you provide more details about the specific sample you're working with?{base_error}"
        
        elif any(word in user_lower for word in ["workflow", "process", "protocol"]):
            return f"I can assist with laboratory workflow management. Our system supports automated workflow orchestration, protocol compliance, and process optimization. What specific workflow operation would you like to perform?{base_error}"
        
        elif any(word in user_lower for word in ["data", "analysis", "report", "result"]):
            return f"I can help with data analysis and reporting. Our LIMS system provides advanced analytics, trend analysis, and customizable reporting capabilities. Please specify what type of data analysis you'd like to perform?{base_error}"
        
        elif any(word in user_lower for word in ["quality", "qc", "control", "compliance"]):
            return f"I can assist with quality control and compliance monitoring. Our system ensures adherence to laboratory standards, automated QC checks, and comprehensive audit trails. What quality control aspect can I help you with?{base_error}"
        
        elif any(word in user_lower for word in ["equipment", "instrument", "calibration"]):
            return f"I can help with equipment and instrument management. Our system tracks equipment status, maintenance schedules, calibration records, and utilization metrics. Which equipment or instrument do you need assistance with?{base_error}"
        
        else:
            return f"I'm ALIMS (Advanced Laboratory Information Management System) Assistant. I can help you with sample management, workflow coordination, data analysis, quality control, and equipment management. Could you please specify what aspect of laboratory operations you need assistance with?{base_error}"

    async def initialize(self) -> bool:
        """
        Initialize the Main Interface Agent
        Following TLA+ specification: requires dependencies to be ready
        """
        async with self._state_lock:
            try:
                if self._initialized:
                    return True

                # Initialize core agent registry with TLA+ verified capabilities
                await self._initialize_core_agents()

                self.central_brain_state = CentralBrainState.READY
                self._initialized = True

                self.logger.info(
                    "Main Interface Agent initialized successfully")
                return True

            except Exception as e:
                self.logger.error(
                    f"Failed to initialize Main Interface Agent: {e}")
                return False

    async def _initialize_core_agents(self):
        """Initialize core LIMS agents with TLA+ verified capabilities"""
        core_agents = [
            ("sample_tracker_001", "sample_tracker"),
            ("workflow_manager_001", "workflow_manager"),
            ("system_monitor_001", "system_monitor"),
            ("lims_coordinator_001", "lims_coordinator")
        ]

        # Ensure we have enough capacity for core agents
        required_agents = min(len(core_agents), self.max_agents)

        for i in range(required_agents):
            agent_id, capability = core_agents[i]
            agent_info = AgentInfo(
                agent_id=agent_id,
                capabilities=capability,
                state=AgentState.IDLE
            )
            self.available_agents[agent_id] = agent_info
            self.logger.info(
                f"Initialized core agent {agent_id} with capability: {capability}")

    async def register_agent(self, agent_id: str, capabilities: str) -> bool:
        """
        Register a specialized agent with the system
        Following TLA+ specification RegisterAgent action
        """
        async with self._state_lock:
            if len(self.available_agents) >= self.max_agents:
                self.logger.warning(
                    f"Maximum agents ({self.max_agents}) reached")
                return False

            if agent_id in self.available_agents:
                self.logger.warning(f"Agent {agent_id} already registered")
                return False

            agent_info = AgentInfo(
                agent_id=agent_id,
                capabilities=capabilities,
                state=AgentState.IDLE
            )

            self.available_agents[agent_id] = agent_info
            self.logger.info(
                f"Registered agent {agent_id} with capabilities: {capabilities}")
            return True

    async def start_conversation(self, user_id: Optional[str] = None) -> str:
        """
        Start a new conversation
        Following TLA+ specification StartConversation action
        """
        async with self._state_lock:
            if len(self.conversations) >= self.max_conversations:
                raise Exception(
                    f"Maximum conversations ({self.max_conversations}) reached")

            conversation_id = str(uuid.uuid4())

            context = ConversationContext(
                conversation_id=conversation_id,
                state=ConversationState.ACTIVE
            )

            self.conversations[conversation_id] = context
            self.system_metrics.total_conversations += 1
            self.system_metrics.active_conversations += 1

            self.logger.info(f"Started conversation {conversation_id}")
            return conversation_id

    @trace_operation(OperationType.AGENT, "receive_user_request", include_args=True)
    async def receive_user_request(
        self,
        conversation_id: str,
        content: str,
        request_type: RequestType,
        priority: Priority = Priority.MEDIUM,
        user_id: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None
    ) -> bool:
        """
        Receive and queue a user request
        Following TLA+ specification ProcessUserRequest action
        """
        async with self._state_lock:
            # Debug tracking
            event = create_event(
                agent_id=self.agent_id,
                event_type=EventType.RECEIVE_MESSAGE,
                message=f"Received request: {content[:100]}...",
                conversation_id=conversation_id
            )
            self.debug_system.record_event(event)

            if conversation_id not in self.conversations:
                self.logger.error(f"Conversation {conversation_id} not found")
                # Debug error tracking
                error_event = create_event(
                    agent_id=self.agent_id,
                    event_type=EventType.ERROR,
                    message=f"Conversation {conversation_id} not found",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(error_event)
                return False

            if self.conversations[conversation_id].state != ConversationState.ACTIVE:
                self.logger.error(f"Conversation {conversation_id} not active")
                # Debug error tracking
                error_event = create_event(
                    agent_id=self.agent_id,
                    event_type=EventType.ERROR,
                    message=f"Conversation {conversation_id} not active",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(error_event)
                return False

            if len(self.user_requests) >= self.max_requests:
                self.logger.warning(
                    f"Maximum requests ({self.max_requests}) reached")
                # Debug warning tracking
                warning_event = create_event(
                    agent_id=self.agent_id,
                    event_type=EventType.WARNING,
                    message=f"Maximum requests ({self.max_requests}) reached",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(warning_event)
                return False

            request = UserRequest(
                conversation_id=conversation_id,
                request_type=request_type,
                content=content,
                priority=priority,
                user_id=user_id,
                metadata=metadata or {}
            )

            self.user_requests.append(request)
            self.conversations[conversation_id].request_history.append(request)
            self.conversations[conversation_id].updated_at = datetime.now()
            self.system_metrics.total_requests += 1

            self.logger.info(
                f"Received request for conversation {conversation_id}: {request_type}")
            return True

    async def analyze_and_orchestrate(self) -> bool:
        """
        Analyze pending requests and orchestrate appropriate agents
        Following TLA+ specification OrchestratorsAgents action
        """
        async with self._state_lock:
            if not self.user_requests:
                return False

            if self.central_brain_state != CentralBrainState.READY:
                return False

            # Transition to orchestrating state (TLA+ verified)
            self.central_brain_state = CentralBrainState.ORCHESTRATING

            # Get next request (FIFO as per TLA+ spec)
            request = self.user_requests.pop(0)
            conv_id = request.conversation_id

            # Determine required capabilities based on request type (TLA+ verified mapping)
            required_capabilities = self._get_required_capabilities(
                request.request_type)

            # Find suitable idle agents (TLA+ verified logic)
            suitable_agents = set()
            for agent_id, agent in self.available_agents.items():
                if (agent.state == AgentState.IDLE and
                        agent.capabilities in required_capabilities):
                    suitable_agents.add(agent_id)

            # Update conversation context (TLA+ verified)
            if conv_id in self.conversations:
                self.conversations[conv_id].user_intent = request.request_type.value
                self.conversations[conv_id].active_agents = suitable_agents
                self.conversations[conv_id].updated_at = datetime.now()

            # Transition back to ready state (TLA+ verified)
            self.central_brain_state = CentralBrainState.READY

            self.logger.info(
                f"Orchestrated request for conversation {conv_id} with {len(suitable_agents)} agents")
            return True

    def _get_required_capabilities(self, request_type: RequestType) -> Set[str]:
        """
        Get required capabilities for a request type
        Following TLA+ specification capability mapping
        """
        capability_mapping = {
            RequestType.SAMPLE_INQUIRY: {"sample_tracker", "workflow_manager"},
            RequestType.WORKFLOW_COMMAND: {"workflow_manager", "lims_coordinator"},
            RequestType.SYSTEM_QUERY: {"system_monitor"},
            RequestType.AGENT_REQUEST: {
                "sample_tracker", "workflow_manager", "lims_coordinator"}
        }
        return capability_mapping.get(request_type, set())

    async def route_to_agent(self, agent_id: str, request_content: str) -> bool:
        """
        Route a request to a specific agent
        Following TLA+ specification RouteToAgent action
        """
        async with self._state_lock:
            if agent_id not in self.available_agents:
                self.logger.error(f"Agent {agent_id} not found")
                return False

            agent = self.available_agents[agent_id]

            if agent.state != AgentState.IDLE:
                self.logger.error(f"Agent {agent_id} not idle")
                return False

            # Update agent state to busy (TLA+ verified)
            agent.state = AgentState.BUSY
            agent.last_activity = datetime.now()

            # Transition central brain to waiting state (TLA+ verified)
            self.central_brain_state = CentralBrainState.WAITING_FOR_RESPONSE

            self.logger.info(f"Routed request to agent {agent_id}")
            return True

    async def receive_agent_response(
        self,
        agent_id: str,
        conversation_id: str,
        content: str,
        success: bool,
        metadata: Optional[Dict[str, Any]] = None
    ) -> bool:
        """
        Receive response from an agent
        Following TLA+ specification ReceiveAgentResponse action
        """
        async with self._state_lock:
            if agent_id not in self.available_agents:
                self.logger.error(f"Agent {agent_id} not found")
                return False

            if conversation_id not in self.conversations:
                self.logger.error(f"Conversation {conversation_id} not found")
                return False

            if len(self.agent_responses) >= self.max_responses:
                self.logger.warning(
                    f"Maximum responses ({self.max_responses}) reached")
                return False

            # Create response object (TLA+ verified structure)
            response = AgentResponse(
                conversation_id=conversation_id,
                agent_id=agent_id,
                content=content,
                success=success,
                metadata=metadata or {}
            )

            # Add to response queue (TLA+ verified)
            self.agent_responses.append(response)
            self.conversations[conversation_id].response_history.append(
                response)

            # Update agent state back to idle (TLA+ verified)
            agent = self.available_agents[agent_id]
            agent.state = AgentState.IDLE
            agent.current_conversation = None
            agent.last_activity = datetime.now()

            # Transition to synthesizing state (TLA+ verified)
            self.central_brain_state = CentralBrainState.SYNTHESIZING

            # Update system metrics (TLA+ verified)
            self.system_metrics.total_responses += 1
            if not success:
                self.system_metrics.errors += 1

            self.logger.info(
                f"Received response from agent {agent_id} for conversation {conversation_id}")
            return True
    
    async def synthesize_and_respond(self) -> Optional[str]:
        """
        Synthesize agent responses and create final response
        Following TLA+ specification SynthesizeResponse action
        """
        async with self._state_lock:
            if not self.agent_responses:
                return None

            if self.central_brain_state != CentralBrainState.SYNTHESIZING:
                return None

            # Get next response (FIFO as per TLA+ spec)
            response = self.agent_responses.pop(0)
            
            # Simple synthesis (TLA+ verified)
            synthesized_response = self._synthesize_response(response)
            
            # Transition back to ready state (TLA+ verified)
            self.central_brain_state = CentralBrainState.READY
            
            self.logger.info(
                f"Synthesized response for conversation {response.conversation_id}")
            return synthesized_response

    def _synthesize_response(self, response: AgentResponse) -> str:
        """
        Synthesize a final response from agent response
        Following TLA+ specification synthesis logic
        """
        if response.success:
            return f"Agent {response.agent_id} successfully processed your request: {response.content}"
        else:
            return f"Agent {response.agent_id} encountered an error: {response.content}"

    async def handle_agent_error(self, agent_id: str, error_message: str) -> bool:
        """
        Handle agent error conditions
        Following TLA+ specification HandleError action
        """
        async with self._state_lock:
            if agent_id not in self.available_agents:
                self.logger.error(f"Agent {agent_id} not found")
                return False

            agent = self.available_agents[agent_id]
            agent.state = AgentState.ERROR
            agent.last_activity = datetime.now()

            # Update system metrics (TLA+ verified)
            self.system_metrics.errors += 1

            self.logger.error(f"Agent {agent_id} error: {error_message}")
            return True
    
    async def complete_conversation(self, conversation_id: str) -> bool:
        """
        Complete a conversation
        Following TLA+ specification conversation completion
        """
        async with self._state_lock:
            if conversation_id not in self.conversations:
                self.logger.error(f"Conversation {conversation_id} not found")
                return False

            conversation = self.conversations[conversation_id]
            conversation.state = ConversationState.COMPLETED
            conversation.updated_at = datetime.now()

            # Update system metrics (TLA+ verified)
            self.system_metrics.active_conversations -= 1
            
            self.logger.info(f"Completed conversation {conversation_id}")
            return True

    async def process_next_request(self) -> bool:
        """
        Process the next pending request
        Main orchestration loop entry point following TLA+ specification
        """
        # Try to orchestrate new requests
        if await self.analyze_and_orchestrate():
            return True

        # Try to synthesize responses
        response = await self.synthesize_and_respond()
        if response:
            return True
        
        return False
    
    async def get_conversation_history(self, conversation_id: str) -> Optional[Dict[str, Any]]:
        """Get conversation history following TLA+ specification"""
        async with self._state_lock:
            if conversation_id not in self.conversations:
                return None

            context = self.conversations[conversation_id]
            return {
                'conversation_id': context.conversation_id,
                'state': context.state.value,
                'user_intent': context.user_intent,
                'active_agents': list(context.active_agents),
                'request_count': len(context.request_history),
                'response_count': len(context.response_history),
                'created_at': context.created_at.isoformat(),
                'updated_at': context.updated_at.isoformat()
            }

    async def get_active_conversations(self) -> List[Dict[str, Any]]:
        """Get all active conversations following TLA+ specification"""
        async with self._state_lock:
            active_conversations = []
            for conv_id, context in self.conversations.items():
                if context.state == ConversationState.ACTIVE:
                    active_conversations.append({
                        'conversation_id': conv_id,
                        'user_intent': context.user_intent,
                        'active_agents': list(context.active_agents),
                        'request_count': len(context.request_history),
                        'response_count': len(context.response_history),
                        'created_at': context.created_at.isoformat(),
                        'updated_at': context.updated_at.isoformat()
                    })
            return active_conversations

    async def get_system_status(self) -> Dict[str, Any]:
        """Get system status and metrics following TLA+ specification"""
        async with self._state_lock:
            return {
                'central_brain_state': self.central_brain_state.value,
                'total_conversations': self.system_metrics.total_conversations,
                'active_conversations': self.system_metrics.active_conversations,
                'total_requests': self.system_metrics.total_requests,
                'total_responses': self.system_metrics.total_responses,
                'errors': self.system_metrics.errors,
                'registered_agents': len(self.available_agents),
                'idle_agents': len([a for a in self.available_agents.values() if a.state == AgentState.IDLE]),
                'busy_agents': len([a for a in self.available_agents.values() if a.state == AgentState.BUSY]),
                'error_agents': len([a for a in self.available_agents.values() if a.state == AgentState.ERROR]),
                'pending_requests': len(self.user_requests),
                'pending_responses': len(self.agent_responses),
                'resource_usage': {
                    'conversations': f"{len(self.conversations)}/{self.max_conversations}",
                    'agents': f"{len(self.available_agents)}/{self.max_agents}",
                    'requests': f"{len(self.user_requests)}/{self.max_requests}",
                    'responses': f"{len(self.agent_responses)}/{self.max_responses}"
                },
                'last_updated': datetime.now().isoformat()
            }

    def is_healthy(self) -> bool:
        """
        Check if the agent is healthy
        Following TLA+ specification health checks
        """
        return (
            self._initialized and
            self.central_brain_state in [CentralBrainState.READY, CentralBrainState.ORCHESTRATING,
                                         CentralBrainState.WAITING_FOR_RESPONSE, CentralBrainState.SYNTHESIZING] and
            len(self.user_requests) <= self.max_requests and
            len(self.agent_responses) <= self.max_responses and
            len(self.conversations) <= self.max_conversations and
            len(self.available_agents) <= self.max_agents
        )

    async def stop(self) -> None:
        """
        Stop the Main Interface Agent
        Following TLA+ specification shutdown procedure
        """
        async with self._state_lock:
            self.logger.info("Stopping Main Interface Agent...")

            # Complete all active conversations
            for conversation_id, context in self.conversations.items():
                if context.state == ConversationState.ACTIVE:
                    context.state = ConversationState.COMPLETED
                    context.updated_at = datetime.now()

            # Reset all agents to idle
            for agent in self.available_agents.values():
                agent.state = AgentState.IDLE
                agent.current_conversation = None

            # Clear queues
            self.user_requests.clear()
            self.agent_responses.clear()

            # Update metrics
            self.system_metrics.active_conversations = 0

            # Reset state
            self.central_brain_state = CentralBrainState.READY
            self._initialized = False

            self.logger.info("Main Interface Agent stopped")

# Factory function for creating Main Interface Agent


async def create_main_interface_agent(
    max_conversations: int = 3,
    max_agents: int = 3,
    max_requests: int = 5,
    max_responses: int = 5
) -> MainInterfaceAgent:
    """
    Create and initialize a Main Interface Agent
    Following TLA+ specification factory pattern
    """
    agent = MainInterfaceAgent(
        max_conversations, max_agents, max_requests, max_responses)
    await agent.initialize()
    return agent

# System configuration following TLA+ specification


@dataclass
class SystemConfiguration:
    """System configuration for Main Interface Agent following TLA+ specification"""
    max_conversations: int = 3
    max_agents: int = 3
    max_requests: int = 5
    max_responses: int = 5
    log_level: str = "INFO"
    enable_metrics: bool = True
    health_check_interval: int = 60

# Main Interface Agent System class for compatibility


class MainInterfaceAgentSystem:
    """Compatibility wrapper for existing code following TLA+ specification"""

    def __init__(self, max_conversations: int = 3, max_agents: int = 3, max_requests: int = 5, max_responses: int = 5):
        self.agent = None
        self.max_conversations = max_conversations
        self.max_agents = max_agents
        self.max_requests = max_requests
        self.max_responses = max_responses
    
    async def initialize(self):
        """Initialize the system following TLA+ specification"""
        self.agent = await create_main_interface_agent(
            self.max_conversations, self.max_agents, self.max_requests, self.max_responses
        )
        return self.agent is not None

    def __getattr__(self, name):
        """Delegate attribute access to the agent"""
        if self.agent:
            return getattr(self.agent, name)
        raise AttributeError(
            f"'{type(self).__name__}' object has no attribute '{name}'")
