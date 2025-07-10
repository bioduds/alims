"""
Main Interface Agent - Primary conversational interface for ALIMS system.

This implementation is based on a formally validated TLA+ specification that was
verified with the TLC model checker across 22+ million states.

The Main Interface Agent serves as the central brain that:
1. Manages user conversations 
2. Orchestrates specialized LIMS agents
3. Routes requests and synthesizes responses
4. Maintains conversation context and state

Author: ALIMS Development Team
Date: July 3, 2025
Status: Implementing from validated TLA+ model
"""

import asyncio
import uuid
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Any
from datetime import datetime
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class ConversationState(Enum):
    """Conversation states as defined in TLA+ specification."""
    ACTIVE = "ACTIVE"
    WAITING_AGENT = "WAITING_AGENT" 
    PROCESSING = "PROCESSING"
    COMPLETED = "COMPLETED"
    ESCALATED = "ESCALATED"


class AgentState(Enum):
    """Agent states as defined in TLA+ specification."""
    IDLE = "IDLE"
    BUSY = "BUSY"
    ERROR = "ERROR"
    OFFLINE = "OFFLINE"


class CentralBrainState(Enum):
    """Central Brain orchestration states."""
    INITIALIZING = "INITIALIZING"
    READY = "READY" 
    ORCHESTRATING = "ORCHESTRATING"
    ERROR = "ERROR"


class RequestType(Enum):
    """Types of user requests the system can handle."""
    SAMPLE_INQUIRY = "SAMPLE_INQUIRY"
    WORKFLOW_COMMAND = "WORKFLOW_COMMAND"
    SYSTEM_QUERY = "SYSTEM_QUERY"
    AGENT_REQUEST = "AGENT_REQUEST"


class Priority(Enum):
    """Request priority levels."""
    LOW = "LOW"
    MEDIUM = "MEDIUM"
    HIGH = "HIGH"
    CRITICAL = "CRITICAL"


@dataclass
class Message:
    """Represents a message in a conversation."""
    role: str  # "user" or "assistant"
    content: str
    timestamp: datetime
    agent_source: Optional[str] = None  # Which agent provided this response


@dataclass
class ConversationContext:
    """Context tracking for each conversation as defined in TLA+ spec."""
    messages: List[Message] = field(default_factory=list)
    current_context: Dict[str, Any] = field(default_factory=dict)
    active_agents: Set[int] = field(default_factory=set)  # Agent IDs currently working
    user_intent: str = "UNKNOWN"


@dataclass
class UserRequest:
    """User request structure from TLA+ specification."""
    conversation_id: str
    request_type: RequestType
    content: str
    priority: Priority
    timestamp: datetime


@dataclass
class AgentResponse:
    """Response from a specialized agent."""
    agent_id: int
    content: str
    success: bool
    timestamp: datetime


@dataclass
class SpecializedAgent:
    """Represents a specialized LIMS agent."""
    agent_id: int
    state: AgentState
    capabilities: str  # e.g., "sample_tracker", "workflow_manager"


@dataclass
class SystemMetrics:
    """System performance and health metrics."""
    active_conversations: int = 0
    response_time: float = 0.0


class MainInterfaceAgent:
    """
    Main Interface Agent implementation based on validated TLA+ specification.
    
    This class implements the central brain that orchestrates specialized LIMS agents
    and manages user conversations according to the formally verified model.
    """
    
    def __init__(self, max_conversations: int = 10, max_agents: int = 20):
        """Initialize the Main Interface Agent."""
        # Configuration (bounded as per TLA+ model)
        self.max_conversations = max_conversations
        self.max_agents = max_agents
        self.max_context_depth = 50
        
        # State variables (matching TLA+ specification)
        self.conversations: Dict[str, ConversationState] = {}
        self.central_brain_state = CentralBrainState.INITIALIZING
        self.available_agents: Dict[int, SpecializedAgent] = {}
        self.agent_registry: Dict[int, str] = {}  # agent_id -> capabilities
        self.conversation_contexts: Dict[str, ConversationContext] = {}
        self.user_requests: List[UserRequest] = []
        self.agent_responses: List[AgentResponse] = []
        self.system_metrics = SystemMetrics()
        
        # Initialize locks for thread safety
        self._state_lock = asyncio.Lock()
        
        logger.info("MainInterfaceAgent initialized in INITIALIZING state")
    
    async def initialize_central_brain(self) -> bool:
        """
        Initialize the central brain and register core agents.
        Implements InitializeCentralBrain action from TLA+ specification.
        """
        async with self._state_lock:
            if self.central_brain_state != CentralBrainState.INITIALIZING:
                return False
            
            # Register core LIMS agents as defined in TLA+ model
            self.available_agents[1] = SpecializedAgent(
                agent_id=1,
                state=AgentState.IDLE,
                capabilities="sample_tracker"
            )
            self.available_agents[2] = SpecializedAgent(
                agent_id=2, 
                state=AgentState.IDLE,
                capabilities="workflow_manager"
            )
            
            # Update agent registry
            self.agent_registry[1] = "sample_tracker"
            self.agent_registry[2] = "workflow_manager"
            
            # Transition to READY state
            self.central_brain_state = CentralBrainState.READY
            
            logger.info("Central Brain initialized with core agents: sample_tracker, workflow_manager")
            return True
    
    async def register_agent(self, agent_id: int, capabilities: str) -> bool:
        """
        Register a new specialized agent.
        Implements RegisterAgent action from TLA+ specification.
        """
        async with self._state_lock:
            if self.central_brain_state != CentralBrainState.READY:
                return False
            
            if agent_id in self.agent_registry:
                return False  # Agent already registered
            
            if len(self.available_agents) >= self.max_agents:
                return False  # Capacity limit reached
            
            # Register new agent
            self.available_agents[agent_id] = SpecializedAgent(
                agent_id=agent_id,
                state=AgentState.IDLE,
                capabilities=capabilities
            )
            self.agent_registry[agent_id] = capabilities
            
            logger.info(f"Registered new agent {agent_id} with capabilities: {capabilities}")
            return True
    
    async def start_conversation(self, user_id: Optional[str] = None) -> Optional[str]:
        """
        Start a new conversation with a user.
        Implements StartConversation action from TLA+ specification.
        """
        async with self._state_lock:
            if self.central_brain_state != CentralBrainState.READY:
                return None
            
            if len(self.conversations) >= self.max_conversations:
                return None  # Capacity limit reached
            
            # Generate unique conversation ID
            conv_id = str(uuid.uuid4())
            
            # Create new conversation
            self.conversations[conv_id] = ConversationState.ACTIVE
            self.conversation_contexts[conv_id] = ConversationContext()
            
            # Update metrics
            self.system_metrics.active_conversations += 1
            
            logger.info(f"Started new conversation {conv_id}")
            return conv_id
    
    async def receive_user_request(
        self, 
        conv_id: str, 
        content: str, 
        request_type: RequestType,
        priority: Priority = Priority.MEDIUM
    ) -> bool:
        """
        Receive and queue a user request.
        Implements ReceiveUserRequest action from TLA+ specification.
        """
        async with self._state_lock:
            # Verify conversation exists and is active
            if conv_id not in self.conversations:
                return False
            if self.conversations[conv_id] != ConversationState.ACTIVE:
                return False
            
            # Check queue capacity (bounded as per TLA+ model)
            if len(self.user_requests) >= self.max_conversations * 10:
                return False
            
            # Create user request
            request = UserRequest(
                conversation_id=conv_id,
                request_type=request_type,
                content=content,
                priority=priority,
                timestamp=datetime.now()
            )
            
            # Add to request queue
            self.user_requests.append(request)
            
            # Add message to conversation context
            message = Message(
                role="user",
                content=content,
                timestamp=datetime.now()
            )
            self.conversation_contexts[conv_id].messages.append(message)
            
            logger.info(f"Received {request_type.value} request in conversation {conv_id}")
            return True
    
    async def analyze_and_orchestrate(self) -> bool:
        """
        Analyze pending requests and orchestrate appropriate agents.
        Implements AnalyzeAndOrchestrate action from TLA+ specification.
        """
        async with self._state_lock:
            if not self.user_requests:
                return False
            
            if self.central_brain_state != CentralBrainState.READY:
                return False
            
            # Transition to orchestrating state
            self.central_brain_state = CentralBrainState.ORCHESTRATING
            
            # Get next request (FIFO)
            request = self.user_requests.pop(0)
            conv_id = request.conversation_id
            
            # Determine required capabilities based on request type
            required_capabilities = self._get_required_capabilities(request.request_type)
            
            # Find suitable idle agents
            suitable_agents = set()
            for agent_id, agent in self.available_agents.items():
                if (agent.state == AgentState.IDLE and 
                    agent.capabilities in required_capabilities):
                    suitable_agents.add(agent_id)
            
            # Update conversation context
            context = self.conversation_contexts[conv_id]
            context.user_intent = request.request_type.value
            context.active_agents = suitable_agents
            
            logger.info(f"Orchestrated agents {suitable_agents} for {request.request_type.value}")
            return True
    
    def _get_required_capabilities(self, request_type: RequestType) -> Set[str]:
        """
        Determine required agent capabilities based on request type.
        Matches the logic from TLA+ specification.
        """
        capability_map = {
            RequestType.SAMPLE_INQUIRY: {"sample_tracker", "workflow_manager"},
            RequestType.WORKFLOW_COMMAND: {"workflow_manager", "lims_coordinator"},
            RequestType.SYSTEM_QUERY: {"system_monitor"},
            RequestType.AGENT_REQUEST: set()
        }
        return capability_map.get(request_type, set())
    
    async def route_to_agent(self, agent_id: int, request_content: str) -> bool:
        """
        Route work to a specific agent.
        Implements RouteToAgent action from TLA+ specification.
        """
        async with self._state_lock:
            if self.central_brain_state != CentralBrainState.ORCHESTRATING:
                return False
            
            # Verify agent exists and is idle
            if agent_id not in self.available_agents:
                return False
            if self.available_agents[agent_id].state != AgentState.IDLE:
                return False
            
            # Verify agent is assigned to an active conversation
            assigned_to_conversation = False
            for context in self.conversation_contexts.values():
                if agent_id in context.active_agents:
                    assigned_to_conversation = True
                    break
            
            if not assigned_to_conversation:
                return False
            
            # Change agent state to BUSY
            self.available_agents[agent_id].state = AgentState.BUSY
            
            logger.info(f"Routed work to agent {agent_id}: {request_content}")
            return True
    
    async def receive_agent_response(
        self, 
        agent_id: int, 
        response_content: str, 
        success: bool
    ) -> bool:
        """
        Receive response from a specialized agent.
        Implements ReceiveAgentResponse action from TLA+ specification.
        """
        async with self._state_lock:
            # Verify agent exists and is busy
            if agent_id not in self.available_agents:
                return False
            if self.available_agents[agent_id].state != AgentState.BUSY:
                return False
            
            # Check response queue capacity
            if len(self.agent_responses) >= self.max_agents * 10:
                return False
            
            # Create agent response
            response = AgentResponse(
                agent_id=agent_id,
                content=response_content,
                success=success,
                timestamp=datetime.now()
            )
            
            # Add to response queue
            self.agent_responses.append(response)
            
            # Return agent to idle state
            self.available_agents[agent_id].state = AgentState.IDLE
            
            logger.info(f"Received response from agent {agent_id} (success: {success})")
            return True
    
    async def synthesize_and_respond(self) -> bool:
        """
        Synthesize agent responses and respond to user.
        Implements SynthesizeAndRespond action from TLA+ specification.
        """
        async with self._state_lock:
            if not self.agent_responses:
                return False
            
            if self.central_brain_state != CentralBrainState.ORCHESTRATING:
                return False
            
            # Get next response (FIFO)
            response = self.agent_responses.pop(0)
            
            # Find the conversation that requested this agent
            target_conv = None
            for conv_id, context in self.conversation_contexts.items():
                if response.agent_id in context.active_agents:
                    target_conv = conv_id
                    break
            
            if target_conv is None:
                logger.warning(f"Could not find conversation for agent {response.agent_id}")
                return False
            
            # Add assistant message to conversation
            message = Message(
                role="assistant",
                content=response.content,
                timestamp=response.timestamp,
                agent_source=str(response.agent_id)
            )
            self.conversation_contexts[target_conv].messages.append(message)
            
            # Return central brain to ready state
            self.central_brain_state = CentralBrainState.READY
            
            logger.info(f"Synthesized response for conversation {target_conv}")
            return True
    
    async def complete_conversation(self, conv_id: str) -> bool:
        """
        Complete a conversation when all work is done.
        Implements CompleteConversation action from TLA+ specification.
        """
        async with self._state_lock:
            # Verify conversation exists and is active
            if conv_id not in self.conversations:
                return False
            if self.conversations[conv_id] != ConversationState.ACTIVE:
                return False
            
            context = self.conversation_contexts[conv_id]
            
            # Check completion conditions from TLA+ spec
            if context.active_agents:  # Still has active agents
                return False
            if len(context.messages) <= 1:  # Must have meaningful conversation
                return False
            
            # Complete the conversation
            self.conversations[conv_id] = ConversationState.COMPLETED
            self.system_metrics.active_conversations -= 1
            
            logger.info(f"Completed conversation {conv_id}")
            return True
    
    async def handle_agent_error(self, agent_id: int, error_type: str) -> bool:
        """
        Handle agent errors and escalate conversations.
        Implements HandleAgentError action from TLA+ specification.
        """
        async with self._state_lock:
            # Verify agent exists and is busy
            if agent_id not in self.available_agents:
                return False
            if self.available_agents[agent_id].state != AgentState.BUSY:
                return False
            
            # Change agent state to ERROR
            self.available_agents[agent_id].state = AgentState.ERROR
            
            # Find and escalate affected conversations
            for conv_id, context in self.conversation_contexts.items():
                if agent_id in context.active_agents:
                    if conv_id in self.conversations:
                        self.conversations[conv_id] = ConversationState.ESCALATED
            
            logger.error(f"Agent {agent_id} encountered error: {error_type}")
            return True
    
    # Public API methods for integration
    
    def get_conversation_history(self, conv_id: str) -> List[Message]:
        """Get message history for a conversation."""
        if conv_id in self.conversation_contexts:
            return self.conversation_contexts[conv_id].messages.copy()
        return []
    
    def get_active_conversations(self) -> List[str]:
        """Get list of active conversation IDs."""
        return [
            conv_id for conv_id, state in self.conversations.items()
            if state == ConversationState.ACTIVE
        ]
    
    def get_system_status(self) -> Dict[str, Any]:
        """Get current system status for monitoring."""
        return {
            "central_brain_state": self.central_brain_state.value,
            "active_conversations": self.system_metrics.active_conversations,
            "total_conversations": len(self.conversations),
            "available_agents": len([a for a in self.available_agents.values() if a.state == AgentState.IDLE]),
            "busy_agents": len([a for a in self.available_agents.values() if a.state == AgentState.BUSY]),
            "error_agents": len([a for a in self.available_agents.values() if a.state == AgentState.ERROR]),
            "pending_requests": len(self.user_requests),
            "pending_responses": len(self.agent_responses)
        }
    
    async def process_next_request(self) -> bool:
        """
        Process one cycle of the main orchestration loop.
        This method can be called repeatedly to drive the system.
        """
        # Try to orchestrate pending requests
        if await self.analyze_and_orchestrate():
            return True
        
        # Try to synthesize pending responses
        if await self.synthesize_and_respond():
            return True
        
        return False


# Convenience function for easy initialization
async def create_main_interface_agent(
    max_conversations: int = 10,
    max_agents: int = 20
) -> MainInterfaceAgent:
    """Create and initialize a Main Interface Agent."""
    agent = MainInterfaceAgent(max_conversations, max_agents)
    await agent.initialize_central_brain()
    return agent
