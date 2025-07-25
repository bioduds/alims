"""
Agent State Tracker - Real-time Agent Monitoring
Based on TLA+ verified AgentState specification

Provides thread-safe tracking of agent states with automatic activity monitoring
and conversation management as proven in the formal specification.
"""

from typing import Dict, List, Optional, Set, Any, Callable
import time
import threading
from dataclasses import dataclass
import logging

from .event_system import (
    DebugEventSystem, AgentState, AgentStatus, EventType, 
    EventRecord, create_event, get_debug_system
)

logger = logging.getLogger(__name__)


@dataclass
class AgentActivity:
    """Extended agent activity tracking"""
    agent_id: str
    total_messages: int = 0
    successful_responses: int = 0
    error_count: int = 0
    avg_response_time: float = 0.0
    last_error: Optional[str] = None
    conversations: Set[str] = None
    
    def __post_init__(self):
        if self.conversations is None:
            self.conversations = set()


class AgentTracker:
    """
    Real-time agent state tracker implementing TLA+ verified behavior
    
    Maintains agent state consistency and provides monitoring capabilities
    for debugging agent interactions and "crazy talk" issues.
    """
    
    def __init__(self, debug_system: Optional[DebugEventSystem] = None):
        """
        Initialize agent tracker
        
        Args:
            debug_system: Debug system instance (uses global if None)
        """
        self.debug_system = debug_system or get_debug_system()
        self.agent_activities: Dict[str, AgentActivity] = {}
        self.conversation_agents: Dict[str, Set[str]] = {}
        self._lock = threading.RLock()
        
        # Callbacks for state changes
        self.state_change_callbacks: List[Callable[[str, AgentState], None]] = []
        
        logger.info("AgentTracker initialized")

    def register_agent(self, agent_id: str, agent_type: str = "unknown") -> bool:
        """
        Register new agent for tracking
        
        Args:
            agent_id: Unique agent identifier
            agent_type: Type of agent (e.g., "main_interface", "chat_agent")
            
        Returns:
            bool: True if agent registered successfully
        """
        with self._lock:
            # Create initial agent state
            initial_state = AgentState(
                status=AgentStatus.READY,
                last_activity=time.time(),
                current_conversation=None,
                processing_message=False
            )
            
            # Update debug system
            success = self.debug_system.update_agent_state(agent_id, initial_state)
            
            if success:
                # Initialize activity tracking
                self.agent_activities[agent_id] = AgentActivity(agent_id=agent_id)
                
                # Record registration event
                event = create_event(
                    agent_id=agent_id,
                    event_type=EventType.INIT,
                    message=f"Agent {agent_id} ({agent_type}) registered for tracking"
                )
                self.debug_system.record_event(event)
                
                logger.info(f"Agent {agent_id} registered successfully")
                return True
            else:
                logger.error(f"Failed to register agent {agent_id}")
                return False

    def update_agent_status(self, agent_id: str, status: AgentStatus, 
                          message: Optional[str] = None) -> bool:
        """
        Update agent status with automatic event recording
        
        Args:
            agent_id: Agent identifier
            status: New agent status
            message: Optional status change message
            
        Returns:
            bool: True if status updated successfully
        """
        with self._lock:
            # Get current state or create default
            current_state = self.debug_system.get_agent_state(agent_id)
            if current_state is None:
                # Auto-register agent if not exists
                if not self.register_agent(agent_id):
                    return False
                current_state = self.debug_system.get_agent_state(agent_id)
            
            # Create new state with updated status
            new_state = AgentState(
                status=status,
                last_activity=time.time(),
                current_conversation=current_state.current_conversation,
                processing_message=current_state.processing_message
            )
            
            # Update debug system
            success = self.debug_system.update_agent_state(agent_id, new_state)
            
            if success:
                # Record state change event
                event_message = message or f"Agent status changed to {status.value}"
                event = create_event(
                    agent_id=agent_id,
                    event_type=EventType.STATE_CHANGE,
                    message=event_message,
                    conversation_id=current_state.current_conversation
                )
                self.debug_system.record_event(event)
                
                # Update activity tracking
                if agent_id in self.agent_activities:
                    activity = self.agent_activities[agent_id]
                    if status == AgentStatus.ERROR:
                        activity.error_count += 1
                        activity.last_error = event_message
                
                # Notify callbacks
                for callback in self.state_change_callbacks:
                    try:
                        callback(agent_id, new_state)
                    except Exception as e:
                        logger.error(f"Callback error: {e}")
                
                logger.debug(f"Agent {agent_id} status updated to {status.value}")
                return True
            else:
                logger.error(f"Failed to update agent {agent_id} status")
                return False

    def start_conversation(self, agent_id: str, conversation_id: str) -> bool:
        """
        Mark agent as starting a conversation
        
        Args:
            agent_id: Agent identifier
            conversation_id: Conversation identifier
            
        Returns:
            bool: True if conversation started successfully
        """
        with self._lock:
            current_state = self.debug_system.get_agent_state(agent_id)
            if current_state is None:
                logger.error(f"Agent {agent_id} not found")
                return False
            
            # Update state to indicate conversation
            new_state = AgentState(
                status=current_state.status,
                last_activity=time.time(),
                current_conversation=conversation_id,
                processing_message=False
            )
            
            success = self.debug_system.update_agent_state(agent_id, new_state)
            
            if success:
                # Track conversation-agent mapping
                if conversation_id not in self.conversation_agents:
                    self.conversation_agents[conversation_id] = set()
                self.conversation_agents[conversation_id].add(agent_id)
                
                # Update activity tracking
                if agent_id in self.agent_activities:
                    self.agent_activities[agent_id].conversations.add(conversation_id)
                
                # Record event
                event = create_event(
                    agent_id=agent_id,
                    event_type=EventType.STATE_CHANGE,
                    message=f"Started conversation {conversation_id}",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(event)
                
                logger.info(f"Agent {agent_id} started conversation {conversation_id}")
                return True
            else:
                return False

    def end_conversation(self, agent_id: str, conversation_id: Optional[str] = None) -> bool:
        """
        Mark agent as ending a conversation
        
        Args:
            agent_id: Agent identifier
            conversation_id: Conversation identifier (uses current if None)
            
        Returns:
            bool: True if conversation ended successfully
        """
        with self._lock:
            current_state = self.debug_system.get_agent_state(agent_id)
            if current_state is None:
                logger.error(f"Agent {agent_id} not found")
                return False
            
            # Use current conversation if not specified
            conv_id = conversation_id or current_state.current_conversation
            if not conv_id:
                logger.warning(f"Agent {agent_id} has no active conversation to end")
                return False
            
            # Update state to clear conversation
            new_state = AgentState(
                status=current_state.status,
                last_activity=time.time(),
                current_conversation=None,
                processing_message=False
            )
            
            success = self.debug_system.update_agent_state(agent_id, new_state)
            
            if success:
                # Remove from conversation tracking
                if conv_id in self.conversation_agents:
                    self.conversation_agents[conv_id].discard(agent_id)
                    if not self.conversation_agents[conv_id]:
                        del self.conversation_agents[conv_id]
                
                # Record event
                event = create_event(
                    agent_id=agent_id,
                    event_type=EventType.STATE_CHANGE,
                    message=f"Ended conversation {conv_id}",
                    conversation_id=conv_id
                )
                self.debug_system.record_event(event)
                
                logger.info(f"Agent {agent_id} ended conversation {conv_id}")
                return True
            else:
                return False

    def record_message_received(self, agent_id: str, message: str, 
                              conversation_id: Optional[str] = None) -> bool:
        """
        Record that agent received a message
        
        Args:
            agent_id: Agent identifier
            message: Message content (truncated for logging)
            conversation_id: Conversation identifier
            
        Returns:
            bool: True if message recorded successfully
        """
        with self._lock:
            # Update activity tracking
            if agent_id in self.agent_activities:
                self.agent_activities[agent_id].total_messages += 1
            
            # Get current conversation if not provided
            if not conversation_id:
                current_state = self.debug_system.get_agent_state(agent_id)
                conversation_id = current_state.current_conversation if current_state else None
            
            # Record event
            truncated_message = message[:200] + "..." if len(message) > 200 else message
            event = create_event(
                agent_id=agent_id,
                event_type=EventType.RECEIVE_MESSAGE,
                message=f"Received: {truncated_message}",
                conversation_id=conversation_id
            )
            
            return self.debug_system.record_event(event)

    def record_message_response(self, agent_id: str, response: str,
                              response_time: float, conversation_id: Optional[str] = None) -> bool:
        """
        Record agent response with timing
        
        Args:
            agent_id: Agent identifier
            response: Response content (truncated for logging)
            response_time: Response time in seconds
            conversation_id: Conversation identifier
            
        Returns:
            bool: True if response recorded successfully
        """
        with self._lock:
            # Update activity tracking
            if agent_id in self.agent_activities:
                activity = self.agent_activities[agent_id]
                activity.successful_responses += 1
                # Update average response time
                if activity.avg_response_time == 0:
                    activity.avg_response_time = response_time
                else:
                    activity.avg_response_time = (activity.avg_response_time + response_time) / 2
            
            # Get current conversation if not provided
            if not conversation_id:
                current_state = self.debug_system.get_agent_state(agent_id)
                conversation_id = current_state.current_conversation if current_state else None
            
            # Record event
            truncated_response = response[:200] + "..." if len(response) > 200 else response
            event = create_event(
                agent_id=agent_id,
                event_type=EventType.RESPOND,
                message=f"Response ({response_time:.3f}s): {truncated_response}",
                conversation_id=conversation_id
            )
            
            return self.debug_system.record_event(event)

    def record_error(self, agent_id: str, error_message: str,
                    conversation_id: Optional[str] = None) -> bool:
        """
        Record agent error with automatic status update
        
        Args:
            agent_id: Agent identifier
            error_message: Error description
            conversation_id: Conversation identifier
            
        Returns:
            bool: True if error recorded successfully
        """
        with self._lock:
            # Update agent status to ERROR
            self.update_agent_status(agent_id, AgentStatus.ERROR, error_message)
            
            # Get current conversation if not provided
            if not conversation_id:
                current_state = self.debug_system.get_agent_state(agent_id)
                conversation_id = current_state.current_conversation if current_state else None
            
            # Record error event
            event = create_event(
                agent_id=agent_id,
                event_type=EventType.ERROR,
                message=f"ERROR: {error_message}",
                conversation_id=conversation_id
            )
            
            return self.debug_system.record_event(event)

    def get_agent_activity(self, agent_id: str) -> Optional[AgentActivity]:
        """Get agent activity summary"""
        with self._lock:
            return self.agent_activities.get(agent_id)

    def get_conversation_agents(self, conversation_id: str) -> Set[str]:
        """Get all agents in a conversation"""
        with self._lock:
            return self.conversation_agents.get(conversation_id, set()).copy()

    def get_active_conversations(self) -> Dict[str, Set[str]]:
        """Get all active conversations and their agents"""
        with self._lock:
            return {k: v.copy() for k, v in self.conversation_agents.items()}

    def add_state_change_callback(self, callback: Callable[[str, AgentState], None]) -> None:
        """Add callback for agent state changes"""
        self.state_change_callbacks.append(callback)

    def get_agent_summary(self) -> Dict[str, Any]:
        """
        Get comprehensive agent tracking summary
        
        Returns:
            Dictionary with agent tracking statistics
        """
        with self._lock:
            summary = {
                'total_agents': len(self.agent_activities),
                'active_conversations': len(self.conversation_agents),
                'agents': {},
                'conversations': {}
            }
            
            # Agent details
            for agent_id, activity in self.agent_activities.items():
                agent_state = self.debug_system.get_agent_state(agent_id)
                summary['agents'][agent_id] = {
                    'state': agent_state.to_dict() if agent_state else None,
                    'activity': {
                        'total_messages': activity.total_messages,
                        'successful_responses': activity.successful_responses,
                        'error_count': activity.error_count,
                        'avg_response_time': activity.avg_response_time,
                        'last_error': activity.last_error,
                        'conversations_count': len(activity.conversations)
                    }
                }
            
            # Conversation details
            for conv_id, agents in self.conversation_agents.items():
                summary['conversations'][conv_id] = {
                    'agents': list(agents),
                    'agent_count': len(agents)
                }
            
            return summary


# Global agent tracker instance
_agent_tracker: Optional[AgentTracker] = None


def get_agent_tracker() -> AgentTracker:
    """
    Get global agent tracker instance
    
    Returns:
        AgentTracker: Global agent tracker instance
    """
    global _agent_tracker
    if _agent_tracker is None:
        _agent_tracker = AgentTracker()
    return _agent_tracker
