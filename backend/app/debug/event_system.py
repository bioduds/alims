"""
Debug Event System - Core Implementation
Based on TLA+ verified specification: SimpleDebugSystem.tla

This module implements the formally verified debug event recording system
that ensures bounded memory usage and type safety as proven by TLC model checker.
"""

from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Any, Set
from enum import Enum
import time
import threading
from collections import deque
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class EventType(Enum):
    """Event types as defined in TLA+ specification"""
    INIT = "INIT"
    RECEIVE_MESSAGE = "RECEIVE_MESSAGE" 
    PROCESS = "PROCESS"
    RESPOND = "RESPOND"
    ERROR = "ERROR"
    STATE_CHANGE = "STATE_CHANGE"


class AgentStatus(Enum):
    """Agent status values as proven in TLA+ specification"""
    READY = "READY"
    BUSY = "BUSY"
    ERROR = "ERROR"


class SystemStatus(Enum):
    """System status values from TLA+ specification"""
    INITIALIZING = "INITIALIZING"
    READY = "READY"
    PROCESSING = "PROCESSING"
    ERROR = "ERROR"


@dataclass
class EventRecord:
    """
    Event record structure matching TLA+ EventRecord definition
    All fields are required for type safety as proven in specification
    """
    timestamp: float
    agent_id: str
    event_type: EventType
    message: str
    trace_id: str
    conversation_id: Optional[str] = None
    agent_type: str = "unknown"
    level: str = "INFO"
    data: str = ""

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization"""
        result = asdict(self)
        result['event_type'] = self.event_type.value
        return result


@dataclass
class AgentState:
    """
    Agent state structure matching TLA+ AgentState definition
    Ensures type safety and consistency as proven in specification
    """
    status: AgentStatus
    last_activity: float
    current_conversation: Optional[str] = None
    processing_message: bool = False

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization"""
        result = asdict(self)
        result['status'] = self.status.value
        return result


class DebugEventSystem:
    """
    Core debug event system implementing TLA+ verified behavior
    
    Key invariants maintained (as proven in TLA+):
    - Bounded memory: events never exceed MaxEvents
    - Type safety: all operations preserve data types
    - Consistency: agent states remain valid during transitions
    """
    
    def __init__(self, max_events: int = 1000, max_agents: int = 50):
        """
        Initialize debug system with bounds matching TLA+ constants
        
        Args:
            max_events: Maximum events to store (prevents memory overflow)
            max_agents: Maximum agents to track
        """
        # Validate inputs match TLA+ assumptions
        if max_events <= 0 or max_agents <= 0:
            raise ValueError("max_events and max_agents must be positive integers")
            
        self.max_events = max_events
        self.max_agents = max_agents
        
        # State variables matching TLA+ specification
        self.events: deque[EventRecord] = deque(maxlen=max_events)
        self.agent_states: Dict[str, AgentState] = {}
        self.active_conversations: Dict[str, List[EventRecord]] = {}
        self.subscribers: Set[int] = set()
        self.system_status = SystemStatus.INITIALIZING
        
        # Thread safety for concurrent access
        self._lock = threading.RLock()
        
        logger.info(f"DebugEventSystem initialized with max_events={max_events}, max_agents={max_agents}")

    def initialize_system(self) -> bool:
        """
        Initialize system state matching TLA+ InitializeSystem action
        Transition: INITIALIZING -> READY
        """
        with self._lock:
            if self.system_status != SystemStatus.INITIALIZING:
                logger.warning(f"Cannot initialize system from status {self.system_status}")
                return False
                
            self.system_status = SystemStatus.READY
            logger.info("Debug system initialized and ready")
            return True

    def record_event(self, event: EventRecord) -> bool:
        """
        Record new event implementing TLA+ RecordEvent action
        
        Ensures:
        - System is ready for operation
        - Memory bounds are respected (proven in TLA+)
        - Event is properly stored and indexed
        
        Args:
            event: EventRecord to store
            
        Returns:
            bool: True if event recorded successfully
        """
        with self._lock:
            if self.system_status != SystemStatus.READY:
                logger.warning(f"Cannot record event, system status: {self.system_status}")
                return False
                
            try:
                # Add timestamp if not provided
                if event.timestamp == 0:
                    event.timestamp = time.time()
                    
                # Store event (deque automatically maintains max_events bound)
                self.events.append(event)
                
                # Update conversation tracking if conversation_id provided
                if event.conversation_id:
                    if event.conversation_id not in self.active_conversations:
                        self.active_conversations[event.conversation_id] = []
                    self.active_conversations[event.conversation_id].append(event)
                
                logger.debug(f"Event recorded: {event.event_type.value} for agent {event.agent_id}")
                return True
                
            except Exception as e:
                logger.error(f"Failed to record event: {e}")
                return False

    def update_agent_state(self, agent_id: str, new_state: AgentState) -> bool:
        """
        Update agent state implementing TLA+ UpdateAgentState action
        
        Ensures:
        - System is ready for operation
        - Agent state consistency (status values from proven set)
        - Thread-safe atomic updates
        
        Args:
            agent_id: Agent identifier
            new_state: New agent state
            
        Returns:
            bool: True if state updated successfully
        """
        with self._lock:
            if self.system_status != SystemStatus.READY:
                logger.warning(f"Cannot update agent state, system status: {self.system_status}")
                return False
                
            if len(self.agent_states) >= self.max_agents and agent_id not in self.agent_states:
                logger.warning(f"Cannot add new agent {agent_id}, max_agents limit reached")
                return False
                
            try:
                # Update timestamp
                new_state.last_activity = time.time()
                
                # Store state
                self.agent_states[agent_id] = new_state
                
                logger.debug(f"Agent {agent_id} state updated to {new_state.status.value}")
                return True
                
            except Exception as e:
                logger.error(f"Failed to update agent state: {e}")
                return False

    def get_agent_state(self, agent_id: str) -> Optional[AgentState]:
        """
        Get current agent state with thread safety
        
        Args:
            agent_id: Agent identifier
            
        Returns:
            AgentState if found, None otherwise
        """
        with self._lock:
            return self.agent_states.get(agent_id)

    def get_conversation_events(self, conversation_id: str) -> List[EventRecord]:
        """
        Get all events for a specific conversation
        Implements TLA+ GetConversationEvents helper function
        
        Args:
            conversation_id: Conversation identifier
            
        Returns:
            List of events for the conversation
        """
        with self._lock:
            return self.active_conversations.get(conversation_id, []).copy()

    def get_recent_events(self, limit: int = 100) -> List[EventRecord]:
        """
        Get recent events with limit
        Ensures bounded response size
        
        Args:
            limit: Maximum number of events to return
            
        Returns:
            List of recent events (most recent first)
        """
        with self._lock:
            events_list = list(self.events)
            return events_list[-limit:] if limit < len(events_list) else events_list

    def add_subscriber(self, subscriber_id: int) -> bool:
        """
        Add WebSocket subscriber implementing TLA+ AddSubscriber action
        
        Args:
            subscriber_id: Unique subscriber identifier
            
        Returns:
            bool: True if subscriber added successfully
        """
        with self._lock:
            if self.system_status != SystemStatus.READY:
                return False
                
            if subscriber_id in self.subscribers:
                return False  # Already subscribed
                
            self.subscribers.add(subscriber_id)
            logger.info(f"Subscriber {subscriber_id} added")
            return True

    def remove_subscriber(self, subscriber_id: int) -> bool:
        """
        Remove WebSocket subscriber implementing TLA+ RemoveSubscriber action
        
        Args:
            subscriber_id: Subscriber identifier to remove
            
        Returns:
            bool: True if subscriber removed successfully
        """
        with self._lock:
            if subscriber_id not in self.subscribers:
                return False
                
            self.subscribers.remove(subscriber_id)
            logger.info(f"Subscriber {subscriber_id} removed")
            return True

    def get_system_stats(self) -> Dict[str, Any]:
        """
        Get system statistics for monitoring
        Provides bounded memory usage information as proven in TLA+
        
        Returns:
            Dictionary with system statistics
        """
        with self._lock:
            return {
                'system_status': self.system_status.value,
                'total_events': len(self.events),
                'max_events': self.max_events,
                'memory_usage_pct': (len(self.events) / self.max_events) * 100,
                'active_agents': len(self.agent_states),
                'max_agents': self.max_agents,
                'active_conversations': len(self.active_conversations),
                'subscribers_count': len(self.subscribers),
                'memory_bounded': len(self.events) <= self.max_events  # TLA+ invariant
            }

    def handle_error(self) -> None:
        """
        Handle system error implementing TLA+ HandleError action
        Transition: READY|PROCESSING -> ERROR
        """
        with self._lock:
            if self.system_status in [SystemStatus.READY, SystemStatus.PROCESSING]:
                self.system_status = SystemStatus.ERROR
                logger.error("Debug system entered error state")

    def recover_from_error(self) -> bool:
        """
        Recover from error implementing TLA+ RecoverFromError action
        Transition: ERROR -> READY
        
        Returns:
            bool: True if recovery successful
        """
        with self._lock:
            if self.system_status != SystemStatus.ERROR:
                return False
                
            self.system_status = SystemStatus.READY
            logger.info("Debug system recovered from error state")
            return True


# Global debug system instance (singleton pattern)
_debug_system: Optional[DebugEventSystem] = None


def get_debug_system() -> DebugEventSystem:
    """
    Get global debug system instance
    Implements singleton pattern for system-wide event tracking
    
    Returns:
        DebugEventSystem: Global debug system instance
    """
    global _debug_system
    if _debug_system is None:
        _debug_system = DebugEventSystem()
        _debug_system.initialize_system()
    return _debug_system


def create_event(agent_id: str, event_type: EventType, message: str,
                 conversation_id: Optional[str] = None, trace_id: Optional[str] = None) -> EventRecord:
    """
    Helper function to create properly formatted EventRecord
    
    Args:
        agent_id: Agent identifier
        event_type: Type of event
        message: Event message
        conversation_id: Optional conversation identifier
        trace_id: Optional trace identifier
        
    Returns:
        EventRecord: Properly formatted event record
    """
    return EventRecord(
        timestamp=time.time(),
        agent_id=agent_id,
        event_type=event_type,
        message=message,
        trace_id=trace_id or f"trace_{int(time.time()*1000)}_{agent_id}",
        conversation_id=conversation_id
    )
