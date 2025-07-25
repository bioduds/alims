"""
Debug System Module Initialization
TLA+ Verified Debug Infrastructure for ALIMS

Provides comprehensive debugging capabilities for tracing agent interactions
and resolving "crazy talk" issues through formal verification.
"""

from .event_system import (
    DebugEventSystem,
    EventType,
    AgentStatus,
    SystemStatus,
    EventRecord,
    AgentState,
    get_debug_system,
    create_event
)

from .agent_tracker import (
    AgentTracker,
    AgentActivity,
    get_agent_tracker
)

from .websocket_handler import (
    WebSocketDebugHandler,
    get_websocket_handler,
    setup_agent_state_callbacks,
    WEBSOCKETS_AVAILABLE
)

__all__ = [
    # Core debug system
    'DebugEventSystem',
    'get_debug_system',
    
    # Event types and data structures
    'EventType',
    'AgentStatus', 
    'SystemStatus',
    'EventRecord',
    'AgentState',
    'create_event',
    
    # Agent tracking
    'AgentTracker',
    'AgentActivity',
    'get_agent_tracker',
    
    # WebSocket streaming
    'WebSocketDebugHandler',
    'get_websocket_handler',
    'setup_agent_state_callbacks',
    'WEBSOCKETS_AVAILABLE',
    
    # Convenience functions
    'initialize_debug_system',
    'get_debug_interface'
]


def initialize_debug_system() -> DebugEventSystem:
    """
    Initialize the complete debug system
    
    Returns:
        DebugEventSystem: Initialized debug system instance
    """
    # Initialize core systems
    debug_system = get_debug_system()
    agent_tracker = get_agent_tracker()
    
    # Setup WebSocket callbacks if available
    if WEBSOCKETS_AVAILABLE:
        setup_agent_state_callbacks()
    
    return debug_system


def get_debug_interface() -> dict:
    """
    Get complete debug interface for easy access
    
    Returns:
        dict: Debug interface with all components
    """
    return {
        'debug_system': get_debug_system(),
        'agent_tracker': get_agent_tracker(),
        'websocket_handler': get_websocket_handler() if WEBSOCKETS_AVAILABLE else None,
        'websockets_available': WEBSOCKETS_AVAILABLE
    }
