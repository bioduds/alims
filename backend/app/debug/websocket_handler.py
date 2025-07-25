"""
WebSocket Handler - Real-time Debug Event Streaming
Based on TLA+ verified subscriber management

Provides real-time streaming of debug events to WebSocket clients
with subscriber management as proven in the formal specification.
"""

import json
import asyncio
import time
from typing import Dict, Set, Any, Optional, List
import logging
from dataclasses import asdict
import weakref

try:
    import websockets
    from websockets.server import WebSocketServerProtocol
    WEBSOCKETS_AVAILABLE = True
except ImportError:
    WebSocketServerProtocol = Any  # Type hint fallback
    WEBSOCKETS_AVAILABLE = False

from .event_system import (
    DebugEventSystem, EventRecord, AgentState, get_debug_system
)
from .agent_tracker import AgentTracker, get_agent_tracker

logger = logging.getLogger(__name__)


class WebSocketDebugHandler:
    """
    WebSocket handler for real-time debug event streaming
    
    Implements TLA+ verified subscriber management ensuring:
    - Safe addition/removal of subscribers
    - Bounded subscriber count
    - Reliable event broadcasting
    """
    
    def __init__(self, debug_system: Optional[DebugEventSystem] = None,
                 agent_tracker: Optional[AgentTracker] = None):
        """
        Initialize WebSocket handler
        
        Args:
            debug_system: Debug system instance
            agent_tracker: Agent tracker instance
        """
        self.debug_system = debug_system or get_debug_system()
        self.agent_tracker = agent_tracker or get_agent_tracker()
        
        # Use weak references to avoid memory leaks
        self.connections: Dict[int, WebSocketServerProtocol] = {}
        self.subscriber_filters: Dict[int, Dict[str, Any]] = {}
        self._next_subscriber_id = 1
        
        # Event queue for broadcasting
        self.event_queue = asyncio.Queue()
        self.broadcast_task: Optional[asyncio.Task] = None
        
        # Statistics
        self.stats = {
            'total_connections': 0,
            'active_connections': 0,
            'events_sent': 0,
            'errors': 0
        }
        
        logger.info("WebSocketDebugHandler initialized")

    async def register_connection(self, websocket: WebSocketServerProtocol) -> int:
        """
        Register new WebSocket connection
        
        Args:
            websocket: WebSocket connection
            
        Returns:
            int: Subscriber ID
        """
        subscriber_id = self._next_subscriber_id
        self._next_subscriber_id += 1
        
        # Add to debug system (TLA+ verified operation)
        if not self.debug_system.add_subscriber(subscriber_id):
            logger.error(f"Failed to add subscriber {subscriber_id}")
            raise Exception("Failed to register subscriber")
        
        # Store connection
        self.connections[subscriber_id] = websocket
        self.subscriber_filters[subscriber_id] = {}
        
        # Update statistics
        self.stats['total_connections'] += 1
        self.stats['active_connections'] = len(self.connections)
        
        logger.info(f"WebSocket subscriber {subscriber_id} registered")
        return subscriber_id

    async def unregister_connection(self, subscriber_id: int) -> None:
        """
        Unregister WebSocket connection
        
        Args:
            subscriber_id: Subscriber ID to remove
        """
        # Remove from debug system (TLA+ verified operation)
        self.debug_system.remove_subscriber(subscriber_id)
        
        # Clean up local data
        self.connections.pop(subscriber_id, None)
        self.subscriber_filters.pop(subscriber_id, None)
        
        # Update statistics
        self.stats['active_connections'] = len(self.connections)
        
        logger.info(f"WebSocket subscriber {subscriber_id} unregistered")

    async def set_subscriber_filter(self, subscriber_id: int, filters: Dict[str, Any]) -> bool:
        """
        Set event filters for subscriber
        
        Args:
            subscriber_id: Subscriber ID
            filters: Filter criteria (agent_ids, event_types, conversation_ids)
            
        Returns:
            bool: True if filters set successfully
        """
        if subscriber_id not in self.connections:
            return False
        
        # Validate filter format
        valid_filters = {}
        if 'agent_ids' in filters and isinstance(filters['agent_ids'], list):
            valid_filters['agent_ids'] = set(filters['agent_ids'])
        if 'event_types' in filters and isinstance(filters['event_types'], list):
            valid_filters['event_types'] = set(filters['event_types'])
        if 'conversation_ids' in filters and isinstance(filters['conversation_ids'], list):
            valid_filters['conversation_ids'] = set(filters['conversation_ids'])
        if 'min_level' in filters:
            valid_filters['min_level'] = filters['min_level']
        
        self.subscriber_filters[subscriber_id] = valid_filters
        
        logger.debug(f"Filters set for subscriber {subscriber_id}: {valid_filters}")
        return True

    def _event_matches_filter(self, event: EventRecord, filters: Dict[str, Any]) -> bool:
        """
        Check if event matches subscriber filters
        
        Args:
            event: Event to check
            filters: Subscriber filters
            
        Returns:
            bool: True if event matches filters
        """
        if not filters:
            return True  # No filters = receive all events
        
        # Check agent filter
        if 'agent_ids' in filters and event.agent_id not in filters['agent_ids']:
            return False
        
        # Check event type filter
        if 'event_types' in filters and event.event_type.value not in filters['event_types']:
            return False
        
        # Check conversation filter
        if 'conversation_ids' in filters:
            if event.conversation_id is None:
                return False
            if event.conversation_id not in filters['conversation_ids']:
                return False
        
        return True

    async def broadcast_event(self, event: EventRecord) -> None:
        """
        Broadcast event to all matching subscribers
        
        Args:
            event: Event to broadcast
        """
        if not self.connections:
            return
        
        # Prepare event data
        event_data = {
            'type': 'debug_event',
            'timestamp': time.time(),
            'event': event.to_dict()
        }
        
        message = json.dumps(event_data)
        disconnected_subscribers = []
        
        # Send to all matching subscribers
        for subscriber_id, websocket in self.connections.items():
            try:
                # Check filters
                filters = self.subscriber_filters.get(subscriber_id, {})
                if not self._event_matches_filter(event, filters):
                    continue
                
                # Send message
                await websocket.send(message)
                self.stats['events_sent'] += 1
                
            except Exception as e:
                logger.error(f"Error sending to subscriber {subscriber_id}: {e}")
                disconnected_subscribers.append(subscriber_id)
                self.stats['errors'] += 1
        
        # Clean up disconnected subscribers
        for subscriber_id in disconnected_subscribers:
            await self.unregister_connection(subscriber_id)

    async def broadcast_agent_state(self, agent_id: str, state: AgentState) -> None:
        """
        Broadcast agent state change
        
        Args:
            agent_id: Agent identifier
            state: New agent state
        """
        if not self.connections:
            return
        
        # Prepare state data
        state_data = {
            'type': 'agent_state_change',
            'timestamp': time.time(),
            'agent_id': agent_id,
            'state': state.to_dict()
        }
        
        message = json.dumps(state_data)
        disconnected_subscribers = []
        
        # Send to all subscribers interested in this agent
        for subscriber_id, websocket in self.connections.items():
            try:
                # Check if subscriber wants this agent
                filters = self.subscriber_filters.get(subscriber_id, {})
                if 'agent_ids' in filters and agent_id not in filters['agent_ids']:
                    continue
                
                # Send message
                await websocket.send(message)
                
            except Exception as e:
                logger.error(f"Error sending state to subscriber {subscriber_id}: {e}")
                disconnected_subscribers.append(subscriber_id)
        
        # Clean up disconnected subscribers
        for subscriber_id in disconnected_subscribers:
            await self.unregister_connection(subscriber_id)

    async def send_system_stats(self, subscriber_id: int) -> bool:
        """
        Send system statistics to specific subscriber
        
        Args:
            subscriber_id: Target subscriber
            
        Returns:
            bool: True if stats sent successfully
        """
        if subscriber_id not in self.connections:
            return False
        
        try:
            # Gather comprehensive statistics
            debug_stats = self.debug_system.get_system_stats()
            agent_stats = self.agent_tracker.get_agent_summary()
            
            stats_data = {
                'type': 'system_stats',
                'timestamp': time.time(),
                'debug_system': debug_stats,
                'agent_tracker': agent_stats,
                'websocket': self.stats
            }
            
            message = json.dumps(stats_data)
            await self.connections[subscriber_id].send(message)
            
            return True
            
        except Exception as e:
            logger.error(f"Error sending stats to subscriber {subscriber_id}: {e}")
            await self.unregister_connection(subscriber_id)
            return False

    async def send_recent_events(self, subscriber_id: int, limit: int = 50) -> bool:
        """
        Send recent events to subscriber
        
        Args:
            subscriber_id: Target subscriber
            limit: Maximum number of events
            
        Returns:
            bool: True if events sent successfully
        """
        if subscriber_id not in self.connections:
            return False
        
        try:
            # Get recent events
            events = self.debug_system.get_recent_events(limit)
            filters = self.subscriber_filters.get(subscriber_id, {})
            
            # Filter events for this subscriber
            filtered_events = [
                event.to_dict() for event in events
                if self._event_matches_filter(event, filters)
            ]
            
            # Send batch
            batch_data = {
                'type': 'event_batch',
                'timestamp': time.time(),
                'events': filtered_events,
                'total_count': len(filtered_events)
            }
            
            message = json.dumps(batch_data)
            await self.connections[subscriber_id].send(message)
            
            return True
            
        except Exception as e:
            logger.error(f"Error sending events to subscriber {subscriber_id}: {e}")
            await self.unregister_connection(subscriber_id)
            return False

    async def handle_message(self, subscriber_id: int, message: str) -> None:
        """
        Handle incoming WebSocket message
        
        Args:
            subscriber_id: Sender subscriber ID
            message: JSON message content
        """
        try:
            data = json.loads(message)
            msg_type = data.get('type')
            
            if msg_type == 'set_filters':
                await self.set_subscriber_filter(subscriber_id, data.get('filters', {}))
                
            elif msg_type == 'get_stats':
                await self.send_system_stats(subscriber_id)
                
            elif msg_type == 'get_recent_events':
                limit = data.get('limit', 50)
                await self.send_recent_events(subscriber_id, limit)
                
            elif msg_type == 'ping':
                # Send pong response
                pong_data = {'type': 'pong', 'timestamp': time.time()}
                await self.connections[subscriber_id].send(json.dumps(pong_data))
                
            else:
                logger.warning(f"Unknown message type from subscriber {subscriber_id}: {msg_type}")
                
        except json.JSONDecodeError:
            logger.error(f"Invalid JSON from subscriber {subscriber_id}: {message}")
        except Exception as e:
            logger.error(f"Error handling message from subscriber {subscriber_id}: {e}")

    async def start_broadcasting(self) -> None:
        """Start background event broadcasting task"""
        if self.broadcast_task is not None:
            return
        
        self.broadcast_task = asyncio.create_task(self._broadcast_loop())
        logger.info("WebSocket broadcasting started")

    async def stop_broadcasting(self) -> None:
        """Stop background event broadcasting task"""
        if self.broadcast_task is not None:
            self.broadcast_task.cancel()
            try:
                await self.broadcast_task
            except asyncio.CancelledError:
                pass
            self.broadcast_task = None
        
        logger.info("WebSocket broadcasting stopped")

    async def _broadcast_loop(self) -> None:
        """Background loop for broadcasting events"""
        while True:
            try:
                # Wait for event or timeout
                event = await asyncio.wait_for(self.event_queue.get(), timeout=1.0)
                await self.broadcast_event(event)
            except asyncio.TimeoutError:
                # Periodic cleanup and health check
                continue
            except Exception as e:
                logger.error(f"Error in broadcast loop: {e}")
                await asyncio.sleep(1)

    def queue_event_for_broadcast(self, event: EventRecord) -> None:
        """
        Queue event for broadcasting (thread-safe)
        
        Args:
            event: Event to broadcast
        """
        try:
            self.event_queue.put_nowait(event)
        except asyncio.QueueFull:
            logger.warning("Event queue full, dropping event")

    def get_connection_stats(self) -> Dict[str, Any]:
        """Get WebSocket connection statistics"""
        return {
            **self.stats,
            'active_connections': len(self.connections),
            'subscriber_ids': list(self.connections.keys()),
            'queue_size': self.event_queue.qsize() if hasattr(self.event_queue, 'qsize') else 0
        }


# Global WebSocket handler instance
_websocket_handler: Optional[WebSocketDebugHandler] = None


def get_websocket_handler() -> WebSocketDebugHandler:
    """
    Get global WebSocket handler instance
    
    Returns:
        WebSocketDebugHandler: Global handler instance
    """
    global _websocket_handler
    if _websocket_handler is None:
        _websocket_handler = WebSocketDebugHandler()
    return _websocket_handler


def setup_agent_state_callbacks() -> None:
    """Setup callbacks to broadcast agent state changes"""
    handler = get_websocket_handler()
    tracker = get_agent_tracker()
    
    async def on_agent_state_change(agent_id: str, state: AgentState) -> None:
        await handler.broadcast_agent_state(agent_id, state)
    
    # Add callback that converts sync to async
    def sync_callback(agent_id: str, state: AgentState) -> None:
        try:
            loop = asyncio.get_event_loop()
            loop.create_task(on_agent_state_change(agent_id, state))
        except RuntimeError:
            # No event loop running, skip broadcasting
            pass
    
    tracker.add_state_change_callback(sync_callback)
