"""
Event Bus Implementation

Simple event bus for agent communication.
"""

from typing import Any, Callable, Dict, List
import asyncio
from dataclasses import dataclass


@dataclass
class Event:
    """Event data structure"""
    event_type: str
    data: Dict[str, Any]
    timestamp: float = None
    
    def __post_init__(self):
        if self.timestamp is None:
            self.timestamp = asyncio.get_event_loop().time()


class EventBus:
    """Simple event bus for agent communication"""
    
    def __init__(self):
        self._subscribers: Dict[str, List[Callable]] = {}
    
    async def subscribe(self, event_type: str, handler: Callable) -> None:
        """Subscribe to an event type"""
        if event_type not in self._subscribers:
            self._subscribers[event_type] = []
        self._subscribers[event_type].append(handler)
    
    async def publish(self, event: Event) -> None:
        """Publish an event"""
        if event.event_type in self._subscribers:
            for handler in self._subscribers[event.event_type]:
                try:
                    await handler(event)
                except Exception as e:
                    print(f"Error in event handler: {e}")
    
    def unsubscribe(self, event_type: str, handler: Callable) -> None:
        """Unsubscribe from an event type"""
        if event_type in self._subscribers:
            if handler in self._subscribers[event_type]:
                self._subscribers[event_type].remove(handler)
