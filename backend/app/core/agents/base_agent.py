"""
Base Agent Class

Abstract base class for all LIMS agents providing common functionality.
"""

from abc import ABC, abstractmethod
from typing import Any, Dict, Optional
import logging

from backend.app.core.events import EventBus


class BaseAgent(ABC):
    """Base class for all LIMS agents"""
    
    def __init__(self, agent_id: str, name: str, event_bus: EventBus):
        self.agent_id = agent_id
        self.name = name
        self.event_bus = event_bus
        self.logger = logging.getLogger(f"agents.{agent_id}")
        self._initialized = False
    
    async def initialize(self) -> None:
        """Initialize the agent"""
        if not self._initialized:
            self.logger.info(f"Initializing agent {self.name}")
            self._initialized = True
    
    @abstractmethod
    async def handle_event(self, event: Any) -> None:
        """Handle incoming events"""
        pass
    
    def get_status(self) -> Dict[str, Any]:
        """Get current agent status"""
        return {
            "agent_id": self.agent_id,
            "name": self.name,
            "initialized": self._initialized
        }
