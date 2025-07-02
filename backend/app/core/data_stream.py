#!/usr/bin/env python3
"""
ALims Data Stream Monitor

Monitors system events and feeds them to the embryo pool.
This is a simplified version for the initial implementation.
"""

import asyncio
import logging
import time
from typing import Dict, Any


class DataStreamMonitor:
    """
    Simple data stream monitor that generates mock system events
    for testing the embryo pool functionality.
    """
    
    def __init__(self, config: dict):
        self.config = config
        self.logger = logging.getLogger('DataStreamMonitor')
        self.is_running = False
        self.data_event = None  # Would be a Qt signal in real implementation
        
    async def initialize(self):
        """Initialize the data stream monitor"""
        self.logger.info("Initializing data stream monitor...")
        
    async def start_monitoring(self):
        """Start monitoring system events"""
        self.is_running = True
        self.logger.info("Starting system event monitoring...")
        
        # Start mock event generation
        asyncio.create_task(self._generate_mock_events())
        
    async def _generate_mock_events(self):
        """Generate mock system events for testing"""
        event_types = [
            {'type': 'app_launch', 'app_name': 'VSCode'},
            {'type': 'file_create', 'file_path': '/Users/user/code/test.py'},
            {'type': 'web_navigate', 'url': 'https://github.com'},
            {'type': 'app_switch', 'app_name': 'Terminal'},
            {'type': 'code_edit', 'file_path': '/Users/user/project/main.py'}
        ]
        
        while self.is_running:
            try:
                # Generate random event
                import random
                event = random.choice(event_types).copy()
                event['timestamp'] = time.time()
                
                # Simulate calling connected handlers
                if hasattr(self, '_event_handlers'):
                    for handler in self._event_handlers:
                        await handler(event)
                        
                await asyncio.sleep(2)  # Generate event every 2 seconds
                
            except Exception as e:
                self.logger.error(f"Error generating mock event: {e}")
                
    def connect(self, handler):
        """Connect an event handler"""
        if not hasattr(self, '_event_handlers'):
            self._event_handlers = []
        self._event_handlers.append(handler)
        
    def pause(self):
        """Pause monitoring"""
        self.is_running = False
        self.logger.info("Data monitoring paused")
        
    def resume(self):
        """Resume monitoring"""
        self.is_running = True
        self.logger.info("Data monitoring resumed")
        asyncio.create_task(self._generate_mock_events())
        
    def stop(self):
        """Stop monitoring"""
        self.is_running = False
        self.logger.info("Data monitoring stopped") 