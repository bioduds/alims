"""
Main Interface Agent Integration Module

This module integrates the formally verified Main Interface Agent 
into the ALIMS backend system, providing the central orchestration
for conversations between users and specialized LIMS agents.
"""

import asyncio
import logging
import sys
import os
from typing import Dict, List, Optional
from datetime import datetime

from .main_interface_agent import (
    MainInterfaceAgentSystem,
    CentralBrainState,
    DispatcherState,
    ConversationState
)

logger = logging.getLogger(__name__)

class LIMSMainInterfaceService:
    """
    Service class that wraps the Main Interface Agent for ALIMS integration.
    Provides high-level API for the Tauri frontend and manages agent lifecycle.
    """
    
    def __init__(self):
        self.agent: Optional[MainInterfaceAgent] = None
        self._initialized = False
        
    async def initialize(self) -> bool:
        """Initialize the Main Interface Agent and register core LIMS agents."""
        try:
            # Create the main interface agent
            self.agent = await create_main_interface_agent()
            
            # Register core LIMS agents
            await self._register_core_agents()
            
            self._initialized = True
            logger.info("LIMS Main Interface Service initialized successfully")
            return True
            
        except Exception as e:
            logger.error(f"Failed to initialize LIMS Main Interface Service: {e}")
            return False
    
    async def _register_core_agents(self):
        """Register the core LIMS specialized agents."""
        core_agents = [
            ("sample_tracker_001", "sample_tracker"),
            ("workflow_manager_001", "workflow_manager"),
            ("lims_coordinator_001", "lims_coordinator"),
            ("system_monitor_001", "system_monitor"),
            ("qc_manager_001", "qc_manager"),
            ("report_generator_001", "report_generator")
        ]
        
        for agent_id, capabilities in core_agents:
            success = await self.agent.register_agent(agent_id, capabilities)
            if success:
                logger.info(f"Registered agent {agent_id} with capabilities {capabilities}")
            else:
                logger.warning(f"Failed to register agent {agent_id}")
    
    async def start_conversation(self) -> Optional[str]:
        """Start a new conversation and return the conversation ID."""
        if not self._initialized:
            logger.error("Service not initialized")
            return None
            
        conv_id = await self.agent.start_conversation()
        if conv_id:
            logger.info(f"Started new conversation: {conv_id}")
        return conv_id
    
    async def send_user_message(
        self, 
        conversation_id: str, 
        message: str, 
        message_type: str = "SAMPLE_INQUIRY",
        priority: str = "MEDIUM"
    ) -> bool:
        """Send a user message to the specified conversation."""
        if not self._initialized:
            logger.error("Service not initialized")
            return False
        
        # Map string types to enums
        request_type = RequestType(message_type)
        priority_enum = Priority(priority)
        
        success = await self.agent.receive_user_request(
            conversation_id, message, request_type, priority_enum
        )
        
        if success:
            logger.info(f"Received user message in conversation {conversation_id}")
            # Process the request
            await self.agent.process_next_request()
        
        return success
    
    async def get_conversation_messages(self, conversation_id: str) -> List[Dict]:
        """Get all messages for a conversation."""
        if not self._initialized:
            return []
            
        history = self.agent.get_conversation_history(conversation_id)
        
        # Convert to frontend-compatible format
        messages = []
        for msg in history.get('messages', []):
            messages.append({
                'role': msg.get('role', 'user'),
                'content': msg.get('content', ''),
                'timestamp': msg.get('timestamp', datetime.now().isoformat()),
                'agent_source': msg.get('agent_source')
            })
        
        return messages
    
    async def get_active_conversations(self) -> List[Dict]:
        """Get all active conversations."""
        if not self._initialized:
            return []
            
        active_convs = self.agent.get_active_conversations()
        return [
            {
                'conversation_id': conv_id,
                'state': state.value,
                'message_count': len(self.agent.conversation_contexts.get(conv_id, {}).get('messages', []))
            }
            for conv_id, state in active_convs.items()
        ]
    
    async def get_system_status(self) -> Dict:
        """Get current system status."""
        if not self._initialized:
            return {'status': 'not_initialized'}
            
        status = self.agent.get_system_status()
        status['initialized'] = True
        status['service_status'] = 'ready'
        return status
    
    async def complete_conversation(self, conversation_id: str) -> bool:
        """Mark a conversation as complete."""
        if not self._initialized:
            return False
            
        return await self.agent.complete_conversation(conversation_id)

# Global service instance
_lims_interface_service: Optional[LIMSMainInterfaceService] = None

async def get_lims_interface_service() -> LIMSMainInterfaceService:
    """Get or create the global LIMS interface service."""
    global _lims_interface_service
    
    if _lims_interface_service is None:
        _lims_interface_service = LIMSMainInterfaceService()
        await _lims_interface_service.initialize()
    
    return _lims_interface_service

# Tauri command functions for frontend integration
async def start_lims_conversation() -> Dict:
    """Tauri command to start a new LIMS conversation."""
    try:
        service = await get_lims_interface_service()
        conv_id = await service.start_conversation()
        
        return {
            'success': True,
            'conversation_id': conv_id,
            'message': 'Conversation started successfully'
        }
    except Exception as e:
        logger.error(f"Error starting conversation: {e}")
        return {
            'success': False,
            'error': str(e)
        }

async def send_lims_message(conversation_id: str, message: str, message_type: str = "SAMPLE_INQUIRY") -> Dict:
    """Tauri command to send a message in a LIMS conversation."""
    try:
        service = await get_lims_interface_service()
        success = await service.send_user_message(conversation_id, message, message_type)
        
        if success:
            # Get updated messages
            messages = await service.get_conversation_messages(conversation_id)
            return {
                'success': True,
                'messages': messages
            }
        else:
            return {
                'success': False,
                'error': 'Failed to send message'
            }
    except Exception as e:
        logger.error(f"Error sending message: {e}")
        return {
            'success': False,
            'error': str(e)
        }

async def get_lims_conversation_messages(conversation_id: str) -> Dict:
    """Tauri command to get conversation messages."""
    try:
        service = await get_lims_interface_service()
        messages = await service.get_conversation_messages(conversation_id)
        
        return {
            'success': True,
            'messages': messages
        }
    except Exception as e:
        logger.error(f"Error getting messages: {e}")
        return {
            'success': False,
            'error': str(e)
        }

async def get_lims_system_status() -> Dict:
    """Tauri command to get system status."""
    try:
        service = await get_lims_interface_service()
        status = await service.get_system_status()
        
        return {
            'success': True,
            'status': status
        }
    except Exception as e:
        logger.error(f"Error getting system status: {e}")
        return {
            'success': False,
            'error': str(e)
        }
