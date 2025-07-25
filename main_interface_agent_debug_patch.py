#!/usr/bin/env python3
"""
MainInterfaceAgent Debug Integration Patch
Adds debug system support to your existing MainInterfaceAgent

Apply this patch by either:
1. Copy the modified methods into your existing MainInterfaceAgent
2. Or import and inherit from DebugMainInterfaceAgentMixin
"""

import asyncio
import logging
import time
import uuid
from typing import Dict, Any, Optional

# Import debug system
from backend.app.debug import (
    get_debug_system, get_agent_tracker, 
    EventType, AgentStatus, create_event
)

logger = logging.getLogger(__name__)


class DebugMainInterfaceAgentMixin:
    """
    Mixin to add debug capabilities to MainInterfaceAgent
    
    Usage: 
    class MainInterfaceAgent(DebugMainInterfaceAgentMixin, YourExistingBaseClass):
        def __init__(self, ...):
            super().__init__(...)
            self._init_debug_system()
    """
    
    def _init_debug_system(self):
        """Initialize debug system for MainInterfaceAgent"""
        # Initialize debug components
        self.debug_system = get_debug_system()
        self.agent_tracker = get_agent_tracker()
        
        # Register this agent
        agent_id = "main_interface_agent"
        self.agent_id = agent_id
        self.agent_tracker.register_agent(agent_id, "main_interface")
        
        # Set up monitoring for all agent state changes
        self.agent_tracker.add_state_change_callback(self._on_agent_state_change)
        
        logger.info("MainInterfaceAgent debug system initialized")
    
    def _on_agent_state_change(self, agent_id: str, new_state):
        """Monitor agent state changes for debugging"""
        logger.info(f"Agent {agent_id} state: {new_state.status.value}")
        
        if new_state.status == AgentStatus.ERROR:
            logger.warning(f"🚨 Agent {agent_id} in ERROR state!")
            
            # Get recent events for analysis
            recent_events = self.debug_system.get_recent_events(5)
            agent_events = [e for e in recent_events if e.agent_id == agent_id]
            
            for event in agent_events[-3:]:
                logger.warning(f"  📋 {event.event_type.value}: {event.message}")
    
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
        ]
        return any(indicators)


# ============================================================================
# PATCH FOR YOUR EXISTING METHODS
# ============================================================================

def patch_process_user_request():
    """
    Replace your existing process_user_request method with this version
    
    Copy this method into your MainInterfaceAgent class (after adding the mixin)
    """
    
    method_code = '''
    async def process_user_request(self, user_input: str, user_id: str = None, conversation_id: str = None) -> str:
        """
        Process user request with debug tracking
        Enhanced version of your existing method
        """
        
        # Generate IDs if needed
        if conversation_id is None:
            conversation_id = f"conv_{uuid.uuid4().hex[:8]}"
        if user_id is None:
            user_id = f"user_{uuid.uuid4().hex[:8]}"
        
        # Start debug tracking
        self.agent_tracker.start_conversation(self.agent_id, conversation_id)
        self.agent_tracker.record_message_received(
            self.agent_id, 
            f"User request: {user_input[:100]}...", 
            conversation_id
        )
        self.agent_tracker.update_agent_status(
            self.agent_id, 
            AgentStatus.BUSY, 
            "Processing user request"
        )
        
        start_time = time.time()
        
        try:
            # Use state lock for thread safety (your existing pattern)
            async with self._state_lock:
                
                # Log processing start
                event = create_event(
                    agent_id=self.agent_id,
                    event_type=EventType.PROCESS,
                    message=f"Starting to process: {user_input[:50]}...",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(event)
                
                # Check system capacity (your existing logic)
                if len(self.conversations) >= self.max_conversations:
                    error_msg = "Maximum conversations reached"
                    self.agent_tracker.record_error(self.agent_id, error_msg, conversation_id)
                    return "I'm currently handling the maximum number of conversations. Please try again later."
                
                # Create conversation context (your existing logic)
                conversation_context = ConversationContext(
                    conversation_id=conversation_id,
                    user_id=user_id,
                    state=ConversationState.ACTIVE,
                    created_at=datetime.now()
                )
                
                # Add to conversations
                self.conversations[conversation_id] = conversation_context
                
                # Log conversation creation
                event = create_event(
                    agent_id=self.agent_id,
                    event_type=EventType.STATE_CHANGE,
                    message=f"Created conversation {conversation_id}",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(event)
                
                # Process the request (your existing orchestration logic)
                response = await self._orchestrate_user_request(user_input, conversation_context)
                
                # Check for crazy talk
                if self._debug_check_crazy_talk(response):
                    self.agent_tracker.record_error(
                        self.agent_id, 
                        f"Crazy talk detected: {response[:100]}...", 
                        conversation_id
                    )
                    response = "I apologize, but I need to rephrase my response. Could you please try again with more specific details?"
                
                # Record successful response
                processing_time = time.time() - start_time
                self.agent_tracker.record_message_response(
                    self.agent_id, 
                    f"Response: {response[:100]}...", 
                    processing_time,
                    conversation_id
                )
                
                # Update metrics (your existing logic)
                self.system_metrics.total_requests += 1
                self.system_metrics.successful_responses += 1
                
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
            self.agent_tracker.record_error(self.agent_id, error_msg, conversation_id)
            
            # Update metrics
            self.system_metrics.failed_requests += 1
            
            logger.error(f"MainInterfaceAgent error: {error_msg}")
            return "I apologize, but I encountered an error processing your request. Please try again."
        
        finally:
            # End conversation tracking
            self.agent_tracker.end_conversation(self.agent_id, conversation_id)
    '''
    
    return method_code


def patch_orchestrate_user_request():
    """
    Enhanced version of your orchestration method with debug tracking
    """
    
    method_code = '''
    async def _orchestrate_user_request(self, user_input: str, conversation_context: ConversationContext) -> str:
        """
        Orchestrate user request with debug tracking
        Enhanced version of your existing orchestration logic
        """
        
        conversation_id = conversation_context.conversation_id
        
        try:
            # Determine agent assignment (your existing logic)
            assigned_agent_id = await self._assign_agent_for_request(user_input)
            
            if assigned_agent_id:
                # Log agent assignment
                event = create_event(
                    agent_id=self.agent_id,
                    event_type=EventType.PROCESS,
                    message=f"Assigned to {assigned_agent_id}",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(event)
                
                # Delegate to assigned agent with debug tracking
                response = await self._delegate_to_agent(assigned_agent_id, user_input, conversation_context)
                
            else:
                # Handle directly
                event = create_event(
                    agent_id=self.agent_id,
                    event_type=EventType.PROCESS,
                    message="Handling request directly",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(event)
                
                response = await self._handle_request_directly(user_input, conversation_context)
            
            return response
            
        except Exception as e:
            error_msg = f"Orchestration error: {str(e)}"
            self.agent_tracker.record_error(self.agent_id, error_msg, conversation_id)
            raise
    '''
    
    return method_code


def patch_delegate_to_agent():
    """
    Enhanced delegation method with debug tracking
    """
    
    method_code = '''
    async def _delegate_to_agent(self, agent_id: str, user_input: str, conversation_context: ConversationContext) -> str:
        """
        Delegate request to specific agent with debug tracking
        """
        
        conversation_id = conversation_context.conversation_id
        
        try:
            # Check agent availability
            if agent_id not in self.available_agents:
                error_msg = f"Agent {agent_id} not available"
                self.agent_tracker.record_error(self.agent_id, error_msg, conversation_id)
                return "The requested service is currently unavailable. Please try again later."
            
            agent_info = self.available_agents[agent_id]
            
            # Update agent state to busy (if you track individual agents)
            # self.agent_tracker.update_agent_status(agent_id, AgentStatus.BUSY, f"Processing request from {self.agent_id}")
            
            # Log delegation
            event = create_event(
                agent_id=self.agent_id,
                event_type=EventType.PROCESS,
                message=f"Delegating to {agent_id}: {user_input[:50]}...",
                conversation_id=conversation_id
            )
            self.debug_system.record_event(event)
            
            # Call the agent (your existing logic)
            # This is where you'd call your actual agent implementation
            # For example:
            # if agent_info.agent_type == "sample_tracker":
            #     response = await self._call_sample_tracker(user_input, conversation_context)
            # elif agent_info.agent_type == "analysis_agent":
            #     response = await self._call_analysis_agent(user_input, conversation_context)
            # else:
            #     response = await self._call_generic_agent(agent_id, user_input, conversation_context)
            
            # Placeholder response (replace with your actual agent calls)
            response = f"Response from {agent_id}: Processed '{user_input}'"
            
            # Log successful delegation
            event = create_event(
                agent_id=self.agent_id,
                event_type=EventType.PROCESS,
                message=f"Received response from {agent_id}",
                conversation_id=conversation_id
            )
            self.debug_system.record_event(event)
            
            return response
            
        except Exception as e:
            error_msg = f"Delegation to {agent_id} failed: {str(e)}"
            self.agent_tracker.record_error(self.agent_id, error_msg, conversation_id)
            return f"I couldn't complete your request through the {agent_id} service. Please try rephrasing your request."
    '''
    
    return method_code


# ============================================================================
# COMPLETE INTEGRATION EXAMPLE
# ============================================================================

def create_complete_debug_patch():
    """
    Create a complete patch file you can apply to your MainInterfaceAgent
    """
    
    patch_content = f'''
# ============================================================================
# STEP 1: Add imports to the top of your main_interface_agent.py file
# ============================================================================

# Add these imports after your existing imports:
import time
import uuid
from backend.app.debug import (
    get_debug_system, get_agent_tracker, 
    EventType, AgentStatus, create_event
)

# ============================================================================
# STEP 2: Modify your MainInterfaceAgent.__init__ method
# ============================================================================

# Add this code to the end of your __init__ method:

        # Initialize debug system
        self.debug_system = get_debug_system()
        self.agent_tracker = get_agent_tracker()
        
        # Register this agent
        self.agent_id = "main_interface_agent"
        self.agent_tracker.register_agent(self.agent_id, "main_interface")
        
        # Set up monitoring
        self.agent_tracker.add_state_change_callback(self._on_agent_state_change)
        
        self.logger.info("MainInterfaceAgent debug system initialized")

# ============================================================================
# STEP 3: Add these new methods to your MainInterfaceAgent class
# ============================================================================

    def _on_agent_state_change(self, agent_id: str, new_state):
        """Monitor agent state changes for debugging"""
        self.logger.info(f"Agent {{agent_id}} state: {{new_state.status.value}}")
        
        if new_state.status == AgentStatus.ERROR:
            self.logger.warning(f"🚨 Agent {{agent_id}} in ERROR state!")
            
            # Get recent events for analysis
            recent_events = self.debug_system.get_recent_events(5)
            agent_events = [e for e in recent_events if e.agent_id == agent_id]
            
            for event in agent_events[-3:]:
                self.logger.warning(f"  📋 {{event.event_type.value}}: {{event.message}}")
    
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
        ]
        return any(indicators)

# ============================================================================
# STEP 4: Replace your existing process_user_request method with this version
# ============================================================================

{patch_process_user_request()}

# ============================================================================
# STEP 5: Enhance your orchestration methods (optional but recommended)
# ============================================================================

{patch_orchestrate_user_request()}

{patch_delegate_to_agent()}
'''
    
    return patch_content


if __name__ == "__main__":
    print("🔧 MainInterfaceAgent Debug Integration Patch")
    print("=" * 50)
    
    print("This file contains the modifications needed to add debug system")
    print("support to your existing MainInterfaceAgent.")
    print()
    print("Choose an option:")
    print("1. Show complete integration patch")
    print("2. Show individual method patches")
    print("3. Generate patch file")
    
    choice = input("Enter choice (1-3): ").strip()
    
    if choice == "1":
        print("\n" + "=" * 70)
        print("COMPLETE INTEGRATION PATCH")
        print("=" * 70)
        print(create_complete_debug_patch())
        
    elif choice == "2":
        print("\n🔧 INDIVIDUAL METHOD PATCHES:")
        print("\n1. process_user_request method:")
        print(patch_process_user_request())
        print("\n2. _orchestrate_user_request method:")
        print(patch_orchestrate_user_request())
        print("\n3. _delegate_to_agent method:")
        print(patch_delegate_to_agent())
        
    elif choice == "3":
        # Write patch to file
        with open("/Users/capanema/Projects/alims/main_interface_agent_debug_patch.txt", "w") as f:
            f.write(create_complete_debug_patch())
        print("✅ Patch file created: main_interface_agent_debug_patch.txt")
        
    else:
        print("Showing quick example by default...")
        print(patch_process_user_request()[:500] + "...")
