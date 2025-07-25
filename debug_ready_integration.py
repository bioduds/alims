#!/usr/bin/env python3
"""
ALIMS Debug System Integration - Practical Implementation
Ready-to-use integration for your existing agents

This file provides the actual code modifications needed to add debug system
support to your MainInterfaceAgent and resolve "crazy talk" issues.
"""

import time
import uuid
import asyncio
import logging
from typing import Dict, Any, Optional
from backend.app.debug import (
    get_debug_system, get_agent_tracker, get_websocket_handler,
    EventType, AgentStatus, create_event
)

logger = logging.getLogger(__name__)


class DebugMixin:
    """
    Mixin class to add debug capabilities to any agent
    Just inherit from this class to get full debug integration
    """
    
    def __init_debug__(self, agent_id: str, agent_type: str = "generic"):
        """Initialize debug system for this agent"""
        self.agent_id = agent_id
        self.debug_system = get_debug_system()
        self.agent_tracker = get_agent_tracker()
        
        # Register with debug system
        self.agent_tracker.register_agent(agent_id, agent_type)
        logger.info(f"Agent {agent_id} registered with debug system")
    
    def debug_start_conversation(self, conversation_id: str):
        """Start tracking a conversation"""
        self.agent_tracker.start_conversation(self.agent_id, conversation_id)
    
    def debug_end_conversation(self, conversation_id: str):
        """End tracking a conversation"""
        self.agent_tracker.end_conversation(self.agent_id, conversation_id)
    
    def debug_record_message_received(self, message: str, conversation_id: str = None):
        """Record that this agent received a message"""
        self.agent_tracker.record_message_received(self.agent_id, message, conversation_id)
    
    def debug_record_response(self, response: str, processing_time: float, conversation_id: str = None):
        """Record that this agent sent a response"""
        self.agent_tracker.record_message_response(self.agent_id, response, processing_time, conversation_id)
    
    def debug_record_error(self, error_message: str, conversation_id: str = None):
        """Record an error for this agent"""
        self.agent_tracker.record_error(self.agent_id, error_message, conversation_id)
    
    def debug_update_status(self, status: AgentStatus, message: str = ""):
        """Update agent status"""
        self.agent_tracker.update_agent_status(self.agent_id, status, message)
    
    def debug_check_crazy_talk(self, response: str) -> bool:
        """Check if response contains crazy talk patterns"""
        indicators = [
            len(response) > 1000,  # Extremely long responses
            "banana elephant quantum" in response.lower(),  # Nonsensical combinations
            "NULL_POINTER_EXCEPTION" in response,  # Code errors leaking through
            "TypeError:" in response,  # Python errors in response
            "recursive loop" in response.lower(),  # Loop issues
            response.count("and") > 15,  # Excessive repetition
            response.count("the") > 30,  # Excessive repetition
            len(response.split()) > 300,  # Too many words
            response.count("...") > 5,  # Too many ellipses
        ]
        
        return any(indicators)


class DebugEnabledMainInterfaceAgent(DebugMixin):
    """
    Enhanced MainInterfaceAgent with full debug integration
    
    This is a wrapper that adds debug capabilities to your existing agent.
    You can either modify your existing agent or use this as a template.
    """
    
    def __init__(self, config: Dict[str, Any]):
        # Initialize debug system first
        self.__init_debug__("main_interface_agent", "main_interface")
        
        # Your existing initialization code here
        self.config = config
        self.conversations = {}
        self.agents = {}
        
        # Set up monitoring for all agent state changes
        self.agent_tracker.add_state_change_callback(self._on_agent_state_change)
        
        logger.info("MainInterfaceAgent initialized with debug capabilities")
    
    def _on_agent_state_change(self, agent_id: str, new_state):
        """Monitor all agent state changes for issues"""
        logger.info(f"Agent {agent_id} -> {new_state.status.value}")
        
        if new_state.status == AgentStatus.ERROR:
            logger.warning(f"🚨 Agent {agent_id} in ERROR state - investigating...")
            
            # Get recent events for analysis
            recent_events = self.debug_system.get_recent_events(5)
            agent_events = [e for e in recent_events if e.agent_id == agent_id]
            
            for event in agent_events[-3:]:
                logger.warning(f"  📋 {event.event_type.value}: {event.message}")
    
    async def process_user_request_with_debug(self, user_input: str, conversation_id: str = None) -> str:
        """
        Process user request with full debug tracking
        Replace your existing process_user_request with this method
        """
        
        # Generate conversation ID if needed
        if conversation_id is None:
            conversation_id = f"conv_{uuid.uuid4().hex[:8]}"
        
        # Start debug tracking
        self.debug_start_conversation(conversation_id)
        self.debug_record_message_received(f"User: {user_input[:100]}...", conversation_id)
        self.debug_update_status(AgentStatus.BUSY, "Processing user request")
        
        start_time = time.time()
        
        try:
            # Log processing start
            event = create_event(
                agent_id=self.agent_id,
                event_type=EventType.PROCESS,
                message=f"Starting to process: {user_input[:50]}...",
                conversation_id=conversation_id
            )
            self.debug_system.record_event(event)
            
            # YOUR EXISTING PROCESSING LOGIC GOES HERE
            # For example:
            response = await self._orchestrate_response(user_input, conversation_id)
            
            # Check for crazy talk
            if self.debug_check_crazy_talk(response):
                self.debug_record_error(f"Crazy talk detected: {response[:100]}...", conversation_id)
                response = "I apologize, but I need to rephrase my response. Could you please try again?"
            
            # Record successful response
            processing_time = time.time() - start_time
            self.debug_record_response(f"Response: {response[:100]}...", processing_time, conversation_id)
            self.debug_update_status(AgentStatus.READY, "Request completed successfully")
            
            return response
            
        except Exception as e:
            # Record error with full context
            error_msg = f"Error processing '{user_input[:50]}...': {str(e)}"
            self.debug_record_error(error_msg, conversation_id)
            
            logger.error(f"MainInterfaceAgent error: {error_msg}")
            return "I apologize, but I encountered an error processing your request. Please try again."
        
        finally:
            # End conversation tracking
            self.debug_end_conversation(conversation_id)
    
    async def _orchestrate_response(self, user_input: str, conversation_id: str) -> str:
        """
        Replace this with your actual orchestration logic
        This is just a placeholder showing how to add debug tracking
        """
        
        # Example: Determine which agent to use
        if "data analysis" in user_input.lower():
            assigned_agent = "analysis_agent"
        elif "chat" in user_input.lower():
            assigned_agent = "chat_agent"
        else:
            assigned_agent = "general_agent"
        
        # Log agent assignment
        event = create_event(
            agent_id=self.agent_id,
            event_type=EventType.PROCESS,
            message=f"Assigned to {assigned_agent}",
            conversation_id=conversation_id
        )
        self.debug_system.record_event(event)
        
        # Simulate processing (replace with your actual logic)
        await asyncio.sleep(0.1)
        return f"Processed by {assigned_agent}: {user_input}"


class DebugEnabledChatAgent(DebugMixin):
    """
    Example of a specialized agent with debug integration
    Use this as a template for your other agents
    """
    
    def __init__(self, agent_id: str = None):
        # Generate agent ID if not provided
        agent_id = agent_id or f"chat_agent_{uuid.uuid4().hex[:8]}"
        
        # Initialize debug system
        self.__init_debug__(agent_id, "chat")
        
        # Your existing initialization here
        self.context_memory = []
        
        logger.info(f"ChatAgent {agent_id} initialized with debug tracking")
    
    async def process_message(self, message: str, conversation_id: str = None) -> str:
        """Process a chat message with full debug tracking"""
        
        # Generate conversation ID if needed
        if conversation_id is None:
            conversation_id = f"conv_{uuid.uuid4().hex[:8]}"
        
        # Debug tracking
        self.debug_start_conversation(conversation_id)
        self.debug_record_message_received(message, conversation_id)
        self.debug_update_status(AgentStatus.BUSY, f"Processing: {message[:30]}...")
        
        start_time = time.time()
        
        try:
            # Your existing message processing logic
            response = await self._generate_chat_response(message)
            
            # Check for crazy talk
            if self.debug_check_crazy_talk(response):
                self.debug_record_error(f"Crazy talk detected: {response[:50]}...", conversation_id)
                response = "I need to think about that differently. Could you rephrase your question?"
            
            # Record successful response
            processing_time = time.time() - start_time
            self.debug_record_response(response, processing_time, conversation_id)
            self.debug_update_status(AgentStatus.READY, "Message processed")
            
            return response
            
        except Exception as e:
            error_msg = f"Chat processing error: {str(e)}"
            self.debug_record_error(error_msg, conversation_id)
            return "I'm sorry, I encountered an error. Please try again."
        
        finally:
            self.debug_end_conversation(conversation_id)
    
    async def _generate_chat_response(self, message: str) -> str:
        """Your existing chat response generation logic"""
        # Placeholder - replace with your actual logic
        await asyncio.sleep(0.1)
        return f"Chat response to: {message}"


# ============================================================================
# MONITORING DASHBOARD
# ============================================================================

async def start_debug_monitoring_dashboard():
    """
    Real-time monitoring dashboard for your debug system
    Run this in a separate terminal to monitor your agents
    """
    
    debug_system = get_debug_system()
    agent_tracker = get_agent_tracker()
    
    print("🔍 ALIMS Debug Monitor Started")
    print("="*50)
    
    # Set up error monitoring
    def on_agent_error(agent_id: str, agent_state):
        if agent_state.status == AgentStatus.ERROR:
            print(f"🚨 ALERT: {agent_id} in ERROR state!")
            
            # Get recent activity
            activity = agent_tracker.get_agent_activity(agent_id)
            print(f"   Last error: {activity.last_error}")
            print(f"   Error count: {activity.error_count}")
            print(f"   Response time: {activity.avg_response_time:.2f}s")
    
    agent_tracker.add_state_change_callback(on_agent_error)
    
    # Monitoring loop
    while True:
        try:
            # Get system statistics
            stats = debug_system.get_system_stats()
            summary = agent_tracker.get_agent_summary()
            
            # Clear screen and show status
            print("\033[2J\033[H")  # Clear screen
            print("🔍 ALIMS DEBUG MONITOR")
            print("=" * 50)
            print(f"📊 System: {stats['system_status']}")
            print(f"📈 Events: {stats['total_events']}/{stats['max_events']} ({stats['memory_usage_pct']:.1f}%)")
            print(f"🤖 Agents: {summary['total_agents']} registered")
            print(f"💬 Conversations: {summary['active_conversations']} active")
            
            # Show agent status
            print("\n🤖 AGENT STATUS:")
            for agent_id, info in summary['agents'].items():
                status_icon = "🟢" if info.get('status') == 'READY' else "🔴" if info.get('status') == 'ERROR' else "🟡"
                print(f"   {status_icon} {agent_id}: {info.get('status', 'UNKNOWN')}")
            
            # Show recent errors
            recent_events = debug_system.get_recent_events(5)
            error_events = [e for e in recent_events if e.event_type == EventType.ERROR]
            
            if error_events:
                print("\n🚨 RECENT ERRORS:")
                for event in error_events[-3:]:
                    print(f"   ❌ {event.agent_id}: {event.message}")
            
            print(f"\nLast updated: {time.strftime('%H:%M:%S')}")
            print("Press Ctrl+C to stop monitoring")
            
            await asyncio.sleep(2)  # Update every 2 seconds
            
        except KeyboardInterrupt:
            print("\n👋 Debug monitoring stopped")
            break
        except Exception as e:
            print(f"Monitoring error: {e}")
            await asyncio.sleep(5)


# ============================================================================
# QUICK START EXAMPLE
# ============================================================================

async def quick_start_example():
    """
    Quick example showing how to use the debug-enabled agents
    """
    
    print("🚀 ALIMS Debug System Quick Start")
    print("=" * 40)
    
    # Initialize main agent
    main_agent = DebugEnabledMainInterfaceAgent(config={})
    
    # Initialize chat agent
    chat_agent = DebugEnabledChatAgent()
    
    # Example conversation
    print("\n💬 Testing normal conversation:")
    response1 = await main_agent.process_user_request_with_debug("Hello, how can you help me?")
    print(f"Response: {response1}")
    
    print("\n💬 Testing chat agent:")
    response2 = await chat_agent.process_message("What's the weather like?")
    print(f"Chat response: {response2}")
    
    # Show debug statistics
    print("\n📊 Debug Statistics:")
    stats = main_agent.debug_system.get_system_stats()
    summary = main_agent.agent_tracker.get_agent_summary()
    
    print(f"   Events recorded: {stats['total_events']}")
    print(f"   Agents active: {summary['total_agents']}")
    
    # Show agent activities
    for agent_id in [main_agent.agent_id, chat_agent.agent_id]:
        activity = main_agent.agent_tracker.get_agent_activity(agent_id)
        print(f"   {agent_id}: {activity.total_messages} messages, {activity.error_count} errors")


if __name__ == "__main__":
    print("Choose an option:")
    print("1. Run quick start example")
    print("2. Start monitoring dashboard")
    
    choice = input("Enter choice (1 or 2): ").strip()
    
    if choice == "1":
        asyncio.run(quick_start_example())
    elif choice == "2":
        asyncio.run(start_debug_monitoring_dashboard())
    else:
        print("Running quick start example by default...")
        asyncio.run(quick_start_example())
