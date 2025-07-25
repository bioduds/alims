#!/usr/bin/env python3
"""
Debug System Integration Guide for ALIMS
Step-by-step integration with your existing agents

This guide shows how to integrate the TLA+ verified debug system
with your existing ALIMS agents to resolve "crazy talk" issues.
"""

from backend.app.debug import (
    get_debug_system, get_agent_tracker, get_websocket_handler,
    EventType, AgentStatus, create_event
)

# ============================================================================
# STEP 1: MODIFY YOUR MAIN INTERFACE AGENT
# ============================================================================

def integrate_debug_into_main_interface_agent():
    """
    Add this code to your MainInterfaceAgent class initialization
    """
    
    # In MainInterfaceAgent.__init__():
    example_init_code = '''
    class MainInterfaceAgent:
        def __init__(self, config: Dict[str, Any]):
            # Existing initialization code...
            self.config = config
            self.conversations = {}
            self.agents = {}
            
            # ADD DEBUG SYSTEM INTEGRATION
            self.debug_system = get_debug_system()
            self.agent_tracker = get_agent_tracker()
            
            # Register this agent with debug system
            agent_id = "main_interface_agent"
            self.agent_id = agent_id
            self.agent_tracker.register_agent(agent_id, "main_interface")
            
            # Set up state change monitoring for all agents
            self.agent_tracker.add_state_change_callback(self._on_agent_state_change)
            
            logger.info(f"MainInterfaceAgent {agent_id} registered with debug system")
    '''
    
    # Add state change callback method:
    state_change_callback = '''
    def _on_agent_state_change(self, agent_id: str, new_state):
        """Callback for monitoring agent state changes"""
        logger.info(f"Agent {agent_id} state changed to {new_state.status.value}")
        
        # Log potential issues
        if new_state.status == AgentStatus.ERROR:
            logger.warning(f"Agent {agent_id} entered ERROR state - investigating...")
            
            # Get recent events for this agent
            recent_events = self.debug_system.get_recent_events(10)
            agent_events = [e for e in recent_events if e.agent_id == agent_id]
            
            for event in agent_events[-3:]:  # Last 3 events
                logger.warning(f"  Recent event: {event.event_type.value} - {event.message}")
    '''
    
    return example_init_code, state_change_callback


# ============================================================================
# STEP 2: ADD DEBUG TRACKING TO MESSAGE PROCESSING
# ============================================================================

def integrate_debug_into_message_processing():
    """
    Add debug tracking to your message processing methods
    """
    
    # Modify your process_user_request method:
    process_request_example = '''
    async def process_user_request(self, user_input: str, conversation_id: str = None) -> str:
        """Process user request with debug tracking"""
        
        # CREATE CONVERSATION ID IF NEEDED
        if conversation_id is None:
            conversation_id = f"conv_{uuid.uuid4().hex[:8]}"
        
        # START DEBUG TRACKING
        self.agent_tracker.start_conversation(self.agent_id, conversation_id)
        self.agent_tracker.record_message_received(
            self.agent_id, 
            f"User request: {user_input[:100]}...", 
            conversation_id
        )
        
        try:
            # Update status to busy
            self.agent_tracker.update_agent_status(
                self.agent_id, 
                AgentStatus.BUSY, 
                "Processing user request"
            )
            
            start_time = time.time()
            
            # YOUR EXISTING PROCESSING LOGIC HERE
            # ... (your current agent assignment, orchestration logic)
            
            # Example of tracking sub-agent calls:
            if assigned_agent_id:
                # Track when delegating to sub-agent
                event = create_event(
                    agent_id=self.agent_id,
                    event_type=EventType.PROCESS,
                    message=f"Delegating to {assigned_agent_id}",
                    conversation_id=conversation_id
                )
                self.debug_system.record_event(event)
            
            # Process and get response
            response = await self._orchestrate_response(user_input, conversation_id)
            
            # RECORD SUCCESSFUL RESPONSE
            processing_time = time.time() - start_time
            self.agent_tracker.record_message_response(
                self.agent_id, 
                f"Response: {response[:100]}...", 
                processing_time,
                conversation_id
            )
            
            # Update status back to ready
            self.agent_tracker.update_agent_status(
                self.agent_id, 
                AgentStatus.READY, 
                "Request completed successfully"
            )
            
            return response
            
        except Exception as e:
            # RECORD ERROR
            error_msg = f"Error processing request: {str(e)}"
            self.agent_tracker.record_error(self.agent_id, error_msg, conversation_id)
            
            # Log the error with context
            logger.error(f"MainInterfaceAgent error: {error_msg}")
            
            # Return user-friendly error message
            return "I apologize, but I encountered an error processing your request. Please try again."
        
        finally:
            # End conversation tracking
            self.agent_tracker.end_conversation(self.agent_id, conversation_id)
    '''
    
    return process_request_example


# ============================================================================
# STEP 3: ADD DEBUG TRACKING TO SUB-AGENTS
# ============================================================================

def integrate_debug_into_sub_agents():
    """
    Add debug tracking to specialized agents (chat, analysis, etc.)
    """
    
    # For each specialized agent class:
    sub_agent_example = '''
    class ChatAgent:  # or AnalysisAgent, etc.
        def __init__(self, agent_id: str, agent_type: str = "chat"):
            # Existing initialization...
            
            # ADD DEBUG INTEGRATION
            self.agent_id = agent_id
            self.agent_tracker = get_agent_tracker()
            self.debug_system = get_debug_system()
            
            # Register with debug system
            self.agent_tracker.register_agent(agent_id, agent_type)
            
        async def process_message(self, message: str, conversation_id: str = None) -> str:
            """Process message with full debug tracking"""
            
            # Record incoming message
            self.agent_tracker.record_message_received(
                self.agent_id, 
                message, 
                conversation_id
            )
            
            # Update status
            self.agent_tracker.update_agent_status(
                self.agent_id, 
                AgentStatus.BUSY, 
                f"Processing: {message[:50]}..."
            )
            
            start_time = time.time()
            
            try:
                # YOUR EXISTING PROCESSING LOGIC
                response = await self._generate_response(message)
                
                # CHECK FOR "CRAZY TALK" PATTERNS
                if self._detect_crazy_talk(response):
                    # Record the issue
                    self.agent_tracker.record_error(
                        self.agent_id,
                        f"Crazy talk detected in response: {response[:100]}...",
                        conversation_id
                    )
                    
                    # Try to regenerate
                    response = await self._regenerate_safe_response(message)
                
                # Record successful response
                processing_time = time.time() - start_time
                self.agent_tracker.record_message_response(
                    self.agent_id, 
                    response, 
                    processing_time,
                    conversation_id
                )
                
                # Update status to ready
                self.agent_tracker.update_agent_status(
                    self.agent_id, 
                    AgentStatus.READY, 
                    "Message processed successfully"
                )
                
                return response
                
            except Exception as e:
                # Record error
                self.agent_tracker.record_error(
                    self.agent_id, 
                    f"Processing error: {str(e)}", 
                    conversation_id
                )
                
                # Return safe fallback
                return "I'm sorry, I couldn't process that request properly."
        
        def _detect_crazy_talk(self, response: str) -> bool:
            """Detect potential crazy talk patterns"""
            crazy_patterns = [
                "banana elephant quantum",  # nonsensical combinations
                "NULL_POINTER_EXCEPTION",   # code errors in responses
                "recursive loop",           # infinite loop indicators
                len(response.split()) > 200,  # extremely long responses
                response.count("and") > 10,   # repetitive connectors
            ]
            
            return any(
                pattern in response.lower() if isinstance(pattern, str) else pattern
                for pattern in crazy_patterns
            )
    '''
    
    return sub_agent_example


# ============================================================================
# STEP 4: SET UP REAL-TIME MONITORING DASHBOARD
# ============================================================================

def setup_debug_dashboard():
    """
    Set up real-time monitoring for your debug system
    """
    
    dashboard_code = '''
    import asyncio
    import json
    from backend.app.debug import get_websocket_handler, get_debug_system, get_agent_tracker
    
    async def start_debug_monitoring():
        """Start real-time debug monitoring"""
        
        debug_system = get_debug_system()
        agent_tracker = get_agent_tracker()
        websocket_handler = get_websocket_handler()
        
        print("🔍 Starting ALIMS Debug Monitor...")
        print("="*50)
        
        # Set up monitoring callbacks
        def on_agent_error(agent_id: str, agent_state):
            if agent_state.status == AgentStatus.ERROR:
                print(f"🚨 ALERT: Agent {agent_id} in ERROR state!")
                
                # Get recent events for analysis
                recent_events = debug_system.get_recent_events(5)
                error_events = [e for e in recent_events if e.agent_id == agent_id and e.event_type == EventType.ERROR]
                
                if error_events:
                    latest_error = error_events[-1]
                    print(f"   Error: {latest_error.message}")
                    print(f"   Time: {datetime.fromtimestamp(latest_error.timestamp)}")
        
        agent_tracker.add_state_change_callback(on_agent_error)
        
        # Monitor system stats
        while True:
            stats = debug_system.get_system_stats()
            agent_summary = agent_tracker.get_agent_summary()
            
            print(f"\\n📊 System Status: {stats['system_status']}")
            print(f"   Events: {stats['total_events']}/{stats['max_events']} ({stats['memory_usage_pct']:.1f}%)")
            print(f"   Agents: {agent_summary['total_agents']} active")
            print(f"   Conversations: {agent_summary['active_conversations']} ongoing")
            
            # Check for agents in error state
            error_agents = [
                agent_id for agent_id, info in agent_summary['agents'].items()
                if info.get('status') == 'ERROR'
            ]
            
            if error_agents:
                print(f"🚨 Agents in ERROR state: {', '.join(error_agents)}")
            
            await asyncio.sleep(10)  # Update every 10 seconds
    
    # Run the monitor
    if __name__ == "__main__":
        asyncio.run(start_debug_monitoring())
    '''
    
    return dashboard_code


# ============================================================================
# STEP 5: CREATE STARTUP SCRIPT
# ============================================================================

def create_startup_integration():
    """
    Create startup script to initialize debug system with your existing app
    """
    
    startup_code = '''
    #!/usr/bin/env python3
    """
    ALIMS Debug-Enabled Startup Script
    Initializes all agents with debug system integration
    """
    
    import asyncio
    import logging
    from backend.app.debug import get_debug_system, get_agent_tracker
    from backend.app.intelligence.main_interface_agent import MainInterfaceAgent
    # Import your other agents here...
    
    async def initialize_alims_with_debug():
        """Initialize ALIMS with full debug system integration"""
        
        # Initialize debug system first
        debug_system = get_debug_system()
        agent_tracker = get_agent_tracker()
        
        print("🚀 Initializing ALIMS with Debug System...")
        
        # Initialize main interface agent
        main_agent = MainInterfaceAgent(config={})
        
        # Initialize other agents with debug integration
        # chat_agent = ChatAgent("chat_agent_1", "chat")
        # analysis_agent = AnalysisAgent("analysis_agent_1", "analysis")
        
        print(f"✅ Debug system initialized:")
        stats = debug_system.get_system_stats()
        summary = agent_tracker.get_agent_summary()
        
        print(f"   System status: {stats['system_status']}")
        print(f"   Registered agents: {summary['total_agents']}")
        print(f"   Memory bounds: {stats['max_events']} events, {stats['max_agents']} agents")
        
        print("\\n🔍 Debug system ready to trace agent interactions!")
        print("   All 'crazy talk' will be automatically detected and logged.")
        
        return main_agent
    
    if __name__ == "__main__":
        main_agent = asyncio.run(initialize_alims_with_debug())
        
        # Start your main application loop here
        # For example:
        # await main_agent.start_processing_loop()
    '''
    
    return startup_code


# ============================================================================
# COMPLETE INTEGRATION EXAMPLE
# ============================================================================

def show_complete_integration_example():
    """Show a complete example of integrated agent"""
    
    print("="*70)
    print("🔧 COMPLETE INTEGRATION EXAMPLE")
    print("="*70)
    
    complete_example = '''
    """
    Example: Debug-Enabled Chat Agent
    """
    
    import time
    import uuid
    from backend.app.debug import (
        get_debug_system, get_agent_tracker, 
        EventType, AgentStatus, create_event
    )
    
    class DebugEnabledChatAgent:
        def __init__(self, agent_id: str = None):
            # Generate agent ID if not provided
            self.agent_id = agent_id or f"chat_agent_{uuid.uuid4().hex[:8]}"
            
            # Initialize debug system
            self.debug_system = get_debug_system()
            self.agent_tracker = get_agent_tracker()
            
            # Register with debug system
            self.agent_tracker.register_agent(self.agent_id, "chat")
            
            print(f"🤖 ChatAgent {self.agent_id} initialized with debug tracking")
        
        async def chat(self, user_message: str, conversation_id: str = None) -> str:
            """Main chat method with full debug integration"""
            
            # Generate conversation ID if needed
            if conversation_id is None:
                conversation_id = f"conv_{uuid.uuid4().hex[:8]}"
            
            # Start conversation tracking
            self.agent_tracker.start_conversation(self.agent_id, conversation_id)
            
            # Record incoming message
            self.agent_tracker.record_message_received(
                self.agent_id, 
                user_message, 
                conversation_id
            )
            
            # Update status to busy
            self.agent_tracker.update_agent_status(
                self.agent_id, 
                AgentStatus.BUSY, 
                f"Processing: {user_message[:30]}..."
            )
            
            start_time = time.time()
            
            try:
                # Generate response (your existing logic)
                response = await self._generate_response(user_message)
                
                # Check for crazy talk
                if self._is_crazy_talk(response):
                    # Record the issue
                    self.agent_tracker.record_error(
                        self.agent_id,
                        f"Crazy talk detected: {response[:50]}...",
                        conversation_id
                    )
                    
                    # Generate safer response
                    response = "I apologize, but I need to rephrase my response. Could you please repeat your question?"
                
                # Record successful response
                processing_time = time.time() - start_time
                self.agent_tracker.record_message_response(
                    self.agent_id, 
                    response, 
                    processing_time,
                    conversation_id
                )
                
                # Update status to ready
                self.agent_tracker.update_agent_status(
                    self.agent_id, 
                    AgentStatus.READY, 
                    "Response completed"
                )
                
                return response
                
            except Exception as e:
                # Record error
                error_msg = f"Chat processing error: {str(e)}"
                self.agent_tracker.record_error(self.agent_id, error_msg, conversation_id)
                
                return "I'm sorry, I encountered an error. Please try again."
            
            finally:
                # End conversation tracking
                self.agent_tracker.end_conversation(self.agent_id, conversation_id)
        
        async def _generate_response(self, message: str) -> str:
            """Your existing response generation logic"""
            # Simulate response generation
            await asyncio.sleep(0.1)  # Simulate processing time
            return f"Response to: {message}"
        
        def _is_crazy_talk(self, response: str) -> bool:
            """Detect crazy talk patterns"""
            indicators = [
                len(response) > 500,  # Too long
                "banana elephant" in response.lower(),  # Nonsensical
                response.count("and") > 8,  # Too repetitive
                "ERROR" in response and "Exception" in response,  # Code leakage
            ]
            return any(indicators)
    
    # Usage example:
    async def demo_debug_enabled_agent():
        agent = DebugEnabledChatAgent()
        
        # Normal conversation
        response1 = await agent.chat("Hello, how are you?")
        print(f"Response: {response1}")
        
        # This would trigger crazy talk detection
        # (if your response generation went wrong)
        
        # Check agent activity
        activity = agent.agent_tracker.get_agent_activity(agent.agent_id)
        print(f"Agent activity: {activity.total_messages} messages, {activity.error_count} errors")
    '''
    
    print(complete_example)
    return complete_example


if __name__ == "__main__":
    print("🔧 ALIMS DEBUG SYSTEM INTEGRATION GUIDE")
    print("="*70)
    
    print("\\n1. 🏗️  MODIFY YOUR MAIN INTERFACE AGENT:")
    init_code, callback_code = integrate_debug_into_main_interface_agent()
    print("   Add to __init__():", init_code[:200] + "...")
    print("   Add callback method:", callback_code[:200] + "...")
    
    print("\\n2. 📨 ADD DEBUG TO MESSAGE PROCESSING:")
    process_code = integrate_debug_into_message_processing()
    print("   Modify process_user_request():", process_code[:200] + "...")
    
    print("\\n3. 🤖 INTEGRATE SUB-AGENTS:")
    sub_agent_code = integrate_debug_into_sub_agents()
    print("   Add to each agent class:", sub_agent_code[:200] + "...")
    
    print("\\n4. 📊 SET UP MONITORING:")
    dashboard_code = setup_debug_dashboard()
    print("   Create monitoring script:", dashboard_code[:200] + "...")
    
    print("\\n5. 🚀 CREATE STARTUP SCRIPT:")
    startup_code = create_startup_integration()
    print("   Create main startup:", startup_code[:200] + "...")
    
    print("\\n" + "="*70)
    show_complete_integration_example()
