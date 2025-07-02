"""
CelFlow Enhanced User Interface Agent
Integrates with the new tool system and workflow orchestrator for smarter responses
"""

import logging
from typing import Dict, Any, List, Optional
from datetime import datetime
from pathlib import Path

from .enhanced_tool_system import (
    ToolRegistry, 
    WebSearchTool, 
    CodeExecutionTool, 
    ToolCategory
)
from .enhanced_agent_workflow import EnhancedAgentWorkflow
from ..intelligence.duckduckgo_search import web_search
from .simple_algorithm_executor import SimpleAlgorithmExecutor

logger = logging.getLogger(__name__)


class EnhancedUserInterfaceAgent:
    """Enhanced User Interface Agent with tool calling and workflow capabilities"""
    
    def __init__(self, central_brain):
        self.central_brain = central_brain
        self.interaction_count = 0
        self.user_preferences = {}
        self.conversation_patterns = {}
        
        # Initialize enhanced components
        self.tool_registry = ToolRegistry()
        self.workflow_engine = None  # Will be initialized after ollama_client is ready
        self.simple_executor = SimpleAlgorithmExecutor()
        
        # Register default tools
        self._register_default_tools()
        
        logger.info("Enhanced UserInterfaceAgent initialized")
    
    def initialize_workflow_engine(self):
        """Initialize the workflow engine after ollama_client is ready"""
        if self.central_brain.ollama_client and not self.workflow_engine:
            self.workflow_engine = EnhancedAgentWorkflow(
                self.tool_registry, 
                self.central_brain.ollama_client
            )
            logger.info("Workflow engine initialized")
    
    def _register_default_tools(self):
        """Register the default set of tools"""
        
        # Web Search Tool
        web_search_tool = WebSearchTool(web_search)
        self.tool_registry.register_tool(web_search_tool)
        
        # Code Execution Tool  
        code_execution_tool = CodeExecutionTool(self.simple_executor)
        self.tool_registry.register_tool(code_execution_tool)
        
        logger.info("Default tools registered")
    
    async def process_chat_message(self, 
                                   message: str, 
                                   context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Process chat message through enhanced workflow system"""
        
        start_time = datetime.now()
        self.interaction_count += 1
        
        try:
            # Initialize workflow engine if not already done
            self.initialize_workflow_engine()
            
            if not self.workflow_engine:
                logger.warning("Workflow engine not available, falling back to basic mode")
                return await self._fallback_basic_response(message, context)
            
            # Prepare interaction context
            interaction_context = await self._build_interaction_context(message, context)
            
            # Process through enhanced workflow system
            result = await self.workflow_engine.process_user_request(
                user_message=message,
                context=interaction_context
            )
            
            # Learn from interaction
            await self._learn_from_enhanced_interaction(message, result, interaction_context)
            
            # Calculate response time
            response_time = (datetime.now() - start_time).total_seconds()
            
            # Enhance result with metadata
            enhanced_result = {
                **result,
                "agent": "enhanced_user_interface",
                "interaction_id": self.interaction_count,
                "response_time": response_time,
                "context_used": interaction_context is not None,
                "enhanced_mode": True
            }
            
            return enhanced_result
            
        except Exception as e:
            logger.error(f"Enhanced processing failed: {e}")
            # Fallback to basic processing
            return await self._fallback_basic_response(message, context)
    
    async def _fallback_basic_response(self, 
                                       message: str, 
                                       context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Fallback to basic response when enhanced processing fails"""
        
        try:
            # Simple web search check
            if self._should_search_web(message):
                try:
                    search_results = await web_search(message)
                    if search_results:
                        context = context or {}
                        context["web_search_results"] = search_results
                except Exception as e:
                    logger.warning(f"Web search failed in fallback: {e}")
            
            # Generate basic response
            system_prompt = self._build_basic_system_prompt(message, context)
            
            response = await self.central_brain.ollama_client.generate_response(
                prompt=message,
                system_prompt=system_prompt,
                context=context
            )
            
            return {
                "success": True,
                "message": response,
                "agent": "enhanced_user_interface",
                "interaction_id": self.interaction_count,
                "enhanced_mode": False,
                "fallback_used": True
            }
            
        except Exception as e:
            logger.error(f"Fallback processing failed: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "I'm experiencing technical difficulties. Please try again.",
                "agent": "enhanced_user_interface",
                "fallback_used": True
            }
    
    def _should_search_web(self, message: str) -> bool:
        """Determine if message would benefit from web search"""
        search_keywords = [
            "what is", "who is", "when is", "where is", "how is",
            "current", "latest", "recent", "news", "weather",
            "today", "now", "2024", "2025", "price", "cost",
            "stock", "market", "cryptocurrency", "bitcoin"
        ]
        
        message_lower = message.lower()
        return any(keyword in message_lower for keyword in search_keywords)
    
    def _build_basic_system_prompt(self, message: str, context: Optional[Dict[str, Any]]) -> str:
        """Build basic system prompt for fallback mode"""
        
        base_prompt = """You are CelFlow AI, a helpful and intelligent assistant.

You have access to current information through web search when needed.
Provide accurate, helpful responses based on the available context.

Current capabilities:
- General conversation and assistance
- Web search for current information
- Basic code execution and calculations
- System information and guidance"""

        # Add web search results if available
        if context and context.get("web_search_results"):
            web_info = context["web_search_results"]
            base_prompt += f"\n\nCURRENT WEB SEARCH RESULTS:\n{web_info}\n\nUse this information to provide accurate, up-to-date responses."
        
        # Add user preferences if available
        if self.user_preferences:
            base_prompt += f"\n\nUser preferences: {self.user_preferences}"
        
        return base_prompt
    
    async def _build_interaction_context(self, 
                                         message: str, 
                                         context: Optional[Dict[str, Any]]) -> Dict[str, Any]:
        """Build comprehensive interaction context"""
        
        interaction_context = context or {}
        
        # Add system information
        try:
            system_summary = await self.central_brain.get_system_summary()
            interaction_context.update({
                "system_status": system_summary.get("status", "operational"),
                "active_agents": system_summary.get("system_state", {}).get("active_agents", 0),
                "recent_activity": f"{system_summary.get('conversation_history', {}).get('recent_activity', 0)} recent interactions"
            })
        except Exception as e:
            logger.warning(f"Could not get system summary: {e}")
            interaction_context.update({
                "system_status": "operational",
                "active_agents": "unknown",
                "recent_activity": "none"
            })
        
        # Add user preferences and patterns
        interaction_context["user_preferences"] = self.user_preferences
        interaction_context["conversation_patterns"] = self.conversation_patterns
        
        # Add tool availability information
        available_tools = self.tool_registry.get_tools_for_context(message)
        interaction_context["available_tools"] = [tool.name for tool in available_tools]
        
        # Add interaction metadata
        interaction_context.update({
            "interaction_count": self.interaction_count,
            "timestamp": datetime.now().isoformat(),
            "message_length": len(message),
            "agent": "enhanced_user_interface"
        })
        
        return interaction_context
    
    async def _learn_from_enhanced_interaction(self, 
                                               message: str, 
                                               result: Dict[str, Any], 
                                               context: Dict[str, Any]):
        """Learn from enhanced interaction patterns"""
        
        try:
            # Update user preferences based on successful patterns
            if result.get("success", False):
                message_lower = message.lower()
                
                # Track tool usage preferences
                tools_used = result.get("tools_used", [])
                if tools_used:
                    for tool in tools_used:
                        pref_key = f"prefers_{tool}"
                        self.user_preferences[pref_key] = self.user_preferences.get(pref_key, 0) + 1
                
                # Track workflow preferences
                if result.get("workflow_used", False):
                    self.user_preferences["prefers_workflows"] = self.user_preferences.get("prefers_workflows", 0) + 1
                
                # Track interaction types
                interaction_type = self._classify_message_type(message)
                self.conversation_patterns[f"{interaction_type}_success"] = self.conversation_patterns.get(f"{interaction_type}_success", 0) + 1
            
            # Update conversation patterns
            self._update_conversation_patterns(message, result.get("message", ""))
            
        except Exception as e:
            logger.error(f"Learning from interaction failed: {e}")
    
    def _classify_message_type(self, message: str) -> str:
        """Classify the type of user message"""
        
        message_lower = message.lower()
        
        # Question patterns
        if any(word in message_lower for word in ["?", "what", "how", "why", "when", "where", "who"]):
            return "question"
        
        # Request patterns
        elif any(word in message_lower for word in ["please", "can you", "could you", "would you"]):
            return "request"
        
        # Greeting patterns
        elif any(word in message_lower for word in ["hello", "hi", "hey", "good morning", "good afternoon"]):
            return "greeting"
        
        # Gratitude patterns
        elif any(word in message_lower for word in ["thank", "thanks", "appreciate"]):
            return "gratitude"
        
        # Help request patterns
        elif any(word in message_lower for word in ["help", "assist", "support"]):
            return "help_request"
        
        # Code/technical patterns
        elif any(word in message_lower for word in ["code", "program", "execute", "run", "calculate"]):
            return "technical"
        
        # Search patterns
        elif any(word in message_lower for word in ["search", "find", "look up", "tell me about"]):
            return "search"
        
        else:
            return "general"
    
    def _update_conversation_patterns(self, message: str, response: str):
        """Update conversation patterns for better future interactions"""
        
        # Track message types
        message_type = self._classify_message_type(message)
        pattern_key = f"{message_type}_count"
        self.conversation_patterns[pattern_key] = self.conversation_patterns.get(pattern_key, 0) + 1
        
        # Track response characteristics
        if len(response) > 500:
            self.conversation_patterns["long_responses"] = self.conversation_patterns.get("long_responses", 0) + 1
        else:
            self.conversation_patterns["short_responses"] = self.conversation_patterns.get("short_responses", 0) + 1
        
        # Track overall statistics
        self.conversation_patterns["total_interactions"] = self.interaction_count
        self.conversation_patterns["last_interaction"] = datetime.now().isoformat()
    
    async def handle_voice_command(self, 
                                   command: str, 
                                   context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Process voice commands through enhanced system"""
        
        try:
            # Voice commands often need more direct action interpretation
            voice_context = context or {}
            voice_context["interaction_type"] = "voice_command"
            voice_context["requires_action"] = True
            voice_context["response_format"] = "conversational"
            
            # Process through enhanced system
            result = await self.process_chat_message(command, voice_context)
            result["input_type"] = "voice"
            
            return result
            
        except Exception as e:
            logger.error(f"Voice command processing failed: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "I couldn't process that voice command. Please try again.",
                "input_type": "voice",
                "agent": "enhanced_user_interface"
            }
    
    async def generate_proactive_suggestions(self, 
                                             context: Optional[Dict[str, Any]] = None) -> List[str]:
        """Generate proactive suggestions based on enhanced patterns"""
        
        try:
            # Analyze conversation patterns and tool usage
            suggestions = []
            
            # Tool-based suggestions
            if self.user_preferences.get("prefers_web_search", 0) > 2:
                suggestions.append("Would you like me to search for the latest information on a topic?")
            
            if self.user_preferences.get("prefers_execute_code", 0) > 2:
                suggestions.append("I can help you with calculations or data analysis if needed.")
            
            # Pattern-based suggestions
            if self.conversation_patterns.get("question_count", 0) > self.conversation_patterns.get("request_count", 0):
                suggestions.append("Feel free to ask me any questions - I'm here to help!")
            
            # Fallback suggestions
            if not suggestions:
                suggestions = [
                    "I can search the web for current information",
                    "I can help with calculations and data analysis", 
                    "Feel free to ask me anything!"
                ]
            
            return suggestions[:3]  # Return top 3 suggestions
            
        except Exception as e:
            logger.error(f"Suggestion generation failed: {e}")
            return ["How can I help you today?"]
    
    def get_agent_status(self) -> Dict[str, Any]:
        """Get comprehensive agent status"""
        
        tool_stats = self.tool_registry.get_execution_stats() if self.tool_registry else {}
        workflow_stats = self.workflow_engine.get_system_stats() if self.workflow_engine else {}
        
        return {
            "agent_type": "enhanced_user_interface",
            "interaction_count": self.interaction_count,
            "enhanced_mode_available": bool(self.workflow_engine),
            "registered_tools": len(self.tool_registry.tools) if self.tool_registry else 0,
            "user_preferences": self.user_preferences,
            "conversation_patterns": self.conversation_patterns,
            "tool_stats": tool_stats,
            "workflow_stats": workflow_stats,
            "status": "operational"
        }
