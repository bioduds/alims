"""
ALims Enhanced Agent Integration
Integrates the enhanced agent system with the existing CentralAIBrain
"""

import logging
from typing import Dict, Any, Optional

from .enhanced_user_interface_agent import EnhancedUserInterfaceAgent
from .enhanced_tool_system import ToolRegistry
from .enhanced_agent_workflow import EnhancedAgentWorkflow

logger = logging.getLogger(__name__)


class EnhancedAgentIntegration:
    """Integration layer for enhanced agent capabilities"""
    
    def __init__(self, central_brain):
        self.central_brain = central_brain
        self.enhanced_agent = None
        self.integration_enabled = False
        
        logger.info("Enhanced Agent Integration initialized")
    
    async def initialize(self):
        """Initialize the enhanced agent system"""
        
        try:
            if not self.central_brain.ollama_client:
                logger.warning("Ollama client not available, enhanced features disabled")
                return False
            
            # Initialize enhanced user interface agent
            self.enhanced_agent = EnhancedUserInterfaceAgent(self.central_brain)
            self.enhanced_agent.initialize_workflow_engine()
            
            self.integration_enabled = True
            logger.info("Enhanced agent system initialized successfully")
            
            return True
            
        except Exception as e:
            logger.error(f"Failed to initialize enhanced agent system: {e}")
            self.integration_enabled = False
            return False
    
    async def process_message(self, 
                              message: str, 
                              context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Process message through enhanced or fallback system"""
        
        if self.integration_enabled and self.enhanced_agent:
            try:
                # Use enhanced processing
                result = await self.enhanced_agent.process_chat_message(message, context)
                result["enhanced_processing"] = True
                return result
                
            except Exception as e:
                logger.error(f"Enhanced processing failed: {e}")
                # Fallback to basic processing
                return await self._fallback_processing(message, context)
        else:
            # Use basic processing
            return await self._fallback_processing(message, context)
    
    async def _fallback_processing(self, 
                                   message: str, 
                                   context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Fallback to basic processing when enhanced system is unavailable"""
        
        try:
            # Use the original user interface agent
            if hasattr(self.central_brain, 'user_interface') and self.central_brain.user_interface:
                result = await self.central_brain.user_interface.process_chat_message(message, context)
                result["enhanced_processing"] = False
                result["fallback_reason"] = "enhanced_system_unavailable"
                return result
            else:
                # Direct ollama response as last resort
                response = await self.central_brain.ollama_client.generate_response(
                    prompt=message,
                    system_prompt="You are ALims AI, a helpful assistant.",
                    context=context
                )
                
                return {
                    "success": True,
                    "message": response,
                    "enhanced_processing": False,
                    "fallback_reason": "basic_ollama_response"
                }
                
        except Exception as e:
            logger.error(f"Fallback processing failed: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "I'm experiencing technical difficulties. Please try again.",
                "enhanced_processing": False,
                "fallback_reason": "processing_error"
            }
    
    async def handle_voice_command(self, 
                                   command: str, 
                                   context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Handle voice commands through enhanced or fallback system"""
        
        if self.integration_enabled and self.enhanced_agent:
            try:
                result = await self.enhanced_agent.handle_voice_command(command, context)
                result["enhanced_processing"] = True
                return result
                
            except Exception as e:
                logger.error(f"Enhanced voice processing failed: {e}")
                # Fallback to basic voice processing
                return await self._fallback_voice_processing(command, context)
        else:
            return await self._fallback_voice_processing(command, context)
    
    async def _fallback_voice_processing(self, 
                                         command: str, 
                                         context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Fallback voice command processing"""
        
        try:
            if hasattr(self.central_brain, 'user_interface') and self.central_brain.user_interface:
                result = await self.central_brain.user_interface.handle_voice_command(command, context)
                result["enhanced_processing"] = False
                return result
            else:
                # Process as regular chat message
                result = await self._fallback_processing(command, context)
                result["input_type"] = "voice"
                return result
                
        except Exception as e:
            logger.error(f"Fallback voice processing failed: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "I couldn't process that voice command. Please try again.",
                "input_type": "voice",
                "enhanced_processing": False
            }
    
    async def generate_suggestions(self, 
                                   context: Optional[Dict[str, Any]] = None) -> list:
        """Generate proactive suggestions"""
        
        if self.integration_enabled and self.enhanced_agent:
            try:
                return await self.enhanced_agent.generate_proactive_suggestions(context)
            except Exception as e:
                logger.error(f"Enhanced suggestion generation failed: {e}")
        
        # Fallback suggestions
        return [
            "I can help you with questions and tasks",
            "Feel free to ask me anything",
            "I'm here to assist you"
        ]
    
    def get_system_status(self) -> Dict[str, Any]:
        """Get comprehensive system status"""
        
        status = {
            "integration_enabled": self.integration_enabled,
            "enhanced_agent_available": bool(self.enhanced_agent),
            "ollama_client_available": bool(self.central_brain.ollama_client),
            "fallback_available": True
        }
        
        if self.enhanced_agent:
            try:
                agent_status = self.enhanced_agent.get_agent_status()
                status["enhanced_agent_status"] = agent_status
            except Exception as e:
                logger.error(f"Error getting enhanced agent status: {e}")
                status["enhanced_agent_error"] = str(e)
        
        return status
    
    def get_tool_registry(self) -> Optional[ToolRegistry]:
        """Get the tool registry if available"""
        if self.enhanced_agent:
            return self.enhanced_agent.tool_registry
        return None
    
    def get_workflow_engine(self) -> Optional[EnhancedAgentWorkflow]:
        """Get the workflow engine if available"""
        if self.enhanced_agent:
            return self.enhanced_agent.workflow_engine
        return None


# Integration functions for backward compatibility with existing code

async def process_enhanced_chat_message(central_brain, 
                                        message: str, 
                                        context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Process chat message through enhanced system (backward compatible)"""
    
    if not hasattr(central_brain, '_enhanced_integration'):
        central_brain._enhanced_integration = EnhancedAgentIntegration(central_brain)
        await central_brain._enhanced_integration.initialize()
    
    return await central_brain._enhanced_integration.process_message(message, context)


async def process_enhanced_voice_command(central_brain, 
                                         command: str, 
                                         context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Process voice command through enhanced system (backward compatible)"""
    
    if not hasattr(central_brain, '_enhanced_integration'):
        central_brain._enhanced_integration = EnhancedAgentIntegration(central_brain)
        await central_brain._enhanced_integration.initialize()
    
    return await central_brain._enhanced_integration.handle_voice_command(command, context)


def get_enhanced_system_status(central_brain) -> Dict[str, Any]:
    """Get enhanced system status (backward compatible)"""
    
    if hasattr(central_brain, '_enhanced_integration'):
        return central_brain._enhanced_integration.get_system_status()
    
    return {
        "integration_enabled": False,
        "enhanced_agent_available": False,
        "reason": "not_initialized"
    }
