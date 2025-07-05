"""
Ollama Integration for Enhanced Main Interface Agent
Provides intelligent LLM-powered responses for LIMS agent interactions.
"""

import logging
from typing import Dict, Any, Optional, List
import aiohttp
import json
import asyncio

logger = logging.getLogger(__name__)


class OllamaLIMSAgent:
    """Ollama-powered intelligent response generator for LIMS agents"""
    
    def __init__(self, 
                 base_url: str = "http://localhost:11434",
                 model_name: str = "llama3.2:latest",
                 timeout: int = 30):
        self.base_url = base_url
        self.model_name = model_name
        self.timeout = timeout
        self.session: Optional[aiohttp.ClientSession] = None
        
        # Agent-specific system prompts
        self.agent_prompts = {
            "sample_manager": """You are a Sample Management Agent in a Laboratory Information Management System (LIMS).
Your expertise includes sample tracking, quality control, chain of custody, sample lifecycle management, and sample searching.
Respond professionally and provide actionable information about laboratory samples.
Keep responses concise and laboratory-focused.""",
            
            "workflow_manager": """You are a Workflow Management Agent in a LIMS.
Your expertise includes protocol management, workflow automation, task scheduling, resource allocation, and workflow optimization.
Help users create, optimize, and manage laboratory workflows efficiently.
Provide practical workflow solutions and scheduling recommendations.""",
            
            "instrument_manager": """You are an Instrument Management Agent in a LIMS.
Your expertise includes instrument control, data acquisition, calibration, maintenance scheduling, and performance monitoring.
Assist with instrument operations, maintenance planning, and performance optimization.
Focus on ensuring instruments operate at peak efficiency.""",
            
            "data_analyst": """You are a Data Analysis Agent in a LIMS.
Your expertise includes statistical analysis, trend analysis, anomaly detection, report generation, and data visualization.
Help users understand their laboratory data through insightful analysis and clear explanations.
Provide statistical insights and data-driven recommendations.""",
            
            "compliance_manager": """You are a Compliance Management Agent in a LIMS.
Your expertise includes regulatory compliance, audit trails, documentation, validation protocols, and change control.
Ensure all laboratory operations meet regulatory requirements and maintain proper documentation.
Focus on compliance adherence and audit readiness.""",
            
            "safety_manager": """You are a Laboratory Safety Agent in a LIMS.
Your expertise includes safety monitoring, hazard assessment, emergency response, training management, and incident reporting.
Prioritize laboratory safety and help maintain a secure working environment.
Provide safety guidance and risk mitigation strategies.""",
            
            "default": """You are an intelligent Laboratory Information Management System (LIMS) agent.
You assist with laboratory operations, sample management, workflow optimization, and data analysis.
Provide helpful, accurate, and professional responses to laboratory-related queries."""
        }
    
    async def __aenter__(self):
        """Async context manager entry"""
        self.session = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=self.timeout))
        return self
    
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit"""
        if self.session:
            await self.session.close()
    
    async def initialize(self):
        """Initialize the Ollama client"""
        if not self.session:
            self.session = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=self.timeout))
        
        # Test connection to Ollama
        try:
            await self._health_check()
            logger.info(f"Ollama client initialized successfully with model: {self.model_name}")
            return True
        except Exception as e:
            logger.warning(f"Failed to connect to Ollama: {e}")
            return False
    
    async def shutdown(self):
        """Shutdown the Ollama client"""
        if self.session:
            await self.session.close()
            self.session = None
    
    async def _health_check(self):
        """Check if Ollama is running and model is available"""
        try:
            url = f"{self.base_url}/api/tags"
            async with self.session.get(url) as response:
                if response.status == 200:
                    data = await response.json()
                    models = [model["name"] for model in data.get("models", [])]
                    if any(self.model_name in model for model in models):
                        return True
                    else:
                        logger.warning(f"Model {self.model_name} not found. Available models: {models}")
                        return False
                else:
                    logger.warning(f"Ollama health check failed with status: {response.status}")
                    return False
        except Exception as e:
            logger.error(f"Ollama health check error: {e}")
            return False
    
    async def generate_response(self, 
                              message: str, 
                              agent_id: str = "default",
                              context: Optional[Dict[str, Any]] = None,
                              conversation_history: Optional[List[Dict[str, str]]] = None) -> str:
        """Generate an intelligent response using Ollama"""
        
        if not self.session:
            await self.initialize()
        
        try:
            # Build the prompt
            system_prompt = self.agent_prompts.get(agent_id, self.agent_prompts["default"])
            prompt = await self._build_prompt(message, system_prompt, context, conversation_history)
            
            # Generate response from Ollama
            response = await self._call_ollama(prompt)
            
            # Process and validate response
            processed_response = self._process_response(response, agent_id)
            
            logger.info(f"Generated response for agent {agent_id}: {len(processed_response)} characters")
            return processed_response
            
        except Exception as e:
            logger.error(f"Error generating Ollama response: {e}")
            return self._fallback_response(message, agent_id)
    
    async def _build_prompt(self, 
                           message: str, 
                           system_prompt: str,
                           context: Optional[Dict[str, Any]] = None,
                           conversation_history: Optional[List[Dict[str, str]]] = None) -> str:
        """Build a comprehensive prompt for the LLM"""
        
        prompt_parts = [
            f"System: {system_prompt}",
            ""
        ]
        
        # Add context if available
        if context:
            prompt_parts.append("Context Information:")
            for key, value in context.items():
                if isinstance(value, (str, int, float)):
                    prompt_parts.append(f"- {key}: {value}")
                elif isinstance(value, list):
                    prompt_parts.append(f"- {key}: {', '.join(map(str, value))}")
            prompt_parts.append("")
        
        # Add conversation history
        if conversation_history:
            prompt_parts.append("Previous Conversation:")
            for entry in conversation_history[-3:]:  # Last 3 entries
                role = entry.get("role", "user")
                content = entry.get("content", "")
                prompt_parts.append(f"{role.capitalize()}: {content}")
            prompt_parts.append("")
        
        # Add current message
        prompt_parts.extend([
            f"User: {message}",
            "",
            "Assistant: "
        ])
        
        return "\n".join(prompt_parts)
    
    async def _call_ollama(self, prompt: str) -> str:
        """Make API call to Ollama"""
        url = f"{self.base_url}/api/generate"
        
        payload = {
            "model": self.model_name,
            "prompt": prompt,
            "stream": False,
            "options": {
                "temperature": 0.7,
                "top_p": 0.9,
                "max_tokens": 512
            }
        }
        
        async with self.session.post(url, json=payload) as response:
            if response.status == 200:
                data = await response.json()
                return data.get("response", "").strip()
            else:
                error_text = await response.text()
                raise Exception(f"Ollama API error {response.status}: {error_text}")
    
    def _process_response(self, response: str, agent_id: str) -> str:
        """Process and enhance the raw Ollama response"""
        
        # Clean up the response
        response = response.strip()
        
        # Ensure response is not too long
        if len(response) > 800:
            response = response[:800] + "..."
        
        # Add agent signature if response doesn't seem agent-specific
        if not any(word in response.lower() for word in ["sample", "workflow", "instrument", "data", "compliance", "safety"]):
            agent_name = agent_id.replace("_", " ").title()
            response = f"[{agent_name}] {response}"
        
        return response
    
    def _fallback_response(self, message: str, agent_id: str) -> str:
        """Provide fallback response when Ollama is unavailable"""
        
        agent_responses = {
            "sample_manager": "I'm currently processing your sample-related request. Please ensure all sample information is complete and try again.",
            "workflow_manager": "I'm working on optimizing your laboratory workflow. Let me analyze the requirements and provide recommendations.",
            "instrument_manager": "I'm checking instrument status and availability. Please verify instrument configurations and try again.",
            "data_analyst": "I'm analyzing your laboratory data. Please provide additional context for more detailed insights.",
            "compliance_manager": "I'm reviewing compliance requirements for your request. Please ensure all documentation is current.",
            "safety_manager": "I'm assessing safety protocols for your laboratory operation. Please follow all safety guidelines.",
            "default": "I'm processing your laboratory request. Please provide more details for optimal assistance."
        }
        
        base_response = agent_responses.get(agent_id, agent_responses["default"])
        return f"{base_response} (Fallback mode - limited functionality)"


class OllamaIntegratedMainInterfaceAgent:
    """Enhanced Main Interface Agent with Ollama integration"""
    
    def __init__(self, base_agent, ollama_config: Optional[Dict[str, Any]] = None):
        self.base_agent = base_agent
        self.ollama_config = ollama_config or {}
        self.ollama_client: Optional[OllamaLIMSAgent] = None
        self.ollama_available = False
        
    async def initialize(self):
        """Initialize both base agent and Ollama client"""
        # Initialize base agent
        await self.base_agent.initialize()
        
        # Initialize Ollama client
        try:
            self.ollama_client = OllamaLIMSAgent(**self.ollama_config)
            self.ollama_available = await self.ollama_client.initialize()
            if self.ollama_available:
                logger.info("Ollama integration enabled for enhanced responses")
            else:
                logger.warning("Ollama not available - using fallback responses")
        except Exception as e:
            logger.warning(f"Failed to initialize Ollama client: {e}")
            self.ollama_available = False
    
    async def process_user_input(self, conversation_id: str, message: str, context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Enhanced user input processing with Ollama responses"""
        
        # Get conversation and agent information
        conversation = self.base_agent.conversations.get(conversation_id)
        if not conversation:
            raise ValueError(f"Conversation {conversation_id} not found")
        
        # Get assigned agent
        assigned_agent = conversation.assigned_agent
        
        # Store message in conversation context
        if 'messages' not in conversation.context:
            conversation.context['messages'] = []
        
        conversation.context['messages'].append({
            'role': 'user',
            'content': message,
            'timestamp': asyncio.get_event_loop().time(),
            'context': context
        })
        
        # Generate intelligent response
        if self.ollama_available and self.ollama_client:
            try:
                # Get conversation history for context
                conversation_history = conversation.context.get('messages', [])[-5:]  # Last 5 messages
                
                # Combine contexts
                full_context = {**conversation.context, **(context or {})}
                
                # Generate Ollama response
                response = await self.ollama_client.generate_response(
                    message=message,
                    agent_id=assigned_agent or "default",
                    context=full_context,
                    conversation_history=conversation_history
                )
                
                # Store response
                conversation.context['messages'].append({
                    'role': 'assistant',
                    'content': response,
                    'timestamp': asyncio.get_event_loop().time(),
                    'agent_id': assigned_agent
                })
                
            except Exception as e:
                logger.error(f"Error generating Ollama response: {e}")
                response = f"I apologize, but I'm experiencing technical difficulties. Please try again. (Error: {str(e)[:50]})"
        else:
            # Fallback to base agent response
            base_response = await self.base_agent.process_user_input(conversation_id, message, context)
            response = base_response.get("response", "")
        
        # Update audit
        self.base_agent._add_audit_event("MESSAGE_PROCESSED_OLLAMA", 
                                       conversation_id=conversation_id,
                                       details={
                                           "message_length": len(message),
                                           "response_length": len(response),
                                           "ollama_used": self.ollama_available,
                                           "agent_id": assigned_agent
                                       })
        
        return {
            "response": response,
            "status": "processed",
            "conversation_id": conversation_id,
            "agent_id": assigned_agent,
            "ollama_powered": self.ollama_available
        }
    
    async def shutdown(self):
        """Shutdown both base agent and Ollama client"""
        if self.ollama_client:
            await self.ollama_client.shutdown()
        await self.base_agent.shutdown()
    
    def __getattr__(self, name):
        """Delegate all other attributes to base agent"""
        return getattr(self.base_agent, name)
