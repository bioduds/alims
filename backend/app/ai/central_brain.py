"""
CelFlow Central AI Brain - Core Orchestrating Intelligence
The main brain that coordinates all AI capabilities and system interactions
"""

import logging
import time
from typing import Dict, Any, Optional
from datetime import datetime

from .ollama_client import OllamaClient
from .context_manager import ContextManager
from .advanced_context_manager import AdvancedContextManager
from .user_interface_agent import UserInterfaceAgent
from .agent_orchestrator import AgentOrchestrator
from .embryo_trainer import EmbryoTrainer
from .system_controller import SystemController
from .pattern_validator import PatternValidator
from .proactive_suggestion_engine import ProactiveSuggestionEngine
from .code_executor import code_executor, ai_execute_code, LAMBDA_TEMPLATES
from .simple_algorithm_executor import SimpleAlgorithmExecutor

# Import voice interface
try:
    from ..system.voice_interface import VoiceInterface, create_voice_interface

    VOICE_AVAILABLE = True
except ImportError:
    VOICE_AVAILABLE = False
    VoiceInterface = None
    create_voice_interface = None

# Import web search capability


# Import enhanced logging
from ..core.enhanced_logging import central_brain_logger, lambda_logger

logger = logging.getLogger(__name__)


class CentralAIBrain:
    """The orchestrating intelligence of CelFlow"""

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.ai_config = config.get("ai_brain", {})
        self.context_config = config.get("context_management", {})

        # Core components
        self.ollama_client = None
        self.context_manager = None
        self.advanced_context_manager = None

        # Specialized agents (will be initialized later)
        self.user_interface = None
        self.agent_orchestrator = None
        self.embryo_trainer = None
        self.system_controller = None
        self.pattern_validator = None
        self.proactive_suggestion_engine = None
        self.voice_interface = None

        # Simple Algorithm Executor for restricted code execution
        self.simple_executor = SimpleAlgorithmExecutor()

        # State management
        self.is_running = False
        self.startup_time = None
        self.interaction_count = 0

        logger.info("CentralAIBrain initialized")

    async def start(self):
        """Initialize the Central AI Brain"""
        try:
            logger.info("🧠 Starting CelFlow Central AI Brain...")

            # Initialize core components
            self.ollama_client = OllamaClient(self.ai_config)
            await self.ollama_client.start()

            self.context_manager = ContextManager(self.context_config)

            # Initialize Advanced Context Manager
            self.advanced_context_manager = AdvancedContextManager(
                self.ollama_client, self.context_manager
            )

            # Validate that everything is working
            health_status = await self.get_health_status()
            if not health_status.get("ollama_healthy", False):
                raise Exception("Ollama client is not healthy")

            self.is_running = True
            self.startup_time = datetime.now()

            # Initialize specialized agents (placeholder for now)
            await self._initialize_specialized_agents()

            logger.info("✅ Central AI Brain started successfully")

        except Exception as e:
            logger.error(f"❌ Failed to start Central AI Brain: {e}")
            raise

    async def stop(self):
        """Shutdown the Central AI Brain"""
        try:
            logger.info("🛑 Stopping Central AI Brain...")

            if self.ollama_client:
                await self.ollama_client.close()

            self.is_running = False
            logger.info("✅ Central AI Brain stopped successfully")

        except Exception as e:
            logger.error(f"❌ Error stopping Central AI Brain: {e}")

    async def _initialize_specialized_agents(self):
        """Initialize specialized agent components"""
        try:
            # Initialize User Interface Agent
            self.user_interface = UserInterfaceAgent(self)
            logger.info("✅ UserInterfaceAgent initialized")

            # Initialize Agent Orchestrator
            self.agent_orchestrator = AgentOrchestrator(self)
            logger.info("✅ AgentOrchestrator initialized")

            # Initialize Embryo Trainer
            self.embryo_trainer = EmbryoTrainer(self)
            logger.info("✅ EmbryoTrainer initialized")

            # Initialize System Controller
            self.system_controller = SystemController(self)
            logger.info("✅ SystemController initialized")

            # Initialize Pattern Validator
            self.pattern_validator = PatternValidator(self.ollama_client)
            logger.info("✅ PatternValidator initialized")

            # Initialize Proactive Suggestion Engine
            self.proactive_suggestion_engine = ProactiveSuggestionEngine(
                self.ollama_client, self.advanced_context_manager
            )
            logger.info("✅ ProactiveSuggestionEngine initialized")

            # Initialize Voice Interface
            if VOICE_AVAILABLE:
                self.voice_interface = create_voice_interface(self.config)
                if self.voice_interface:
                    # Set up voice command callback
                    self.voice_interface.set_command_callback(
                        self._handle_voice_command
                    )
                    logger.info("✅ VoiceInterface initialized")
                else:
                    logger.warning("⚠️ VoiceInterface creation failed")
            else:
                logger.warning("⚠️ Voice interface not available (missing dependencies)")

            # Other agents will be initialized in subsequent phases
            logger.info("Specialized agents initialization completed")

        except Exception as e:
            logger.error(f"Failed to initialize specialized agents: {e}")
            # Continue without specialized agents for now
            logger.warning("Continuing without some specialized agents")

    async def process_user_input(
        self, user_message: str, context_type: str = "chat"
    ) -> Dict[str, Any]:
        """Main entry point for user interactions"""

        if not self.is_running:
            return {
                "success": False,
                "error": "Central AI Brain is not running",
                "message": "I apologize, but I'm not currently available. Please try again later.",
            }

        try:
            self.interaction_count += 1
            start_time = datetime.now()

            # Build context for this interaction
            context = await self.context_manager.build_context(
                interaction_type=context_type, user_message=user_message
            )

            # Generate system prompt based on context type
            system_prompt = self._get_system_prompt(context_type)

            # Generate response using Ollama
            response = await self.ollama_client.generate_response(
                prompt=user_message,
                context={"conversation_history": context},
                system_prompt=system_prompt,
            )

            # Update context with this interaction
            await self.context_manager.update_context(
                {
                    "user_message": user_message,
                    "assistant_response": response,
                    "context_type": context_type,
                    "metadata": {
                        "interaction_id": self.interaction_count,
                        "response_time": (datetime.now() - start_time).total_seconds(),
                    },
                }
            )

            return {
                "success": True,
                "message": response,
                "context_type": context_type,
                "interaction_id": self.interaction_count,
                "response_time": (datetime.now() - start_time).total_seconds(),
            }

        except Exception as e:
            logger.error(f"Error processing user input: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "I apologize, but I encountered an error processing your request. Please try again.",
            }

    async def chat_with_user_interface_agent(
        self, message: str, context: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """Process user input through the specialized User Interface Agent"""

        if not self.is_running:
            return {
                "success": False,
                "error": "Central AI Brain is not running",
                "message": "I apologize, but I'm not currently available. Please try again later.",
            }

        if not self.user_interface:
            # Fallback to basic processing if UserInterfaceAgent not available
            return await self.process_user_input(message, "chat")

        try:
            # Use the specialized User Interface Agent
            return await self.user_interface.process_chat_message(message, context)

        except Exception as e:
            logger.error(f"Error with User Interface Agent: {e}")
            # Fallback to basic processing
            return await self.process_user_input(message, "chat")

    async def stream_user_response(self, user_message: str, context_type: str = "chat"):
        """Stream response for real-time chat interface"""

        if not self.is_running:
            yield "I apologize, but I'm not currently available. Please try again later."
            return

        try:
            # Build context
            context = await self.context_manager.build_context(
                interaction_type=context_type, user_message=user_message
            )

            system_prompt = self._get_system_prompt(context_type)

            # Stream response
            full_response = ""
            async for chunk in self.ollama_client.stream_response(
                prompt=user_message,
                context={"conversation_history": context},
                system_prompt=system_prompt,
            ):
                full_response += chunk
                yield chunk

            # Update context after streaming is complete
            await self.context_manager.update_context(
                {
                    "user_message": user_message,
                    "assistant_response": full_response,
                    "context_type": context_type,
                    "metadata": {"interaction_id": self.interaction_count},
                }
            )

        except Exception as e:
            logger.error(f"Error streaming response: {e}")
            yield "I apologize, but I encountered an error. Please try again."

    def _get_system_prompt(self, context_type: str) -> str:
        """Get appropriate system prompt based on context type"""

        base_prompt = """You are the Central AI Brain of CelFlow, a self-creating AI operating system.

Your personality:
- Helpful and knowledgeable about the CelFlow system
- Clear and concise in explanations
- Proactive in offering assistance
- Respectful of user privacy and preferences
- Enthusiastic about AI and system capabilities

Your core capabilities:
- Answer questions about CelFlow functionality
- Execute user commands by coordinating with specialized agents
- Provide system status and insights
- Offer proactive suggestions based on user patterns
- Learn and adapt from interactions
- Execute dynamic Python code when existing tools are insufficient (Lambda capability)"""

        if context_type == "chat":
            return (
                base_prompt
                + "\n\nYou are in casual conversation mode. Be friendly and helpful."
            )

        elif context_type == "system_control":
            return (
                base_prompt
                + "\n\nYou are in system control mode. Focus on understanding and executing system commands safely."
            )

        elif context_type == "agent_orchestration":
            return (
                base_prompt
                + "\n\nYou are coordinating multiple agents. Focus on task delegation and result synthesis."
            )

        elif context_type == "embryo_training":
            return (
                base_prompt
                + "\n\nYou are evaluating embryo training. Focus on pattern analysis and specialization recommendations."
            )

        else:
            return base_prompt

    async def coordinate_system_action(self, action: Dict[str, Any]) -> Dict[str, Any]:
        """Coordinate complex system actions"""

        if not self.is_running:
            return {"success": False, "error": "Central AI Brain is not running"}

        try:
            action_type = action.get("type", "unknown")
            logger.info(f"Coordinating system action: {action_type}")

            # This is a placeholder for system action coordination
            # Will be implemented with specialized agents

            return {
                "success": True,
                "action_type": action_type,
                "message": f"System action '{action_type}' coordinated successfully",
                "timestamp": datetime.now().isoformat(),
            }

        except Exception as e:
            logger.error(f"Error coordinating system action: {e}")
            return {"success": False, "error": str(e)}

    async def orchestrate_complex_task(
        self, task_description: str, context: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """Orchestrate complex tasks using multiple specialized agents"""

        if not self.is_running:
            return {"success": False, "error": "Central AI Brain is not running"}

        if not self.agent_orchestrator:
            return {"success": False, "error": "Agent Orchestrator not available"}

        try:
            logger.info(f"🎭 Orchestrating complex task: {task_description[:50]}...")

            # Delegate to Agent Orchestrator
            result = await self.agent_orchestrator.coordinate_task(
                task_description, context
            )

            logger.info(
                f"✅ Task orchestration completed: {result.get('success', False)}"
            )
            return result

        except Exception as e:
            logger.error(f"Error orchestrating complex task: {e}")
            return {"success": False, "error": str(e)}

    async def get_health_status(self) -> Dict[str, Any]:
        """Get comprehensive health status of Central AI Brain"""

        status = {
            "central_brain_running": self.is_running,
            "startup_time": (
                self.startup_time.isoformat() if self.startup_time else None
            ),
            "interaction_count": self.interaction_count,
            "ollama_healthy": False,
            "context_manager_status": None,
        }

        # Check Ollama client health
        if self.ollama_client:
            ollama_status = self.ollama_client.get_health_status()
            status["ollama_healthy"] = ollama_status.get("is_healthy", False)
            status["ollama_model"] = ollama_status.get("model_name", "unknown")

        # Check context manager status
        if self.context_manager:
            status["context_manager_status"] = (
                self.context_manager.get_context_summary()
            )

        return status

    async def get_system_insights(self) -> Dict[str, Any]:
        """Get insights about system usage and patterns"""

        insights = {
            "interaction_statistics": {
                "total_interactions": self.interaction_count,
                "uptime_hours": 0,
            },
            "context_insights": {},
            "performance_metrics": {},
        }

        if self.startup_time:
            uptime = datetime.now() - self.startup_time
            insights["interaction_statistics"]["uptime_hours"] = (
                uptime.total_seconds() / 3600
            )

        if self.context_manager:
            insights["context_insights"] = self.context_manager.get_context_summary()

        return insights

    async def update_system_state(self, state_update: Dict[str, Any]):
        """Update system state information"""

        if self.context_manager:
            await self.context_manager.update_context(
                {
                    "system_state": state_update,
                    "metadata": {"update_time": datetime.now().isoformat()},
                }
            )

    async def validate_patterns(self, patterns: list) -> Dict[str, Any]:
        """Validate pattern classifications for coherence"""
        if not self.pattern_validator:
            return {
                "success": False,
                "error": "PatternValidator not available",
                "patterns_validated": 0,
            }

        try:
            # Convert patterns to PatternClassification objects if needed
            from .pattern_validator import PatternClassification

            pattern_objects = []

            for pattern in patterns:
                if isinstance(pattern, dict):
                    pattern_obj = PatternClassification(
                        pattern_id=pattern.get("id", f"pattern_{len(pattern_objects)}"),
                        category=pattern.get("category", "UNKNOWN"),
                        subcategory=pattern.get("subcategory", "unknown"),
                        confidence=pattern.get("confidence", 0.5),
                        source_agent=pattern.get("source_agent", "system"),
                        timestamp=datetime.now(),
                        metadata=pattern.get("metadata", {}),
                    )
                    pattern_objects.append(pattern_obj)
                else:
                    pattern_objects.append(pattern)

            # Perform system audit if multiple patterns
            if len(pattern_objects) > 1:
                result = await self.pattern_validator.system_audit()
            else:
                # Validate single pattern
                result = await self.pattern_validator.validate_single_pattern(
                    pattern_objects[0]
                )
                result = {
                    "success": True,
                    "validation_result": result,
                    "patterns_validated": 1,
                }

            return {
                "success": True,
                "validation_result": result,
                "patterns_validated": len(pattern_objects),
            }

        except Exception as e:
            logger.error(f"Error validating patterns: {e}")
            return {
                "success": False,
                "error": str(e),
                "patterns_validated": 0,
            }

    async def generate_training_labels(self, events: list) -> Dict[str, Any]:
        """Generate intelligent training labels for events"""

        if not self.is_running:
            return {"success": False, "error": "Central AI Brain is not running"}

        if not self.embryo_trainer:
            return {"success": False, "error": "Embryo Trainer not available"}

        try:
            logger.info(f"🏷️ Generating training labels for {len(events)} events")

            # Delegate to Embryo Trainer
            result = await self.embryo_trainer.generate_training_labels(events)

            logger.info(f"✅ Training labels generated: {result.get('success', False)}")
            return result

        except Exception as e:
            logger.error(f"Error generating training labels: {e}")
            return {"success": False, "error": str(e)}

    async def validate_embryo_training(
        self, embryo_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Validate embryo training quality and coherence"""

        if not self.is_running:
            return {"success": False, "error": "Central AI Brain is not running"}

        if not self.embryo_trainer:
            return {"success": False, "error": "Embryo Trainer not available"}

        try:
            embryo_id = embryo_data.get("id", "unknown")
            logger.info(f"🧬 Validating embryo training: {embryo_id}")

            # Delegate to Embryo Trainer
            result = await self.embryo_trainer.validate_embryo_training(embryo_data)

            logger.info(
                f"✅ Embryo validation completed: {result.get('success', False)}"
            )
            return result

        except Exception as e:
            logger.error(f"Error validating embryo training: {e}")
            return {"success": False, "error": str(e)}

    async def assess_embryo_birth_readiness(
        self, embryo_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Assess if embryo is ready for agent birth"""

        if not self.is_running:
            return {"success": False, "error": "Central AI Brain is not running"}

        if not self.embryo_trainer:
            return {"success": False, "error": "Embryo Trainer not available"}

        try:
            embryo_id = embryo_data.get("id", "unknown")
            logger.info(f"🎯 Assessing birth readiness: {embryo_id}")

            # Delegate to Embryo Trainer
            result = await self.embryo_trainer.assess_birth_readiness(embryo_data)

            logger.info(f"✅ Birth readiness assessed: {result.get('success', False)}")
            return result

        except Exception as e:
            logger.error(f"Error assessing birth readiness: {e}")
            return {"success": False, "error": str(e)}

    def get_status_summary(self) -> str:
        """Get a human-readable status summary"""

        if not self.is_running:
            return "🔴 Central AI Brain is offline"

        uptime = ""
        if self.startup_time:
            uptime_seconds = (datetime.now() - self.startup_time).total_seconds()
            uptime = f" (uptime: {uptime_seconds/3600:.1f}h)"

        return f"🟢 Central AI Brain is online{uptime} - {self.interaction_count} interactions processed"

    async def translate_user_command(
        self, user_command: str, user_context: Dict[str, Any] = None
    ) -> Dict[str, Any]:
        """Translate natural language command into system action"""
        if not self.is_running or not self.system_controller:
            return {
                "success": False,
                "error": "SystemController not available",
                "action": None,
            }

        try:
            system_action = await self.system_controller.translate_user_command(
                user_command, user_context
            )
            return {
                "success": True,
                "action": system_action,
                "action_id": system_action.action_id,
            }

        except Exception as e:
            logger.error(f"Error translating user command: {e}")
            return {
                "success": False,
                "error": str(e),
                "action": None,
            }

    async def execute_system_action(self, action) -> Dict[str, Any]:
        """Execute a validated system action"""
        if not self.is_running or not self.system_controller:
            return {
                "success": False,
                "error": "SystemController not available",
            }

        try:
            return await self.system_controller.execute_system_action(action)

        except Exception as e:
            logger.error(f"Error executing system action: {e}")
            return {
                "success": False,
                "error": str(e),
            }

    async def process_user_command(
        self, user_command: str, user_context: Dict[str, Any] = None
    ) -> Dict[str, Any]:
        """Complete command processing: translate and execute"""
        try:
            # Translate command
            translation_result = await self.translate_user_command(
                user_command, user_context
            )

            if not translation_result.get("success"):
                return translation_result

            action = translation_result["action"]

            # Check if action requires confirmation
            if action.recommended_action.value in [
                "request_confirmation",
                "request_clarification",
            ]:
                return {
                    "success": True,
                    "requires_user_input": True,
                    "message": action.user_feedback,
                    "action_id": action.action_id,
                    "recommended_action": action.recommended_action.value,
                }

            # Execute if safe
            if action.recommended_action.value == "execute":
                execution_result = await self.execute_system_action(action)
                return {
                    "success": execution_result.get("success", False),
                    "message": execution_result.get("message", "Action completed"),
                    "action_id": action.action_id,
                    "results": execution_result,
                }

            # Deny unsafe actions
            return {
                "success": False,
                "message": action.user_feedback,
                "action_id": action.action_id,
                "recommended_action": action.recommended_action.value,
            }

        except Exception as e:
            logger.error(f"Error processing user command: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "I encountered an error processing your command.",
            }

    async def analyze_user_patterns(
        self, user_id: str = "default_user"
    ) -> Dict[str, Any]:
        """Analyze user interaction patterns using Advanced Context Manager"""
        if not self.advanced_context_manager:
            return {
                "success": False,
                "error": "Advanced Context Manager not available",
                "patterns": [],
                "insights": [],
                "recommendations": [],
            }

        try:
            analysis_result = (
                await self.advanced_context_manager.analyze_interaction_patterns(
                    user_id
                )
            )
            return {"success": True, **analysis_result}
        except Exception as e:
            logger.error(f"Error analyzing user patterns: {e}")
            return {
                "success": False,
                "error": str(e),
                "patterns": [],
                "insights": [],
                "recommendations": [],
            }

    async def generate_context_insights(
        self, interaction_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Generate AI-powered context insights"""
        if not self.advanced_context_manager:
            return {
                "success": False,
                "error": "Advanced Context Manager not available",
                "insights": [],
            }

        try:
            insights = await self.advanced_context_manager.generate_context_insights(
                interaction_data
            )
            return {
                "success": True,
                "insights": [
                    {
                        "id": insight.insight_id,
                        "type": insight.insight_type,
                        "description": insight.description,
                        "confidence": insight.confidence,
                        "suggestions": insight.actionable_suggestions,
                        "created_at": insight.created_at.isoformat(),
                    }
                    for insight in insights
                ],
            }
        except Exception as e:
            logger.error(f"Error generating context insights: {e}")
            return {"success": False, "error": str(e), "insights": []}

    async def optimize_context_memory(self) -> Dict[str, Any]:
        """Optimize context memory using AI-driven analysis"""
        if not self.advanced_context_manager:
            return {"success": False, "error": "Advanced Context Manager not available"}

        try:
            optimization_result = (
                await self.advanced_context_manager.optimize_context_memory()
            )
            return {"success": True, **optimization_result}
        except Exception as e:
            logger.error(f"Error optimizing context memory: {e}")
            return {"success": False, "error": str(e)}

    def get_advanced_context_metrics(self) -> Dict[str, Any]:
        """Get advanced context management metrics"""
        if not self.advanced_context_manager:
            return {
                "success": False,
                "error": "Advanced Context Manager not available",
                "metrics": {},
            }

        try:
            metrics = self.advanced_context_manager.get_advanced_metrics()
            return {"success": True, "metrics": metrics}
        except Exception as e:
            logger.error(f"Error getting advanced context metrics: {e}")
            return {"success": False, "error": str(e), "metrics": {}}

    async def generate_proactive_suggestions(
        self, user_id: str, context_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Generate proactive suggestions for the user"""
        if not self.proactive_suggestion_engine:
            return {
                "success": False,
                "error": "Proactive Suggestion Engine not available",
                "suggestions": [],
            }

        try:
            from .proactive_suggestion_engine import SuggestionContext

            # Build suggestion context
            suggestion_context = SuggestionContext(
                user_id=user_id,
                current_activity=context_data.get("current_activity", "unknown"),
                time_of_day=context_data.get("time_of_day", "unknown"),
                day_of_week=context_data.get("day_of_week", "unknown"),
                recent_patterns=context_data.get("recent_patterns", []),
                productivity_metrics=context_data.get("productivity_metrics", {}),
                user_preferences=context_data.get("user_preferences", {}),
                available_time=context_data.get("available_time", 30),
                energy_level=context_data.get("energy_level", "medium"),
                focus_areas=context_data.get("focus_areas", []),
            )

            suggestions = await self.proactive_suggestion_engine.generate_suggestions(
                suggestion_context
            )

            return {
                "success": True,
                "suggestions": [
                    {
                        "id": s.suggestion_id,
                        "type": s.suggestion_type.value,
                        "priority": s.priority.value,
                        "timing": s.timing.value,
                        "title": s.title,
                        "description": s.description,
                        "rationale": s.rationale,
                        "actionable_steps": s.actionable_steps,
                        "expected_benefit": s.expected_benefit,
                        "confidence_score": s.confidence_score,
                        "created_at": s.created_at.isoformat(),
                        "expires_at": s.expires_at.isoformat(),
                        "status": s.status.value,
                    }
                    for s in suggestions
                ],
                "total_suggestions": len(suggestions),
            }

        except Exception as e:
            logger.error(f"Error generating proactive suggestions: {e}")
            return {"success": False, "error": str(e), "suggestions": []}

    async def get_immediate_suggestions(
        self, user_id: str, max_count: int = 3
    ) -> Dict[str, Any]:
        """Get immediate suggestions for the user"""
        if not self.proactive_suggestion_engine:
            return {
                "success": False,
                "error": "Proactive Suggestion Engine not available",
                "suggestions": [],
            }

        try:
            suggestions = (
                await self.proactive_suggestion_engine.get_immediate_suggestions(
                    user_id, max_count
                )
            )

            return {
                "success": True,
                "suggestions": [
                    {
                        "id": s.suggestion_id,
                        "type": s.suggestion_type.value,
                        "priority": s.priority.value,
                        "title": s.title,
                        "description": s.description,
                        "actionable_steps": s.actionable_steps,
                        "expected_benefit": s.expected_benefit,
                        "confidence_score": s.confidence_score,
                    }
                    for s in suggestions
                ],
                "delivered_count": len(suggestions),
            }

        except Exception as e:
            logger.error(f"Error getting immediate suggestions: {e}")
            return {"success": False, "error": str(e), "suggestions": []}

    async def process_suggestion_feedback(
        self,
        suggestion_id: str,
        user_id: str,
        feedback_type: str,
        feedback_text: str = None,
        effectiveness_rating: int = None,
    ) -> Dict[str, Any]:
        """Process user feedback on suggestions"""
        if not self.proactive_suggestion_engine:
            return {
                "success": False,
                "error": "Proactive Suggestion Engine not available",
            }

        try:
            from .proactive_suggestion_engine import SuggestionFeedback

            feedback = SuggestionFeedback(
                suggestion_id=suggestion_id,
                user_id=user_id,
                feedback_type=feedback_type,
                feedback_text=feedback_text,
                effectiveness_rating=effectiveness_rating,
                timestamp=datetime.now(),
            )

            result = await self.proactive_suggestion_engine.process_user_feedback(
                feedback
            )
            return result

        except Exception as e:
            logger.error(f"Error processing suggestion feedback: {e}")
            return {"success": False, "error": str(e)}

    def get_suggestion_metrics(self) -> Dict[str, Any]:
        """Get proactive suggestion system metrics"""
        if not self.proactive_suggestion_engine:
            return {
                "success": False,
                "error": "Proactive Suggestion Engine not available",
                "metrics": {},
            }

        try:
            metrics = self.proactive_suggestion_engine.get_suggestion_metrics()
            return {"success": True, "metrics": metrics}

        except Exception as e:
            logger.error(f"Error getting suggestion metrics: {e}")
            return {"success": False, "error": str(e), "metrics": {}}

    async def _handle_voice_command(self, voice_command):
        """Handle voice commands from the voice interface"""
        try:
            from ..system.voice_interface import VoiceCommandType

            logger.info(f"Processing voice command: {voice_command.processed_text}")

            if voice_command.command_type == VoiceCommandType.SYSTEM_CONTROL:
                # Handle system control commands
                action = voice_command.parameters.get("action", "status")
                if action == "status":
                    status = self.get_status_summary()
                    await self.voice_interface.speak(f"System status: {status}")
                elif action == "start":
                    await self.voice_interface.speak("Starting system components")
                elif action == "stop":
                    await self.voice_interface.speak("Stopping system components")
                else:
                    await self.voice_interface.speak("System command processed")

            elif voice_command.command_type == VoiceCommandType.CHAT_MESSAGE:
                # Process as regular chat message
                response = await self.process_user_input(
                    voice_command.processed_text, "voice_chat"
                )
                if response.get("success"):
                    await self.voice_interface.speak(
                        response.get("message", "I'm here to help")
                    )
                else:
                    await self.voice_interface.speak(
                        "I'm sorry, I couldn't process that request"
                    )

            elif voice_command.command_type == VoiceCommandType.TASK_MANAGEMENT:
                # Handle task management
                action = voice_command.parameters.get("action", "list")
                if action == "list":
                    await self.voice_interface.speak("Here are your current tasks")
                elif action == "create":
                    await self.voice_interface.speak("I'll help you create a new task")
                else:
                    await self.voice_interface.speak("Task command processed")

            elif voice_command.command_type == VoiceCommandType.QUERY_REQUEST:
                # Handle query requests
                query = voice_command.parameters.get("query", "")
                if query:
                    await self.voice_interface.speak(
                        f"Searching for information about {query}"
                    )
                else:
                    await self.voice_interface.speak(
                        "What would you like me to search for?"
                    )

            else:
                # Default response
                await self.voice_interface.speak(
                    "I heard your command and I'm processing it"
                )

        except Exception as e:
            logger.error(f"Error handling voice command: {e}")
            if self.voice_interface:
                await self.voice_interface.speak(
                    "I encountered an error processing your command"
                )

    async def start_voice_interface(self) -> Dict[str, Any]:
        """Start the voice interface system"""
        if not self.voice_interface:
            return {"success": False, "error": "Voice interface not available"}

        try:
            success = await self.voice_interface.start()
            return {
                "success": success,
                "message": (
                    "Voice interface started"
                    if success
                    else "Failed to start voice interface"
                ),
            }
        except Exception as e:
            logger.error(f"Error starting voice interface: {e}")
            return {"success": False, "error": str(e)}

    async def stop_voice_interface(self) -> Dict[str, Any]:
        """Stop the voice interface system"""
        if not self.voice_interface:
            return {"success": False, "error": "Voice interface not available"}

        try:
            await self.voice_interface.stop()
            return {"success": True, "message": "Voice interface stopped"}
        except Exception as e:
            logger.error(f"Error stopping voice interface: {e}")
            return {"success": False, "error": str(e)}

    async def start_voice_listening(self) -> Dict[str, Any]:
        """Start voice listening"""
        if not self.voice_interface:
            return {"success": False, "error": "Voice interface not available"}

        try:
            await self.voice_interface.start_listening()
            return {"success": True, "message": "Voice listening started"}
        except Exception as e:
            logger.error(f"Error starting voice listening: {e}")
            return {"success": False, "error": str(e)}

    async def stop_voice_listening(self) -> Dict[str, Any]:
        """Stop voice listening"""
        if not self.voice_interface:
            return {"success": False, "error": "Voice interface not available"}

        try:
            await self.voice_interface.stop_listening()
            return {"success": True, "message": "Voice listening stopped"}
        except Exception as e:
            logger.error(f"Error stopping voice listening: {e}")
            return {"success": False, "error": str(e)}

    def get_voice_metrics(self) -> Dict[str, Any]:
        """Get voice interface metrics"""
        if not self.voice_interface:
            return {
                "success": False,
                "error": "Voice interface not available",
                "metrics": {},
            }

        try:
            metrics = self.voice_interface.get_voice_metrics()
            return {"success": True, "metrics": metrics}
        except Exception as e:
            logger.error(f"Error getting voice metrics: {e}")
            return {"success": False, "error": str(e), "metrics": {}}

    def get_voice_status(self) -> Dict[str, Any]:
        """Get voice interface status"""
        if not self.voice_interface:
            return {
                "success": False,
                "error": "Voice interface not available",
                "status": {},
            }

        try:
            status = self.voice_interface.get_voice_status()
            return {"success": True, "status": status}
        except Exception as e:
            logger.error(f"Error getting voice status: {e}")
            return {"success": False, "error": str(e), "status": {}}

    async def execute_dynamic_code(self, 
                                  code: str, 
                                  purpose: str = "general",
                                  context: Dict[str, Any] = None,
                                  use_lambda_style: bool = False) -> Dict[str, Any]:
        """
        Execute dynamic code in a sandboxed environment.
        This is the AI's 'Lambda' capability - run code on-demand when existing tools aren't sufficient.
        
        Args:
            code: Python code to execute
            purpose: Purpose of execution ('calculation', 'visualization', 'data_processing', etc.)
            context: Variables to inject into the execution environment
            use_lambda_style: If True, expects code to define a handler(event, context) function
            
        Returns:
            Execution results including output, errors, and optionally visualizations
        """
        try:
            logger.info(f"🧠 AI executing dynamic code for purpose: {purpose}")

            # Log the routing decision with enhanced logging
            should_use_simple = self._should_use_simple_executor(code, purpose)
            executor_type = (
                "Simple Algorithm Executor"
                if should_use_simple
                else "Full Code Executor"
            )

            central_brain_logger.log_routing_decision(
                code=code,
                purpose=purpose,
                decision=executor_type,
                reasoning=f"Based on purpose '{purpose}' and code analysis",
            )

            # Check if we should use Simple Algorithm Executor
            if should_use_simple:
                logger.info("🔢 Using Simple Algorithm Executor for safe execution")
                start_time = time.time()
                result = await self.execute_simple_algorithm(
                    code=code, inputs=context, expected_output_type="auto"
                )
                execution_time = time.time() - start_time

                # Log the execution with enhanced logging
                lambda_logger.log_lambda_execution(
                    code=code,
                    purpose=purpose,
                    executor_type="simple",
                    result=result,
                    execution_time=execution_time,
                )
                return result

            # Use full code executor for complex tasks
            logger.info("⚙️ Using full Code Executor for complex execution")

            # Add system context
            execution_context = context or {}
            execution_context.update({
                'celflow_version': '1.0.0',
                'ai_model': self.ai_config.get('model_name', 'gemma3:4b'),
                'execution_purpose': purpose,
                'timestamp': datetime.now().isoformat()
            })

            if use_lambda_style:
                # Execute as Lambda function
                event = execution_context.get('event', {})
                lambda_context = execution_context.get('lambda_context', {})
                result = await code_executor.execute_lambda_function(code, event, lambda_context)
            else:
                # Execute as regular code
                result = await ai_execute_code(code, purpose, execution_context)

            # Check if result is None
            if result is None:
                logger.error("❌ ai_execute_code returned None!")
                return {
                    "success": False,
                    "error": "Code execution returned no result",
                    "execution_id": datetime.now().isoformat()
                }

            # Log execution for learning
            if result.get('success'):
                logger.info(f"✅ Code execution successful for {purpose}")
                # Store successful patterns for future reference
                await self.context_manager.update_context({
                    'code_execution': {
                        'purpose': purpose,
                        'success': True,
                        'code_snippet': code[:200] + '...' if len(code) > 200 else code,
                        'timestamp': datetime.now().isoformat()
                    }
                })
            else:
                logger.warning(f"⚠️ Code execution failed: {result.get('error')}")
                logger.warning(f"Full execution result: {result}")

            return result

        except Exception as e:
            logger.error(f"❌ Error in execute_dynamic_code: {e}")
            return {
                "success": False,
                "error": str(e),
                "execution_id": datetime.now().isoformat()
            }

    async def get_lambda_template(self, template_type: str) -> Dict[str, Any]:
        """
        Get a Lambda-style template for the AI to use as a starting point.
        
        Args:
            template_type: Type of template ('data_processor', 'chart_generator', 'custom_analysis')
            
        Returns:
            Template code and usage instructions
        """
        if template_type in LAMBDA_TEMPLATES:
            return {
                "success": True,
                "template_type": template_type,
                "code": LAMBDA_TEMPLATES[template_type],
                "usage": f"Modify this template for {template_type} tasks. Call handler(event, context) with appropriate data.",
                "example_event": {
                    "data_processor": {"data": [1, 2, 3, 4, 5]},
                    "chart_generator": {"chart_type": "bar", "data": [10, 20, 30], "title": "Sample Chart"},
                    "custom_analysis": {"input": "Sample text", "type": "sentiment"}
                }.get(template_type, {})
            }
        else:
            return {
                "success": False,
                "error": f"Unknown template type: {template_type}",
                "available_templates": list(LAMBDA_TEMPLATES.keys())
            }

    async def decide_code_execution(self, user_request: str, available_tools: list) -> Dict[str, Any]:
        """
        AI decides whether to use existing tools or write custom code.
        
        Args:
            user_request: What the user is asking for
            available_tools: List of available tools/capabilities
            
        Returns:
            Decision on whether to use code execution and suggested approach
        """
        # Ask the AI to analyze the request
        decision_prompt = f"""Analyze this user request and determine if it requires custom code execution:

User Request: {user_request}

Available Tools: {', '.join(available_tools)}

Consider:
1. Can this be done with existing tools?
2. Would custom code provide a better solution?
3. What type of code would be needed?

Respond with:
- use_code: true/false
- reason: explanation of decision
- suggested_approach: brief description
- code_purpose: 'calculation', 'visualization', 'data_processing', or 'custom'"""

        response = await self.ollama_client.generate_response(
            prompt=decision_prompt,
            system_prompt="You are an AI assistant that helps decide when to use custom code execution."
        )

        # Parse the response (in a real implementation, this would be more structured)
        return {
            "decision": response,
            "timestamp": datetime.now().isoformat()
        }

    def _should_use_simple_executor(self, code: str, purpose: str) -> bool:
        """
        Determine if code should use the Simple Algorithm Executor
        instead of the full code executor.

        Returns True for simple algorithmic tasks that match our restricted patterns.
        """
        # Check for complexity indicators first (higher priority)
        code_lower = code.lower()
        complex_indicators = [
            "import requests",
            "import urllib",
            "import os",
            "import subprocess",
            "import sys",
            "open(",
            "file(",
            "exec(",
            "eval(",
            "__import__",
        ]

        if any(indicator in code_lower for indicator in complex_indicators):
            return False

        # Check if purpose suggests simple algorithm
        simple_purposes = [
            "calculation",
            "mathematical_calculation",
            "algorithm",
            "number_generation",
            "list_generation",
            "simple_sorting",
            "basic_filtering",
            "simple_statistics",
        ]

        if purpose.lower() in simple_purposes:
            return True

        # Check if code contains simple algorithm patterns
        simple_patterns = [
            "def calculate_",
            "def generate_",
            "def find_",
            "def sort_",
            "def filter_",
            "def analyze_",
            "prime",
            "fibonacci",
            "factorial",
            "statistics",
        ]

        # If code contains these patterns and is relatively short (< 2000 chars)
        if (
            any(pattern in code_lower for pattern in simple_patterns)
            and len(code) < 2000
        ):
            return True

        return False

    async def execute_simple_algorithm(
        self,
        code: str,
        inputs: Optional[Dict[str, Any]] = None,
        expected_output_type: str = "auto",
    ) -> Dict[str, Any]:
        """
        Execute simple algorithm using the restricted Simple Algorithm Executor.
        This provides safer, more predictable execution for basic algorithmic tasks.
        """
        try:
            logger.info("🔢 Using Simple Algorithm Executor for restricted execution")

            result = await self.simple_executor.execute_simple_algorithm(
                code=code, inputs=inputs, expected_output_type=expected_output_type
            )

            # Log success/failure for learning
            if result.get("success"):
                logger.info(
                    f"✅ Simple algorithm executed: {result.get('function_name')}"
                )
                if self.context_manager:
                    await self.context_manager.update_context(
                        {
                            "simple_algorithm_execution": {
                                "function_name": result.get("function_name"),
                                "pattern_type": result.get("pattern_type"),
                                "success": True,
                                "timestamp": datetime.now().isoformat(),
                            }
                        }
                    )
            else:
                logger.warning(f"⚠️ Simple algorithm failed: {result.get('error')}")

            return result

        except Exception as e:
            logger.error(f"❌ Error in simple algorithm execution: {e}")
            return {
                "success": False,
                "error": f"Simple algorithm execution error: {str(e)}",
                "execution_id": f"simple_algo_error_{int(time.time())}",
            }

    def get_simple_algorithm_guidelines(self) -> Dict[str, Any]:
        """
        Get guidelines for Gemma on when and how to use the Simple Algorithm Executor.
        This helps the AI understand the restrictions and appropriate use cases.
        """
        return {
            "purpose": "Restricted execution for simple, focused algorithms only",
            "when_to_use": [
                "Mathematical calculations (primes, fibonacci, factorials)",
                "List generation and basic data processing",
                "Simple sorting and filtering operations",
                "Basic statistical analysis",
                "Number sequence generation",
                "String processing algorithms",
            ],
            "restrictions": {
                "max_execution_time": "5 seconds",
                "no_file_operations": "Cannot read/write files",
                "no_network": "No web requests or downloads",
                "no_complex_imports": "Only basic math and built-ins",
                "single_function": "Must contain exactly one function",
                "clear_purpose": "Function name must be descriptive",
            },
            "function_naming": {
                "must_start_with": [
                    "calculate_",
                    "generate_",
                    "find_",
                    "sort_",
                    "filter_",
                    "analyze_",
                ],
                "examples": [
                    "calculate_prime_numbers(n)",
                    "generate_fibonacci_sequence(count)",
                    "analyze_number_statistics(numbers)",
                ],
            },
            "allowed_patterns": self.simple_executor.get_allowed_patterns(),
            "example_good_code": '''
def calculate_prime_numbers(n):
    """Generate first n prime numbers"""
    primes = []
    num = 2
    while len(primes) < n:
        is_prime = True
        for i in range(2, int(num ** 0.5) + 1):
            if num % i == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(num)
        num += 1
    return primes
''',
            "advice_for_ai": [
                "Use for simple, predictable algorithms only",
                "Prefer this over full executor for basic math/data tasks",
                "Always include function docstring",
                "Keep functions focused and single-purpose",
                "Return clear, usable results for further processing",
            ],
        }

    async def get_execution_recommendations(self, user_request: str) -> Dict[str, Any]:
        """
        Analyze user request and recommend execution approach.
        Helps Gemma decide between Simple Algorithm Executor vs full executor.
        """
        try:
            analysis_prompt = f"""Analyze this user request and recommend the best execution approach:

User Request: "{user_request}"

Consider:
1. Is this a simple algorithm that could use restricted execution?
2. Does it require complex operations, file access, or network requests?
3. What type of code would be needed?

Respond with JSON:
{{
    "recommendation": "simple_algorithm" | "full_executor" | "existing_tools",
    "reason": "brief explanation",
    "algorithm_type": "mathematical_calculation" | "list_generation" | "data_processing" | "complex_task",
    "confidence": 0.0-1.0,
    "suggested_function_name": "descriptive_name_here",
    "expected_inputs": {{"param": "type"}},
    "expected_output": "description"
}}"""

            if self.ollama_client:
                response = await self.ollama_client.generate_response(
                    prompt=analysis_prompt,
                    system_prompt="You are an AI that helps decide the best approach for code execution tasks.",
                )

                # Try to parse JSON from response
                try:
                    import json

                    # Extract JSON from response
                    json_start = response.find("{")
                    json_end = response.rfind("}") + 1
                    if json_start != -1 and json_end > json_start:
                        analysis = json.loads(response[json_start:json_end])
                        analysis["raw_response"] = response
                        return analysis
                except:
                    pass

                return {
                    "recommendation": "analysis_failed",
                    "raw_response": response,
                    "timestamp": datetime.now().isoformat(),
                }
            else:
                return {
                    "recommendation": "simple_algorithm",
                    "reason": "Default to simple executor when AI unavailable",
                    "confidence": 0.5,
                }

        except Exception as e:
            logger.error(f"Error in execution recommendation: {e}")
            return {
                "recommendation": "simple_algorithm",
                "reason": f"Error in analysis: {str(e)}",
                "confidence": 0.3,
            }


# Utility functions
async def create_central_brain(config: Dict[str, Any]) -> CentralAIBrain:
    """Create and start a Central AI Brain instance"""
    brain = CentralAIBrain(config)
    await brain.start()
    return brain
