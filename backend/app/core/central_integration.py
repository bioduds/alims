"""
Central Integration - Unified ALims AI Assistant

This module provides the complete integration layer that orchestrates all 8 specialized
agents into a unified, intelligent AI assistant for ALims. It serves as the main
entry point for all AI-powered interactions and coordinates:

- Natural language processing and user interface
- Multi-agent task coordination and orchestration
- Intelligent embryo training and validation
- Safe system command translation and execution
- Pattern classification coherence validation
- Advanced context intelligence and memory management
- Proactive user assistance and workflow optimization
- Voice command processing and speech interaction
"""

import asyncio
import logging
import time
from datetime import datetime
from typing import Dict, Any, Optional, List, Callable
from dataclasses import dataclass
from enum import Enum
import json

# Import all AI components
from ..ai.central_brain import CentralAIBrain, create_central_brain
from ..ai.context_manager import ContextManager

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class IntegrationMode(Enum):
    """Integration operation modes"""

    DEVELOPMENT = "development"
    PRODUCTION = "production"
    TESTING = "testing"
    DEMO = "demo"


class SystemState(Enum):
    """Overall system states"""

    INITIALIZING = "initializing"
    READY = "ready"
    ACTIVE = "active"
    PROCESSING = "processing"
    ERROR = "error"
    SHUTDOWN = "shutdown"


class InteractionType(Enum):
    """Types of user interactions"""

    TEXT_CHAT = "text_chat"
    VOICE_COMMAND = "voice_command"
    SYSTEM_COMMAND = "system_command"
    TASK_REQUEST = "task_request"
    QUERY_REQUEST = "query_request"
    TRAINING_REQUEST = "training_request"


@dataclass
class SystemMetrics:
    """Comprehensive system performance metrics"""

    total_interactions: int
    successful_interactions: int
    failed_interactions: int
    average_response_time: float
    agent_performance: Dict[str, Dict[str, Any]]
    system_uptime: float
    memory_usage: Dict[str, Any]
    ai_model_performance: Dict[str, Any]


@dataclass
class UserInteraction:
    """A complete user interaction with the system"""

    interaction_id: str
    user_id: str
    interaction_type: InteractionType
    input_data: Dict[str, Any]
    timestamp: datetime
    processing_time: float
    agents_involved: List[str]
    response_data: Dict[str, Any]
    success: bool
    confidence: float
    context_used: Dict[str, Any]


class CentralIntegration:
    """
    Central Integration System for ALims

    The unified AI assistant that orchestrates all specialized agents to provide
    intelligent, context-aware assistance for ALims users. This system serves
    as the main interface between users and the AI-powered capabilities.
    """

    def __init__(self, config: Dict[str, Any]):
        """Initialize the Central Integration system"""
        self.config = config
        self.integration_config = config.get("central_integration", {})

        # System state
        self.system_state = SystemState.INITIALIZING
        self.integration_mode = IntegrationMode(
            self.integration_config.get("mode", "development")
        )
        self.start_time = datetime.now()

        # Core AI Brain
        self.central_brain: Optional[CentralAIBrain] = None

        # Integration components
        self.interaction_history: List[UserInteraction] = []
        self.active_sessions: Dict[str, Dict[str, Any]] = {}
        self.system_callbacks: Dict[str, Callable] = {}

        # Performance tracking
        self.metrics = SystemMetrics(
            total_interactions=0,
            successful_interactions=0,
            failed_interactions=0,
            average_response_time=0.0,
            agent_performance={},
            system_uptime=0.0,
            memory_usage={},
            ai_model_performance={},
        )

        # Configuration
        self.max_interaction_history = self.integration_config.get("max_history", 1000)
        self.auto_cleanup_interval = self.integration_config.get(
            "cleanup_interval", 3600
        )
        self.performance_monitoring = self.integration_config.get("monitoring", True)

        logger.info("CentralIntegration initialized")

    async def start(self) -> bool:
        """Start the Central Integration system (alias for initialize)"""
        return await self.initialize()

    async def initialize(self) -> bool:
        """Initialize the complete AI system"""
        try:
            logger.info("🚀 Initializing ALims Central AI Brain Integration...")

            # Initialize Central AI Brain
            self.central_brain = await create_central_brain(self.config)
            if not self.central_brain:
                logger.error("Failed to create Central AI Brain")
                return False

            # Start the Central AI Brain
            await self.central_brain.start()

            # Set up system callbacks
            self._setup_system_callbacks()

            # Start background tasks
            await self._start_background_tasks()

            # Update system state
            self.system_state = SystemState.READY

            logger.info(
                "✅ ALims Central AI Brain Integration initialized successfully"
            )
            return True

        except Exception as e:
            logger.error(f"❌ Failed to initialize Central Integration: {e}")
            self.system_state = SystemState.ERROR
            return False

    def _setup_system_callbacks(self):
        """Set up system-wide callbacks and event handlers"""
        # Voice command callback
        if self.central_brain.voice_interface:
            self.central_brain.voice_interface.set_command_callback(
                self._handle_voice_interaction
            )

        # System event callbacks
        self.system_callbacks = {
            "user_interaction": self._log_user_interaction,
            "agent_response": self._track_agent_performance,
            "system_error": self._handle_system_error,
            "performance_update": self._update_performance_metrics,
        }

        logger.info("System callbacks configured")

    async def _start_background_tasks(self):
        """Start background monitoring and maintenance tasks"""
        # Start performance monitoring
        if self.performance_monitoring:
            asyncio.create_task(self._performance_monitoring_loop())

        # Start cleanup task
        asyncio.create_task(self._cleanup_loop())

        logger.info("Background tasks started")

    async def _performance_monitoring_loop(self):
        """Background task for performance monitoring"""
        while self.system_state != SystemState.SHUTDOWN:
            try:
                await self._update_system_metrics()
                await asyncio.sleep(60)  # Update every minute
            except Exception as e:
                logger.error(f"Performance monitoring error: {e}")
                await asyncio.sleep(60)

    async def _cleanup_loop(self):
        """Background task for system cleanup"""
        while self.system_state != SystemState.SHUTDOWN:
            try:
                await self._cleanup_old_data()
                await asyncio.sleep(self.auto_cleanup_interval)
            except Exception as e:
                logger.error(f"Cleanup task error: {e}")
                await asyncio.sleep(self.auto_cleanup_interval)

    async def process_user_interaction(
        self,
        user_id: str,
        interaction_type: InteractionType,
        input_data: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Process a complete user interaction through the AI system"""
        interaction_id = f"int_{int(time.time())}_{user_id}"
        start_time = time.time()

        try:
            logger.info(f"🎯 Processing user interaction: {interaction_type.value}")

            # Update system state
            self.system_state = SystemState.PROCESSING

            # Create interaction record
            interaction = UserInteraction(
                interaction_id=interaction_id,
                user_id=user_id,
                interaction_type=interaction_type,
                input_data=input_data,
                timestamp=datetime.now(),
                processing_time=0.0,
                agents_involved=[],
                response_data={},
                success=False,
                confidence=0.0,
                context_used={},
            )

            # Route to appropriate processing method
            if interaction_type == InteractionType.TEXT_CHAT:
                result = await self._process_text_chat(interaction)
            elif interaction_type == InteractionType.VOICE_COMMAND:
                result = await self._process_voice_command(interaction)
            elif interaction_type == InteractionType.SYSTEM_COMMAND:
                result = await self._process_system_command(interaction)
            elif interaction_type == InteractionType.TASK_REQUEST:
                result = await self._process_task_request(interaction)
            elif interaction_type == InteractionType.QUERY_REQUEST:
                result = await self._process_query_request(interaction)
            elif interaction_type == InteractionType.TRAINING_REQUEST:
                result = await self._process_training_request(interaction)
            else:
                result = await self._process_generic_interaction(interaction)

            # Finalize interaction
            interaction.processing_time = time.time() - start_time
            interaction.response_data = result
            interaction.success = result.get("success", False)
            interaction.confidence = result.get("confidence", 0.0)

            # Update metrics
            self.metrics.total_interactions += 1
            if interaction.success:
                self.metrics.successful_interactions += 1
            else:
                self.metrics.failed_interactions += 1

            # Store interaction
            self.interaction_history.append(interaction)

            # Update system state
            self.system_state = SystemState.READY

            logger.info(
                f"✅ Interaction processed in {interaction.processing_time:.2f}s"
            )

            return {
                "success": interaction.success,
                "interaction_id": interaction_id,
                "response": result,
                "processing_time": interaction.processing_time,
                "agents_involved": interaction.agents_involved,
                "confidence": interaction.confidence,
            }

        except Exception as e:
            logger.error(f"❌ Failed to process user interaction: {e}")
            self.system_state = SystemState.ERROR

            return {
                "success": False,
                "error": str(e),
                "interaction_id": interaction_id,
                "processing_time": time.time() - start_time,
            }

    async def _process_text_chat(self, interaction: UserInteraction) -> Dict[str, Any]:
        """Process text-based chat interactions"""
        try:
            user_message = interaction.input_data.get("message", "")
            session_id = interaction.input_data.get("session_id", "default")

            # Use UserInterfaceAgent for natural language processing
            response = await self.central_brain.process_user_input(
                user_message, session_id
            )

            interaction.agents_involved.append("UserInterfaceAgent")

            # Get proactive suggestions if enabled
            if self.central_brain.proactive_suggestion_engine:
                suggestions = await self.central_brain.generate_proactive_suggestions(
                    user_id=session_id,
                    context_data={"message": user_message, "session": session_id},
                )
                if suggestions.get("success"):
                    response["suggestions"] = suggestions.get("suggestions", [])
                    interaction.agents_involved.append("ProactiveSuggestionEngine")

            return response

        except Exception as e:
            logger.error(f"Text chat processing error: {e}")
            return {"success": False, "error": str(e)}

    async def _process_voice_command(
        self, interaction: UserInteraction
    ) -> Dict[str, Any]:
        """Process voice command interactions"""
        try:
            voice_command = interaction.input_data.get("voice_command")

            if not voice_command:
                return {"success": False, "error": "No voice command provided"}

            # Process through voice interface
            if self.central_brain.voice_interface:
                # Voice command is already processed, just handle the response
                response = await self.central_brain._handle_voice_command(voice_command)
                interaction.agents_involved.append("VoiceInterface")

                return {
                    "success": True,
                    "message": "Voice command processed",
                    "command_type": voice_command.command_type.value,
                    "confidence": voice_command.confidence,
                }
            else:
                return {"success": False, "error": "Voice interface not available"}

        except Exception as e:
            logger.error(f"Voice command processing error: {e}")
            return {"success": False, "error": str(e)}

    async def _process_system_command(
        self, interaction: UserInteraction
    ) -> Dict[str, Any]:
        """Process system control commands"""
        try:
            command = interaction.input_data.get("command", "")
            parameters = interaction.input_data.get("parameters", {})

            # Use SystemController for safe command execution
            response = await self.central_brain.execute_system_command(
                command, parameters
            )

            interaction.agents_involved.append("SystemController")

            return response

        except Exception as e:
            logger.error(f"System command processing error: {e}")
            return {"success": False, "error": str(e)}

    async def _process_task_request(
        self, interaction: UserInteraction
    ) -> Dict[str, Any]:
        """Process task management requests"""
        try:
            task_data = interaction.input_data.get("task", {})
            action = interaction.input_data.get("action", "create")

            # Use AgentOrchestrator for complex task coordination
            response = await self.central_brain.coordinate_agents(
                task_description=f"Task {action}: {task_data}",
                required_capabilities=["task_management"],
                priority="normal",
            )

            interaction.agents_involved.append("AgentOrchestrator")

            return response

        except Exception as e:
            logger.error(f"Task request processing error: {e}")
            return {"success": False, "error": str(e)}

    async def _process_query_request(
        self, interaction: UserInteraction
    ) -> Dict[str, Any]:
        """Process information query requests"""
        try:
            query = interaction.input_data.get("query", "")
            context = interaction.input_data.get("context", {})

            # Use advanced context management for intelligent responses
            if self.central_brain.advanced_context_manager:
                context_insights = await self.central_brain.analyze_context_patterns(
                    context_data={"query": query, "context": context}
                )
                interaction.agents_involved.append("AdvancedContextManager")

            # Process query through user interface
            response = await self.central_brain.process_user_input(
                query, "query_session"
            )
            interaction.agents_involved.append("UserInterfaceAgent")

            return response

        except Exception as e:
            logger.error(f"Query request processing error: {e}")
            return {"success": False, "error": str(e)}

    async def _process_training_request(
        self, interaction: UserInteraction
    ) -> Dict[str, Any]:
        """Process embryo training requests"""
        try:
            embryo_data = interaction.input_data.get("embryo", {})
            training_type = interaction.input_data.get("training_type", "validation")

            # Use EmbryoTrainer for intelligent training
            if training_type == "validation":
                response = await self.central_brain.validate_embryo_training(
                    embryo_data
                )
            elif training_type == "birth_readiness":
                response = await self.central_brain.assess_birth_readiness(embryo_data)
            else:
                response = {
                    "success": False,
                    "error": f"Unknown training type: {training_type}",
                }

            interaction.agents_involved.append("EmbryoTrainer")

            return response

        except Exception as e:
            logger.error(f"Training request processing error: {e}")
            return {"success": False, "error": str(e)}

    async def _process_generic_interaction(
        self, interaction: UserInteraction
    ) -> Dict[str, Any]:
        """Process generic interactions that don't fit specific categories"""
        try:
            # Default to user interface processing
            message = interaction.input_data.get("message", str(interaction.input_data))
            response = await self.central_brain.process_user_input(
                message, "generic_session"
            )

            interaction.agents_involved.append("UserInterfaceAgent")

            return response

        except Exception as e:
            logger.error(f"Generic interaction processing error: {e}")
            return {"success": False, "error": str(e)}

    async def _handle_voice_interaction(self, voice_command):
        """Handle voice interactions from the voice interface"""
        try:
            # Convert voice command to user interaction
            await self.process_user_interaction(
                user_id="voice_user",
                interaction_type=InteractionType.VOICE_COMMAND,
                input_data={"voice_command": voice_command},
            )
        except Exception as e:
            logger.error(f"Voice interaction handling error: {e}")

    async def start_voice_interface(self) -> Dict[str, Any]:
        """Start the voice interface system"""
        if not self.central_brain or not self.central_brain.voice_interface:
            return {"success": False, "error": "Voice interface not available"}

        return await self.central_brain.start_voice_interface()

    async def stop_voice_interface(self) -> Dict[str, Any]:
        """Stop the voice interface system"""
        if not self.central_brain or not self.central_brain.voice_interface:
            return {"success": False, "error": "Voice interface not available"}

        return await self.central_brain.stop_voice_interface()

    async def get_system_status(self) -> Dict[str, Any]:
        """Get comprehensive system status"""
        try:
            # Get central brain status
            brain_status = {}
            if self.central_brain:
                brain_status = self.central_brain.get_status_summary()

            # Calculate uptime
            uptime = (datetime.now() - self.start_time).total_seconds()

            # Get agent performance
            agent_performance = {}
            if self.central_brain:
                # Get individual agent statuses
                if self.central_brain.pattern_validator:
                    pattern_metrics = (
                        self.central_brain.get_pattern_validation_metrics()
                    )
                    agent_performance["PatternValidator"] = pattern_metrics.get(
                        "metrics", {}
                    )

                if self.central_brain.advanced_context_manager:
                    context_metrics = self.central_brain.get_context_insights()
                    agent_performance["AdvancedContextManager"] = context_metrics.get(
                        "insights", {}
                    )

                if self.central_brain.proactive_suggestion_engine:
                    suggestion_metrics = self.central_brain.get_suggestion_metrics()
                    agent_performance["ProactiveSuggestionEngine"] = (
                        suggestion_metrics.get("metrics", {})
                    )

                if self.central_brain.voice_interface:
                    voice_metrics = self.central_brain.get_voice_metrics()
                    agent_performance["VoiceInterface"] = voice_metrics.get(
                        "metrics", {}
                    )

            return {
                "success": True,
                "system_state": self.system_state.value,
                "integration_mode": self.integration_mode.value,
                "uptime_seconds": uptime,
                "total_interactions": self.metrics.total_interactions,
                "success_rate": (
                    (
                        self.metrics.successful_interactions
                        / self.metrics.total_interactions
                        * 100
                    )
                    if self.metrics.total_interactions > 0
                    else 0
                ),
                "central_brain_status": brain_status,
                "agent_performance": agent_performance,
                "active_sessions": len(self.active_sessions),
                "interaction_history_size": len(self.interaction_history),
            }

        except Exception as e:
            logger.error(f"Error getting system status: {e}")
            return {"success": False, "error": str(e)}

    async def get_interaction_history(
        self, user_id: Optional[str] = None, limit: int = 50
    ) -> Dict[str, Any]:
        """Get user interaction history"""
        try:
            # Filter by user if specified
            if user_id:
                filtered_history = [
                    interaction
                    for interaction in self.interaction_history
                    if interaction.user_id == user_id
                ]
            else:
                filtered_history = self.interaction_history

            # Apply limit
            recent_history = (
                filtered_history[-limit:] if limit > 0 else filtered_history
            )

            # Convert to serializable format
            history_data = []
            for interaction in recent_history:
                history_data.append(
                    {
                        "interaction_id": interaction.interaction_id,
                        "user_id": interaction.user_id,
                        "type": interaction.interaction_type.value,
                        "timestamp": interaction.timestamp.isoformat(),
                        "processing_time": interaction.processing_time,
                        "success": interaction.success,
                        "confidence": interaction.confidence,
                        "agents_involved": interaction.agents_involved,
                    }
                )

            return {
                "success": True,
                "history": history_data,
                "total_interactions": len(filtered_history),
                "returned_count": len(history_data),
            }

        except Exception as e:
            logger.error(f"Error getting interaction history: {e}")
            return {"success": False, "error": str(e)}

    async def _update_system_metrics(self):
        """Update comprehensive system metrics"""
        try:
            # Update uptime
            self.metrics.system_uptime = (
                datetime.now() - self.start_time
            ).total_seconds()

            # Update average response time
            if self.interaction_history:
                total_time = sum(i.processing_time for i in self.interaction_history)
                self.metrics.average_response_time = total_time / len(
                    self.interaction_history
                )

            # Update agent performance metrics
            if self.central_brain:
                self.metrics.agent_performance = {
                    "UserInterfaceAgent": {"status": "operational"},
                    "AgentOrchestrator": {"status": "operational"},
                    "EmbryoTrainer": {"status": "operational"},
                    "SystemController": {"status": "operational"},
                    "PatternValidator": {"status": "operational"},
                    "AdvancedContextManager": {"status": "operational"},
                    "ProactiveSuggestionEngine": {"status": "operational"},
                    "VoiceInterface": {"status": "operational"},
                }

        except Exception as e:
            logger.error(f"Error updating system metrics: {e}")

    async def _cleanup_old_data(self):
        """Clean up old interaction data and optimize memory"""
        try:
            # Limit interaction history size
            if len(self.interaction_history) > self.max_interaction_history:
                # Keep only the most recent interactions
                self.interaction_history = self.interaction_history[
                    -self.max_interaction_history :
                ]
                logger.info(
                    f"Cleaned up interaction history, kept {len(self.interaction_history)} recent interactions"
                )

            # Clean up old sessions
            current_time = datetime.now()
            expired_sessions = []
            for session_id, session_data in self.active_sessions.items():
                last_activity = session_data.get("last_activity", current_time)
                if (
                    current_time - last_activity
                ).total_seconds() > 3600:  # 1 hour timeout
                    expired_sessions.append(session_id)

            for session_id in expired_sessions:
                del self.active_sessions[session_id]

            if expired_sessions:
                logger.info(f"Cleaned up {len(expired_sessions)} expired sessions")

        except Exception as e:
            logger.error(f"Error during cleanup: {e}")

    def _log_user_interaction(self, interaction_data: Dict[str, Any]):
        """Log user interaction for analytics"""
        logger.info(
            f"User interaction logged: {interaction_data.get('type', 'unknown')}"
        )

    def _track_agent_performance(self, agent_data: Dict[str, Any]):
        """Track individual agent performance"""
        agent_name = agent_data.get("agent", "unknown")
        logger.debug(f"Agent performance tracked: {agent_name}")

    def _handle_system_error(self, error_data: Dict[str, Any]):
        """Handle system-wide errors"""
        logger.error(f"System error handled: {error_data.get('error', 'unknown')}")

    def _update_performance_metrics(self, metrics_data: Dict[str, Any]):
        """Update performance metrics"""
        logger.debug("Performance metrics updated")

    async def shutdown(self):
        """Gracefully shutdown the integration system"""
        try:
            logger.info("🛑 Shutting down Central Integration...")

            self.system_state = SystemState.SHUTDOWN

            # Stop voice interface
            if self.central_brain and self.central_brain.voice_interface:
                await self.central_brain.stop_voice_interface()

            # Cleanup final data
            await self._cleanup_old_data()

            logger.info("✅ Central Integration shutdown complete")

        except Exception as e:
            logger.error(f"Error during shutdown: {e}")


# Utility functions
async def create_central_integration(
    config: Dict[str, Any],
) -> Optional[CentralIntegration]:
    """Create and initialize a central integration instance"""
    try:
        integration = CentralIntegration(config)
        return integration
    except Exception as e:
        logger.error(f"Failed to create central integration: {e}")
        return None
