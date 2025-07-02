#!/usr/bin/env python3
"""
ALims Agent-User Interaction Interface

Provides interfaces for users to interact with their AI agents:
- Chat interface for direct communication
- Task delegation and management
- Agent personality customization
- Performance monitoring and feedback
"""

import asyncio
import logging
import json
import time
from typing import Dict, List, Optional, Any, Callable
from datetime import datetime
from dataclasses import dataclass, asdict
from enum import Enum

from ..core.agent_manager import AgentManager, ActiveAgent


class InteractionType(Enum):
    """Types of user-agent interactions"""

    CHAT = "chat"
    TASK_DELEGATION = "task_delegation"
    FEEDBACK = "feedback"
    CUSTOMIZATION = "customization"
    MONITORING = "monitoring"


@dataclass
class UserMessage:
    """User message to agent"""

    content: str
    message_type: InteractionType
    target_agent: Optional[str] = None  # Specific agent or None for auto-select
    context: Dict[str, Any] = None
    timestamp: float = None

    def __post_init__(self):
        if self.timestamp is None:
            self.timestamp = time.time()
        if self.context is None:
            self.context = {}


@dataclass
class AgentResponse:
    """Agent response to user"""

    content: str
    agent_name: str
    agent_specialization: str
    response_type: InteractionType
    confidence: float
    suggested_actions: List[str] = None
    timestamp: float = None

    def __post_init__(self):
        if self.timestamp is None:
            self.timestamp = time.time()
        if self.suggested_actions is None:
            self.suggested_actions = []


@dataclass
class ChatSession:
    """Chat session between user and agents"""

    session_id: str
    start_time: float
    messages: List[Dict[str, Any]]
    active_agents: List[str]
    context: Dict[str, Any]

    def add_message(self, message: UserMessage):
        """Add user message to session"""
        self.messages.append(
            {
                "type": "user",
                "content": message.content,
                "timestamp": message.timestamp,
                "interaction_type": message.message_type.value,
            }
        )

    def add_response(self, response: AgentResponse):
        """Add agent response to session"""
        self.messages.append(
            {
                "type": "agent",
                "content": response.content,
                "agent_name": response.agent_name,
                "specialization": response.agent_specialization,
                "confidence": response.confidence,
                "timestamp": response.timestamp,
                "suggested_actions": response.suggested_actions,
            }
        )


class AgentSelector:
    """Selects the best agent for a given user request"""

    def __init__(self, agent_manager: AgentManager):
        self.agent_manager = agent_manager
        self.logger = logging.getLogger("AgentSelector")

        # Keywords for different specializations
        self.specialization_keywords = {
            "file_operations": [
                "file",
                "folder",
                "directory",
                "save",
                "open",
                "copy",
                "move",
                "delete",
                "organize",
                "backup",
                "sync",
                "search files",
            ],
            "development": [
                "code",
                "programming",
                "debug",
                "compile",
                "git",
                "repository",
                "function",
                "class",
                "variable",
                "algorithm",
                "software",
            ],
            "communication": [
                "email",
                "message",
                "chat",
                "call",
                "meeting",
                "schedule",
                "contact",
                "notification",
                "reminder",
                "calendar",
            ],
            "web_browsing": [
                "website",
                "browser",
                "search",
                "google",
                "internet",
                "url",
                "bookmark",
                "download",
                "online",
                "web page",
            ],
            "creative_work": [
                "design",
                "art",
                "creative",
                "image",
                "photo",
                "video",
                "music",
                "writing",
                "document",
                "presentation",
                "graphics",
            ],
            "app_launches": [
                "application",
                "app",
                "program",
                "software",
                "launch",
                "open",
                "start",
                "run",
                "execute",
                "tool",
            ],
            "temporal_patterns": [
                "time",
                "schedule",
                "calendar",
                "deadline",
                "reminder",
                "routine",
                "habit",
                "daily",
                "weekly",
                "monthly",
            ],
            "system_maintenance": [
                "system",
                "performance",
                "memory",
                "disk",
                "cpu",
                "cleanup",
                "optimize",
                "maintenance",
                "update",
                "backup",
            ],
        }

    async def select_agent(self, message: UserMessage) -> Optional[ActiveAgent]:
        """Select the best agent for handling the user message"""
        try:
            # If specific agent requested, try to find it
            if message.target_agent:
                agents = await self.agent_manager.get_active_agents()
                for agent in agents:
                    if agent.blueprint.name.lower() == message.target_agent.lower():
                        return agent

            # Auto-select based on message content
            return await self._auto_select_agent(message)

        except Exception as e:
            self.logger.error(f"Error selecting agent: {e}")
            return None

    async def _auto_select_agent(self, message: UserMessage) -> Optional[ActiveAgent]:
        """Automatically select best agent based on message content"""
        try:
            agents = await self.agent_manager.get_active_agents()
            if not agents:
                return None

            # Score agents based on specialization match
            agent_scores = []
            message_lower = message.content.lower()

            for agent in agents:
                score = self._calculate_agent_score(agent, message_lower)
                agent_scores.append((agent, score))

            # Sort by score (highest first)
            agent_scores.sort(key=lambda x: x[1], reverse=True)

            # Return best agent if score is above threshold
            if agent_scores and agent_scores[0][1] > 0.3:
                return agent_scores[0][0]

            # If no good match, return highest performing agent
            if agent_scores:
                return max(agents, key=lambda a: a.success_rate)

            return None

        except Exception as e:
            self.logger.error(f"Error in auto-selection: {e}")
            return None

    def _calculate_agent_score(self, agent: ActiveAgent, message_lower: str) -> float:
        """Calculate how well an agent matches the message"""
        specialization = agent.blueprint.specialization
        keywords = self.specialization_keywords.get(specialization, [])

        # Count keyword matches
        matches = sum(1 for keyword in keywords if keyword in message_lower)
        keyword_score = matches / max(len(keywords), 1)

        # Factor in agent performance
        performance_score = agent.success_rate

        # Factor in agent confidence
        confidence_score = agent.blueprint.confidence_threshold / 100.0

        # Weighted combination
        total_score = (
            keyword_score * 0.5 + performance_score * 0.3 + confidence_score * 0.2
        )

        return total_score


class AgentChatInterface:
    """Main interface for chatting with agents"""

    def __init__(self, agent_manager: AgentManager):
        self.agent_manager = agent_manager
        self.agent_selector = AgentSelector(agent_manager)
        self.logger = logging.getLogger("AgentChatInterface")

        # Active chat sessions
        self.active_sessions: Dict[str, ChatSession] = {}
        self.session_counter = 0

        # Response templates
        self.response_templates = {
            "no_agents": "I don't have any active agents yet. Agents will be born as embryos mature and specialize based on your usage patterns.",
            "agent_not_found": "I couldn't find an agent named '{agent_name}'. Available agents: {available_agents}",
            "processing_error": "I encountered an error while processing your request. Please try again.",
            "task_delegated": "I've delegated this task to {agent_name}. They'll work on it and update you on progress.",
            "general_help": """I'm ALims, your AI operating system! Here's how you can interact with me:

🤖 **Chat with Agents**: Just type naturally - I'll route your message to the best agent
📋 **Delegate Tasks**: Say "Please [task]" and I'll assign it to the right specialist
⚙️ **Customize Agents**: Ask to modify agent behavior or preferences
📊 **Monitor Performance**: Ask about agent status, performance, or system health

Try saying:
• "Help me organize my files"
• "Show me my active agents"
• "What tasks are you working on?"
• "How is the system performing?"
""",
        }

    async def start_chat_session(self, context: Dict[str, Any] = None) -> str:
        """Start a new chat session"""
        self.session_counter += 1
        session_id = f"chat_{self.session_counter}_{int(time.time())}"

        session = ChatSession(
            session_id=session_id,
            start_time=time.time(),
            messages=[],
            active_agents=[],
            context=context or {},
        )

        self.active_sessions[session_id] = session

        # Add welcome message
        welcome_response = AgentResponse(
            content=self.response_templates["general_help"],
            agent_name="ALims System",
            agent_specialization="general",
            response_type=InteractionType.CHAT,
            confidence=1.0,
        )

        session.add_response(welcome_response)

        self.logger.info(f"Started chat session: {session_id}")
        return session_id

    async def send_message(
        self, session_id: str, message: UserMessage
    ) -> AgentResponse:
        """Send message to agents and get response"""
        try:
            session = self.active_sessions.get(session_id)
            if not session:
                raise ValueError(f"Chat session {session_id} not found")

            # Add message to session
            session.add_message(message)

            # Process message based on type
            if message.message_type == InteractionType.CHAT:
                response = await self._handle_chat_message(message)
            elif message.message_type == InteractionType.TASK_DELEGATION:
                response = await self._handle_task_delegation(message)
            elif message.message_type == InteractionType.FEEDBACK:
                response = await self._handle_feedback(message)
            elif message.message_type == InteractionType.CUSTOMIZATION:
                response = await self._handle_customization(message)
            elif message.message_type == InteractionType.MONITORING:
                response = await self._handle_monitoring(message)
            else:
                response = await self._handle_chat_message(message)  # Default to chat

            # Add response to session
            session.add_response(response)

            return response

        except Exception as e:
            self.logger.error(f"Error processing message: {e}")
            return AgentResponse(
                content=self.response_templates["processing_error"],
                agent_name="ALims System",
                agent_specialization="error_handling",
                response_type=message.message_type,
                confidence=0.5,
            )

    async def _handle_chat_message(self, message: UserMessage) -> AgentResponse:
        """Handle general chat message"""
        # Check for system commands
        content_lower = message.content.lower().strip()

        if any(
            phrase in content_lower
            for phrase in ["help", "what can you do", "how do i"]
        ):
            return AgentResponse(
                content=self.response_templates["general_help"],
                agent_name="ALims System",
                agent_specialization="help",
                response_type=InteractionType.CHAT,
                confidence=1.0,
            )

        if any(
            phrase in content_lower
            for phrase in ["show agents", "list agents", "active agents"]
        ):
            return await self._show_active_agents()

        if any(
            phrase in content_lower
            for phrase in ["system status", "how are you", "status"]
        ):
            return await self._show_system_status()

        # Route to appropriate agent
        selected_agent = await self.agent_selector.select_agent(message)

        if not selected_agent:
            agents = await self.agent_manager.get_active_agents()
            if not agents:
                return AgentResponse(
                    content=self.response_templates["no_agents"],
                    agent_name="ALims System",
                    agent_specialization="system",
                    response_type=InteractionType.CHAT,
                    confidence=0.8,
                )
            else:
                # No good match, provide general response
                return AgentResponse(
                    content=f"I have {len(agents)} active agents, but I'm not sure which one would be best for your request. Could you be more specific about what you need help with?",
                    agent_name="ALims System",
                    agent_specialization="routing",
                    response_type=InteractionType.CHAT,
                    confidence=0.6,
                    suggested_actions=[
                        "Ask about file operations",
                        "Request development help",
                        "Ask for creative assistance",
                        "Request system maintenance",
                    ],
                )

        # Generate agent response
        return await self._generate_agent_response(selected_agent, message)

    async def _handle_task_delegation(self, message: UserMessage) -> AgentResponse:
        """Handle task delegation"""
        selected_agent = await self.agent_selector.select_agent(message)

        if not selected_agent:
            return AgentResponse(
                content="I don't have a suitable agent available for this task right now.",
                agent_name="ALims System",
                agent_specialization="task_management",
                response_type=InteractionType.TASK_DELEGATION,
                confidence=0.5,
            )

        # Simulate task delegation
        task_response = self.response_templates["task_delegated"].format(
            agent_name=selected_agent.blueprint.name
        )

        return AgentResponse(
            content=f"{task_response}\n\n{selected_agent.blueprint.introduction}",
            agent_name=selected_agent.blueprint.name,
            agent_specialization=selected_agent.blueprint.specialization,
            response_type=InteractionType.TASK_DELEGATION,
            confidence=selected_agent.blueprint.confidence_threshold / 100.0,
            suggested_actions=[
                "Check task progress",
                "Modify task requirements",
                "Cancel task",
            ],
        )

    async def _handle_feedback(self, message: UserMessage) -> AgentResponse:
        """Handle user feedback"""
        return AgentResponse(
            content="Thank you for your feedback! I'm learning from your input to improve my assistance. Your feedback helps me understand your preferences and work style better.",
            agent_name="ALims System",
            agent_specialization="learning",
            response_type=InteractionType.FEEDBACK,
            confidence=0.9,
        )

    async def _handle_customization(self, message: UserMessage) -> AgentResponse:
        """Handle agent customization requests"""
        return AgentResponse(
            content="Agent customization features are coming soon! You'll be able to adjust agent personalities, preferences, and behavior patterns to better match your workflow.",
            agent_name="ALims System",
            agent_specialization="customization",
            response_type=InteractionType.CUSTOMIZATION,
            confidence=0.7,
            suggested_actions=[
                "View current agent settings",
                "Request specific customizations",
                "Reset agent to defaults",
            ],
        )

    async def _handle_monitoring(self, message: UserMessage) -> AgentResponse:
        """Handle monitoring requests"""
        return await self._show_system_status()

    async def _show_active_agents(self) -> AgentResponse:
        """Show information about active agents"""
        try:
            agents = await self.agent_manager.get_active_agents()

            if not agents:
                return AgentResponse(
                    content=self.response_templates["no_agents"],
                    agent_name="ALims System",
                    agent_specialization="system",
                    response_type=InteractionType.MONITORING,
                    confidence=1.0,
                )

            agent_info = []
            for agent in agents:
                info = f"""🤖 **{agent.blueprint.name}**
Specialization: {agent.blueprint.specialization.replace('_', ' ').title()}
Autonomy: {agent.blueprint.autonomy_level.title()}
Success Rate: {agent.success_rate:.1%}
Tasks Completed: {agent.task_count}

*"{agent.blueprint.introduction}"*"""
                agent_info.append(info)

            content = f"**Active Agents ({len(agents)}):**\n\n" + "\n\n---\n\n".join(
                agent_info
            )

            return AgentResponse(
                content=content,
                agent_name="ALims System",
                agent_specialization="monitoring",
                response_type=InteractionType.MONITORING,
                confidence=1.0,
            )

        except Exception as e:
            self.logger.error(f"Error showing agents: {e}")
            return AgentResponse(
                content="Error retrieving agent information.",
                agent_name="ALims System",
                agent_specialization="error_handling",
                response_type=InteractionType.MONITORING,
                confidence=0.5,
            )

    async def _show_system_status(self) -> AgentResponse:
        """Show system status information"""
        try:
            status = await self.agent_manager.get_system_status()
            system_info = status.get("system", {})
            embryo_info = status.get("embryo_pool", {})

            content = f"""**ALims System Status:**

🤖 **Agents:**
• Active: {system_info.get('active_agents', 0)}
• Total Births: {system_info.get('total_births', 0)}
• Retirements: {system_info.get('total_retirements', 0)}

🧬 **Embryo Pool:**
• Active Embryos: {embryo_info.get('active_embryos', 0)}
• Events Processed: {embryo_info.get('events_processed', 0)}
• Generation: {embryo_info.get('generation', 0)}

⏱️ **System:**
• Uptime: {system_info.get('uptime', 'Unknown')}
• Status: Healthy ✅

The system is learning from your patterns and evolving specialized agents to assist you!"""

            return AgentResponse(
                content=content,
                agent_name="ALims System",
                agent_specialization="monitoring",
                response_type=InteractionType.MONITORING,
                confidence=1.0,
            )

        except Exception as e:
            self.logger.error(f"Error getting system status: {e}")
            return AgentResponse(
                content="Error retrieving system status.",
                agent_name="ALims System",
                agent_specialization="error_handling",
                response_type=InteractionType.MONITORING,
                confidence=0.5,
            )

    async def _generate_agent_response(
        self, agent: ActiveAgent, message: UserMessage
    ) -> AgentResponse:
        """Generate response from selected agent"""
        # This is a simplified response generator
        # In a full implementation, this would interface with the actual agent AI

        specialization_responses = {
            "file_operations": [
                "I can help you organize, search, and manage your files efficiently.",
                "Let me assist you with file operations and organization.",
                "I specialize in keeping your files organized and accessible.",
            ],
            "development": [
                "I'm here to help with your coding and development tasks.",
                "Let me assist you with programming and software development.",
                "I can help debug, optimize, and improve your code.",
            ],
            "communication": [
                "I can help you manage communications and stay connected.",
                "Let me assist with your messaging and communication needs.",
                "I specialize in keeping your communications organized.",
            ],
            "creative_work": [
                "I'm here to spark your creativity and help with creative projects.",
                "Let me assist you with your creative endeavors.",
                "I can help bring your creative ideas to life.",
            ],
            "web_browsing": [
                "I can help you navigate the web and find information efficiently.",
                "Let me assist with your browsing and research needs.",
                "I specialize in web navigation and information gathering.",
            ],
            "system_maintenance": [
                "I can help keep your system running smoothly and efficiently.",
                "Let me assist with system optimization and maintenance.",
                "I specialize in system health and performance.",
            ],
        }

        responses = specialization_responses.get(
            agent.blueprint.specialization,
            ["I'm here to help you with whatever you need."],
        )

        # Select response based on agent personality
        import random

        response_text = random.choice(responses)

        return AgentResponse(
            content=f"{response_text}\n\n{agent.blueprint.introduction}",
            agent_name=agent.blueprint.name,
            agent_specialization=agent.blueprint.specialization,
            response_type=InteractionType.CHAT,
            confidence=agent.blueprint.confidence_threshold / 100.0,
            suggested_actions=[
                f"Ask about {agent.blueprint.specialization.replace('_', ' ')}",
                "Delegate a specific task",
                "Provide feedback on assistance",
            ],
        )

    def get_session_history(self, session_id: str) -> Optional[Dict[str, Any]]:
        """Get chat session history"""
        session = self.active_sessions.get(session_id)
        if not session:
            return None

        return {
            "session_id": session.session_id,
            "start_time": session.start_time,
            "duration": time.time() - session.start_time,
            "message_count": len(session.messages),
            "active_agents": session.active_agents,
            "messages": session.messages,
        }

    def close_session(self, session_id: str):
        """Close a chat session"""
        if session_id in self.active_sessions:
            del self.active_sessions[session_id]
            self.logger.info(f"Closed chat session: {session_id}")


def create_agent_interface(agent_manager: AgentManager) -> AgentChatInterface:
    """Create and return the agent chat interface"""
    return AgentChatInterface(agent_manager)
