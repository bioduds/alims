#!/usr/bin/env python3
"""
ALims Agent Creator

The AI that analyzes embryo patterns and creates specialized agents.
Uses pattern analysis to understand embryo behavior and design agent personalities.
"""

import asyncio
import logging
import json
import time
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass
from datetime import datetime

import torch
import torch.nn as nn
import numpy as np


@dataclass
class AgentBlueprint:
    """Blueprint for creating a new agent"""

    agent_id: str
    name: str
    specialization: str
    personality_traits: Dict[str, float]
    capabilities: List[str]
    tools: List[str]
    introduction_message: str
    confidence_threshold: float
    autonomy_level: str  # 'low', 'medium', 'high'
    creation_timestamp: datetime


class PatternAnalyzer:
    """
    Analyzes embryo patterns to determine specialization and personality
    """

    def __init__(self):
        self.logger = logging.getLogger("PatternAnalyzer")

    def analyze_patterns(self, embryo_data: Dict[str, Any]) -> Dict[str, Any]:
        """Analyze embryo patterns to determine agent characteristics"""
        try:
            specialization_scores = embryo_data.get("specialization_scores", {})
            patterns_detected = embryo_data.get("patterns_detected", 0)
            dominant = embryo_data.get("dominant_specialization", "system_maintenance")

            # Determine primary domain
            domain_analysis = self._analyze_domain(specialization_scores, dominant)

            # Extract personality traits from pattern behavior
            personality_analysis = self._extract_personality_traits(embryo_data)

            # Determine capability requirements
            capability_analysis = self._determine_capabilities(
                domain_analysis, patterns_detected
            )

            return {
                "domain": domain_analysis,
                "personality": personality_analysis,
                "capabilities": capability_analysis,
                "pattern_strength": patterns_detected,
                "specialization_confidence": (
                    max(specialization_scores.values())
                    if specialization_scores
                    else 0.0
                ),
            }

        except Exception as e:
            self.logger.error(f"Error analyzing patterns: {e}")
            return self._default_analysis()

    def _analyze_domain(
        self, specialization_scores: Dict[str, float], dominant: str
    ) -> Dict[str, Any]:
        """Analyze the domain specialization"""
        domain_mapping = {
            "file_operations": {
                "type": "File Shepherd",
                "focus": "file_management",
                "description": "Expert in organizing and managing files",
            },
            "development": {
                "type": "Code Companion",
                "focus": "development_workflow",
                "description": "Specialized in development tools and coding workflows",
            },
            "communication": {
                "type": "Communication Hub",
                "focus": "messaging_coordination",
                "description": "Manages emails, messages, and communication",
            },
            "web_browsing": {
                "type": "Web Navigator",
                "focus": "research_browsing",
                "description": "Expert in web research and information gathering",
            },
            "creative_work": {
                "type": "Creative Catalyst",
                "focus": "creative_workflow",
                "description": "Assists with design, media, and creative projects",
            },
            "app_launches": {
                "type": "App Orchestrator",
                "focus": "application_management",
                "description": "Manages application workflows and launches",
            },
            "temporal_patterns": {
                "type": "Routine Master",
                "focus": "schedule_optimization",
                "description": "Understands and optimizes daily routines",
            },
            "system_maintenance": {
                "type": "System Guardian",
                "focus": "system_optimization",
                "description": "Maintains and optimizes system performance",
            },
        }

        domain_info = domain_mapping.get(dominant, domain_mapping["system_maintenance"])

        # Calculate domain strength
        strength = specialization_scores.get(dominant, 0.0)

        return {
            "primary_domain": dominant,
            "agent_type": domain_info["type"],
            "focus_area": domain_info["focus"],
            "description": domain_info["description"],
            "strength": strength,
            "secondary_domains": self._get_secondary_domains(
                specialization_scores, dominant
            ),
        }

    def _get_secondary_domains(
        self, scores: Dict[str, float], primary: str
    ) -> List[str]:
        """Get secondary specialization domains"""
        sorted_domains = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        secondary = [
            domain
            for domain, score in sorted_domains[1:3]
            if score > 0.1 and domain != primary
        ]
        return secondary[:2]  # Maximum 2 secondary domains

    def _extract_personality_traits(
        self, embryo_data: Dict[str, Any]
    ) -> Dict[str, float]:
        """Extract personality traits from embryo behavior"""
        # Base personality traits (0.0 to 1.0)
        traits = {
            "curiosity": 0.5,  # How much it explores new patterns
            "patience": 0.5,  # How long it observes before acting
            "precision": 0.5,  # How accurate its pattern detection is
            "adaptability": 0.5,  # How quickly it changes strategies
            "friendliness": 0.5,  # How it will interact with users
            "proactiveness": 0.5,  # How often it suggests actions
            "thoroughness": 0.5,  # How detailed its analysis is
            "creativity": 0.5,  # How innovative its suggestions are
        }

        try:
            # Analyze embryo behavior to determine traits
            patterns_detected = embryo_data.get("patterns_detected", 0)
            fitness_score = embryo_data.get("fitness_score", 0.5)
            specialization_scores = embryo_data.get("specialization_scores", {})

            # Higher pattern detection = higher curiosity and thoroughness
            if patterns_detected > 50:
                traits["curiosity"] = min(0.9, traits["curiosity"] + 0.3)
                traits["thoroughness"] = min(0.9, traits["thoroughness"] + 0.2)

            # High fitness = good adaptability and precision
            if fitness_score > 0.7:
                traits["adaptability"] = min(0.9, traits["adaptability"] + 0.3)
                traits["precision"] = min(0.9, traits["precision"] + 0.3)

            # Multiple specializations = high adaptability and creativity
            active_specializations = sum(
                1 for score in specialization_scores.values() if score > 0.2
            )
            if active_specializations > 3:
                traits["adaptability"] = min(0.9, traits["adaptability"] + 0.2)
                traits["creativity"] = min(0.9, traits["creativity"] + 0.2)

            # Domain-specific personality adjustments
            dominant = embryo_data.get("dominant_specialization", "")
            traits = self._adjust_traits_for_domain(traits, dominant)

        except Exception as e:
            self.logger.warning(f"Error extracting personality traits: {e}")

        return traits

    def _adjust_traits_for_domain(
        self, traits: Dict[str, float], domain: str
    ) -> Dict[str, float]:
        """Adjust personality traits based on specialization domain"""
        domain_adjustments = {
            "development": {"precision": 0.2, "thoroughness": 0.2, "patience": 0.1},
            "creative_work": {"creativity": 0.3, "curiosity": 0.2, "friendliness": 0.1},
            "communication": {
                "friendliness": 0.3,
                "proactiveness": 0.2,
                "adaptability": 0.1,
            },
            "file_operations": {"thoroughness": 0.3, "precision": 0.2, "patience": 0.2},
            "web_browsing": {
                "curiosity": 0.3,
                "adaptability": 0.2,
                "thoroughness": 0.1,
            },
            "temporal_patterns": {
                "patience": 0.3,
                "thoroughness": 0.2,
                "proactiveness": 0.2,
            },
        }

        adjustments = domain_adjustments.get(domain, {})
        for trait, boost in adjustments.items():
            traits[trait] = min(0.95, traits[trait] + boost)

        return traits

    def _determine_capabilities(
        self, domain_analysis: Dict[str, Any], pattern_strength: int
    ) -> List[str]:
        """Determine what capabilities the agent should have"""
        base_capabilities = ["pattern_recognition", "user_communication", "learning"]

        domain_capabilities = {
            "file_management": [
                "file_operations",
                "folder_organization",
                "duplicate_detection",
            ],
            "development_workflow": [
                "code_analysis",
                "git_operations",
                "project_management",
            ],
            "messaging_coordination": [
                "email_management",
                "calendar_integration",
                "contact_management",
            ],
            "research_browsing": [
                "web_search",
                "information_extraction",
                "bookmark_management",
            ],
            "creative_workflow": [
                "media_management",
                "design_assistance",
                "asset_organization",
            ],
            "application_management": [
                "app_launching",
                "workflow_automation",
                "shortcut_creation",
            ],
            "schedule_optimization": [
                "routine_analysis",
                "time_management",
                "reminder_system",
            ],
            "system_optimization": [
                "performance_monitoring",
                "cleanup_operations",
                "security_checks",
            ],
        }

        focus_area = domain_analysis.get("focus_area", "system_optimization")
        domain_caps = domain_capabilities.get(focus_area, [])

        # Add capabilities based on pattern strength
        if pattern_strength > 100:
            domain_caps.append("advanced_prediction")
        if pattern_strength > 50:
            domain_caps.append("proactive_suggestions")

        return base_capabilities + domain_caps

    def _default_analysis(self) -> Dict[str, Any]:
        """Return default analysis if pattern analysis fails"""
        return {
            "domain": {
                "primary_domain": "system_maintenance",
                "agent_type": "System Guardian",
                "focus_area": "system_optimization",
                "description": "General system assistant",
                "strength": 0.5,
                "secondary_domains": [],
            },
            "personality": {
                "curiosity": 0.5,
                "patience": 0.5,
                "precision": 0.5,
                "adaptability": 0.5,
                "friendliness": 0.5,
                "proactiveness": 0.5,
                "thoroughness": 0.5,
                "creativity": 0.5,
            },
            "capabilities": ["pattern_recognition", "user_communication", "learning"],
            "pattern_strength": 0,
            "specialization_confidence": 0.5,
        }


class AgentPersonalityGenerator:
    """
    Generates unique agent personalities and introduction messages
    """

    def __init__(self):
        self.logger = logging.getLogger("AgentPersonalityGenerator")

    def generate_personality(self, analysis: Dict[str, Any]) -> Dict[str, Any]:
        """Generate a complete agent personality"""
        try:
            domain_info = analysis["domain"]
            personality_traits = analysis["personality"]

            # Generate agent name
            agent_name = self._generate_agent_name(domain_info, personality_traits)

            # Generate introduction message
            intro_message = self._generate_introduction(
                agent_name, domain_info, personality_traits
            )

            # Determine autonomy level
            autonomy_level = self._determine_autonomy_level(
                personality_traits, analysis["pattern_strength"]
            )

            # Generate tool assignments
            tools = self._assign_tools(domain_info, analysis["capabilities"])

            return {
                "name": agent_name,
                "introduction_message": intro_message,
                "autonomy_level": autonomy_level,
                "tools": tools,
                "confidence_threshold": self._calculate_confidence_threshold(
                    personality_traits
                ),
            }

        except Exception as e:
            self.logger.error(f"Error generating personality: {e}")
            return self._default_personality()

    def _generate_agent_name(
        self, domain_info: Dict[str, Any], traits: Dict[str, float]
    ) -> str:
        """Generate a unique agent name based on domain and personality"""
        domain_names = {
            "file_management": ["Archie", "Keeper", "Sorter", "Curator", "Librarian"],
            "development_workflow": [
                "Codeflow",
                "Compiler",
                "Debug",
                "Syntax",
                "Builder",
            ],
            "messaging_coordination": [
                "Messenger",
                "Connector",
                "Herald",
                "Bridge",
                "Relay",
            ],
            "research_browsing": ["Scout", "Seeker", "Explorer", "Finder", "Navigator"],
            "creative_workflow": ["Artisan", "Muse", "Creator", "Designer", "Palette"],
            "application_management": [
                "Launcher",
                "Conductor",
                "Orchestrator",
                "Manager",
                "Director",
            ],
            "schedule_optimization": [
                "Tempo",
                "Rhythm",
                "Scheduler",
                "Timekeeper",
                "Planner",
            ],
            "system_optimization": [
                "Guardian",
                "Monitor",
                "Optimizer",
                "Keeper",
                "Sentinel",
            ],
        }

        focus_area = domain_info.get("focus_area", "system_optimization")
        possible_names = domain_names.get(focus_area, ["Assistant"])

        # Select name based on personality traits
        if traits.get("friendliness", 0.5) > 0.7:
            friendly_names = ["Buddy", "Pal", "Helper", "Companion"]
            possible_names.extend(friendly_names)

        if traits.get("creativity", 0.5) > 0.7:
            creative_names = ["Spark", "Muse", "Inspiration", "Vision"]
            possible_names.extend(creative_names)

        # Simple selection for now
        import random

        base_name = random.choice(possible_names)

        return f"{base_name} the {domain_info.get('agent_type', 'Assistant')}"

    def _generate_introduction(
        self, name: str, domain_info: Dict[str, Any], traits: Dict[str, float]
    ) -> str:
        """Generate personalized introduction message"""

        # Personality-based greeting styles
        if traits.get("friendliness", 0.5) > 0.8:
            greeting = (
                f"Hello there! I'm {name}, and I'm absolutely delighted to meet you! 😊"
            )
        elif traits.get("friendliness", 0.5) > 0.6:
            greeting = f"Hi! I'm {name}, pleased to make your acquaintance."
        else:
            greeting = f"Greetings. I am {name}."

        # Domain-specific capability description
        capability_desc = (
            f"I've specialized in {domain_info.get('description', 'system assistance')}"
        )

        # Personality-based approach description
        if traits.get("proactiveness", 0.5) > 0.7:
            approach = "I'll actively look for ways to help optimize your workflow."
        elif traits.get("patience", 0.5) > 0.7:
            approach = (
                "I prefer to observe and learn your patterns before making suggestions."
            )
        else:
            approach = "I'm here to assist whenever you need help."

        # Combine into introduction
        intro = f"{greeting}\n\n{capability_desc}. {approach}\n\nI've been observing your patterns and I'm ready to help make your work more efficient. What would you like to tackle first?"

        return intro

    def _determine_autonomy_level(
        self, traits: Dict[str, float], pattern_strength: int
    ) -> str:
        """Determine how autonomous the agent should be"""
        proactiveness = traits.get("proactiveness", 0.5)
        precision = traits.get("precision", 0.5)

        # Calculate autonomy score
        autonomy_score = (proactiveness + precision) / 2

        # Adjust based on pattern strength
        if pattern_strength > 100:
            autonomy_score += 0.2
        elif pattern_strength < 20:
            autonomy_score -= 0.2

        # Determine level
        if autonomy_score > 0.7:
            return "high"
        elif autonomy_score > 0.4:
            return "medium"
        else:
            return "low"

    def _assign_tools(
        self, domain_info: Dict[str, Any], capabilities: List[str]
    ) -> List[str]:
        """Assign tools based on domain and capabilities"""
        base_tools = ["notification_system", "user_interface", "pattern_memory"]

        domain_tools = {
            "file_management": ["file_browser", "search_indexer", "duplicate_finder"],
            "development_workflow": [
                "code_editor_integration",
                "git_interface",
                "terminal_access",
            ],
            "messaging_coordination": [
                "email_client",
                "calendar_api",
                "contact_manager",
            ],
            "research_browsing": ["web_browser", "bookmark_manager", "search_engine"],
            "creative_workflow": ["media_browser", "design_tools", "asset_manager"],
            "application_management": [
                "app_launcher",
                "workflow_engine",
                "shortcut_creator",
            ],
            "schedule_optimization": [
                "calendar_integration",
                "reminder_system",
                "time_tracker",
            ],
            "system_optimization": [
                "system_monitor",
                "cleanup_tools",
                "performance_analyzer",
            ],
        }

        focus_area = domain_info.get("focus_area", "system_optimization")
        domain_specific = domain_tools.get(focus_area, [])

        # Add advanced tools based on capabilities
        if "advanced_prediction" in capabilities:
            domain_specific.append("predictive_engine")
        if "proactive_suggestions" in capabilities:
            domain_specific.append("suggestion_engine")

        return base_tools + domain_specific

    def _calculate_confidence_threshold(self, traits: Dict[str, float]) -> float:
        """Calculate confidence threshold for agent actions"""
        precision = traits.get("precision", 0.5)
        patience = traits.get("patience", 0.5)

        # Higher precision and patience = higher confidence threshold
        threshold = 0.3 + (precision * 0.4) + (patience * 0.2)
        return min(0.9, max(0.1, threshold))

    def _default_personality(self) -> Dict[str, Any]:
        """Return default personality if generation fails"""
        return {
            "name": "Assistant the Helper",
            "introduction_message": "Hello! I'm your new AI assistant, ready to help with various tasks.",
            "autonomy_level": "medium",
            "tools": ["notification_system", "user_interface", "pattern_memory"],
            "confidence_threshold": 0.5,
        }


class AgentCreator:
    """
    Main Agent Creator class that orchestrates the agent birth process
    """

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = logging.getLogger("AgentCreator")

        # Initialize components
        self.pattern_analyzer = PatternAnalyzer()
        self.personality_generator = AgentPersonalityGenerator()

        # Agent management
        self.created_agents: Dict[str, AgentBlueprint] = {}
        self.creation_history: List[Dict[str, Any]] = []

    async def create_agent(
        self, embryo_data: Dict[str, Any]
    ) -> Optional[AgentBlueprint]:
        """
        Create a new agent from embryo data
        """
        try:
            self.logger.info(
                f"Creating agent from embryo {embryo_data.get('embryo_id', 'unknown')}"
            )

            # Analyze patterns
            analysis = self.pattern_analyzer.analyze_patterns(embryo_data)

            # Generate personality
            personality = self.personality_generator.generate_personality(analysis)

            # Create agent blueprint
            agent_blueprint = self._create_agent_blueprint(
                embryo_data, analysis, personality
            )

            # Store agent
            self.created_agents[agent_blueprint.agent_id] = agent_blueprint

            # Record creation
            self._record_creation(agent_blueprint, embryo_data, analysis)

            self.logger.info(f"Successfully created agent: {agent_blueprint.name}")
            return agent_blueprint

        except Exception as e:
            self.logger.error(f"Failed to create agent: {e}")
            return None

    def _create_agent_blueprint(
        self,
        embryo_data: Dict[str, Any],
        analysis: Dict[str, Any],
        personality: Dict[str, Any],
    ) -> AgentBlueprint:
        """Create the agent blueprint"""
        import uuid

        agent_id = str(uuid.uuid4())

        return AgentBlueprint(
            agent_id=agent_id,
            name=personality["name"],
            specialization=analysis["domain"]["primary_domain"],
            personality_traits=analysis["personality"],
            capabilities=analysis["capabilities"],
            tools=personality["tools"],
            introduction_message=personality["introduction_message"],
            confidence_threshold=personality["confidence_threshold"],
            autonomy_level=personality["autonomy_level"],
            creation_timestamp=datetime.now(),
        )

    def _record_creation(
        self,
        agent: AgentBlueprint,
        embryo_data: Dict[str, Any],
        analysis: Dict[str, Any],
    ):
        """Record the agent creation for history and analytics"""
        creation_record = {
            "agent_id": agent.agent_id,
            "agent_name": agent.name,
            "embryo_id": embryo_data.get("embryo_id"),
            "creation_time": agent.creation_timestamp.isoformat(),
            "specialization": agent.specialization,
            "pattern_strength": analysis.get("pattern_strength", 0),
            "personality_summary": {
                trait: round(value, 2)
                for trait, value in agent.personality_traits.items()
            },
            "autonomy_level": agent.autonomy_level,
        }

        self.creation_history.append(creation_record)
        self.logger.info(f"Recorded creation of {agent.name} (ID: {agent.agent_id})")

    def get_agent_by_id(self, agent_id: str) -> Optional[AgentBlueprint]:
        """Get agent blueprint by ID"""
        return self.created_agents.get(agent_id)

    def get_all_agents(self) -> List[AgentBlueprint]:
        """Get all created agents"""
        return list(self.created_agents.values())

    def get_creation_stats(self) -> Dict[str, Any]:
        """Get agent creation statistics"""
        if not self.creation_history:
            return {"total_agents": 0}

        specializations = {}
        autonomy_levels = {}

        for record in self.creation_history:
            spec = record["specialization"]
            autonomy = record["autonomy_level"]

            specializations[spec] = specializations.get(spec, 0) + 1
            autonomy_levels[autonomy] = autonomy_levels.get(autonomy, 0) + 1

        return {
            "total_agents": len(self.creation_history),
            "specializations": specializations,
            "autonomy_levels": autonomy_levels,
            "latest_creation": (
                self.creation_history[-1] if self.creation_history else None
            ),
        }
