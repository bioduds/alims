#!/usr/bin/env python3
"""
ALims Agent Manager

Coordinates the entire agent lifecycle:
- Monitors embryo pool maturity
- Triggers agent births via Agent Creator
- Manages active agents
- Handles agent retirement and replacement
"""

import asyncio
import logging
import json
from typing import Dict, List, Optional, Any
from datetime import datetime, timedelta
from dataclasses import dataclass, asdict

from .embryo_pool import EmbryoPool, AgentEmbryo
from .agent_creator import AgentCreator, AgentBlueprint


@dataclass
class ActiveAgent:
    """Represents an active agent in the system"""

    blueprint: AgentBlueprint
    creation_time: datetime
    last_activity: datetime
    task_count: int = 0
    success_rate: float = 0.0
    user_satisfaction: float = 0.0
    active: bool = True


class AgentManager:
    """
    Orchestrates the complete agent lifecycle from embryo to retirement
    """

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = logging.getLogger("AgentManager")

        # Core components
        self.embryo_pool = EmbryoPool(config)
        self.agent_creator = AgentCreator(config)

        # Agent management
        self.active_agents: Dict[str, ActiveAgent] = {}
        self.agent_history: List[Dict[str, Any]] = []

        # Configuration
        self.max_active_agents = config.get("max_active_agents", 5)
        self.agent_birth_threshold = config.get("agent_birth_threshold", 50)
        self.agent_retirement_threshold = config.get("agent_retirement_threshold", 0.3)

        # Lifecycle tracking
        self.total_births = 0
        self.total_retirements = 0
        self.system_start_time = datetime.now()

    async def start(self):
        """Start the agent management system"""
        self.logger.info("🚀 Starting ALims Agent Management System...")

        # Start embryo pool
        await self.embryo_pool.start()

        # Start monitoring loop
        self._monitoring_task = asyncio.create_task(self._monitor_lifecycle())

        self.logger.info("✅ Agent Management System started successfully")

    async def start_without_embryo_pool(self):
        """Start the agent management system without starting embryo pool

        Used when embryo pool is managed externally by system integration
        """
        self.logger.info("🚀 Starting ALims Agent Management System...")

        # Skip embryo pool start - managed externally
        self.logger.info("📋 Embryo pool managed by system integration")

        # Start monitoring loop
        self._monitoring_task = asyncio.create_task(self._monitor_lifecycle())

        self.logger.info("✅ Agent Management System started successfully")

    async def stop(self):
        """Stop the agent management system"""
        self.logger.info("🛑 Stopping Agent Management System...")

        # Stop monitoring
        if hasattr(self, "_monitoring_task"):
            self._monitoring_task.cancel()

        # Stop embryo pool
        await self.embryo_pool.stop()

        self.logger.info("✅ Agent Management System stopped")

    async def _monitor_lifecycle(self):
        """Monitor embryo pool and manage agent lifecycle"""
        try:
            while True:
                # Check for embryos ready for birth
                await self._check_for_births()

                # Monitor active agent performance
                await self._monitor_agent_performance()

                # Check for agent retirements
                await self._check_for_retirements()

                # Wait before next check
                await asyncio.sleep(30)  # Check every 30 seconds

        except asyncio.CancelledError:
            self.logger.info("Lifecycle monitoring cancelled")
        except Exception as e:
            self.logger.error(f"Error in lifecycle monitoring: {e}")

    async def _check_for_births(self):
        """Check if any embryos are ready for agent birth"""
        try:
            # Check if we have room for more agents
            if len(self.active_agents) >= self.max_active_agents:
                return

            # Get mature embryos from pool
            embryo_stats = self.embryo_pool.get_pool_status()

            for embryo_data in embryo_stats.get("embryos", []):
                patterns_detected = embryo_data.get("patterns_detected", 0)
                fitness_score = embryo_data.get("fitness_score", 0.0)

                # Check if embryo is ready for birth
                if (
                    patterns_detected >= self.agent_birth_threshold
                    and fitness_score > 0.7
                ):

                    await self._birth_agent(embryo_data)
                    break  # Only birth one agent per cycle

        except Exception as e:
            self.logger.error(f"Error checking for births: {e}")

    async def _birth_agent(self, embryo_data: Dict[str, Any]):
        """Birth a new agent from embryo data"""
        try:
            self.logger.info(
                f"🧬 Agent birth initiated for embryo {embryo_data.get('embryo_id')}"
            )

            # Create agent blueprint
            agent_blueprint = await self.agent_creator.create_agent(embryo_data)

            if agent_blueprint:
                # Create active agent
                active_agent = ActiveAgent(
                    blueprint=agent_blueprint,
                    creation_time=datetime.now(),
                    last_activity=datetime.now(),
                )

                # Add to active agents
                self.active_agents[agent_blueprint.agent_id] = active_agent
                self.total_births += 1

                # Remove embryo from pool (it has been born)
                embryo_id = embryo_data.get("embryo_id")
                if embryo_id:
                    await self.embryo_pool.remove_embryo(embryo_id)

                # Log the birth
                self.logger.info(f"🎉 Agent birth successful: {agent_blueprint.name}")
                self.logger.info(
                    f"   - Specialization: {agent_blueprint.specialization}"
                )
                self.logger.info(f"   - Autonomy: {agent_blueprint.autonomy_level}")
                self.logger.info(f"   - Active agents: {len(self.active_agents)}")

                # Record in history
                self._record_birth(active_agent, embryo_data)

                return active_agent

        except Exception as e:
            self.logger.error(f"Agent birth failed: {e}")
            return None

    async def _monitor_agent_performance(self):
        """Monitor performance of active agents"""
        try:
            current_time = datetime.now()

            for agent_id, agent in self.active_agents.items():
                # Check for inactive agents
                time_since_activity = current_time - agent.last_activity

                if time_since_activity > timedelta(hours=24):
                    self.logger.warning(
                        f"Agent {agent.blueprint.name} has been inactive for {time_since_activity}"
                    )

                # Update agent metrics (placeholder for now)
                # In real implementation, would gather actual performance data
                agent.last_activity = current_time

        except Exception as e:
            self.logger.error(f"Error monitoring agent performance: {e}")

    async def _check_for_retirements(self):
        """Check if any agents should be retired"""
        try:
            agents_to_retire = []

            for agent_id, agent in self.active_agents.items():
                # Check retirement criteria
                if (
                    agent.success_rate < self.agent_retirement_threshold
                    and agent.task_count > 10
                ):
                    agents_to_retire.append(agent_id)

            # Retire agents
            for agent_id in agents_to_retire:
                await self._retire_agent(agent_id)

        except Exception as e:
            self.logger.error(f"Error checking for retirements: {e}")

    async def _retire_agent(self, agent_id: str):
        """Retire an underperforming agent"""
        try:
            agent = self.active_agents.get(agent_id)
            if not agent:
                return

            self.logger.info(f"👋 Retiring agent: {agent.blueprint.name}")
            self.logger.info(
                f"   - Reason: Low performance (success rate: {agent.success_rate:.1%})"
            )

            # Mark as inactive
            agent.active = False

            # Remove from active agents
            del self.active_agents[agent_id]
            self.total_retirements += 1

            # Record retirement
            self._record_retirement(agent)

        except Exception as e:
            self.logger.error(f"Error retiring agent {agent_id}: {e}")

    def _record_birth(self, agent: ActiveAgent, embryo_data: Dict[str, Any]):
        """Record agent birth in history"""
        try:
            birth_record = {
                "event": "birth",
                "timestamp": agent.creation_time.isoformat(),
                "agent_id": getattr(agent.blueprint, "agent_id", "unknown"),
                "agent_name": getattr(agent.blueprint, "name", "Unknown Agent"),
                "specialization": getattr(agent.blueprint, "specialization", "general"),
                "embryo_id": embryo_data.get("embryo_id", "unknown"),
                "embryo_patterns": embryo_data.get("patterns_detected", 0),
                "personality_traits": getattr(
                    agent.blueprint, "personality_traits", {}
                ),
            }

            self.agent_history.append(birth_record)
        except Exception as e:
            self.logger.error(f"Error recording birth: {e}")
            # Don't fail the birth process for recording issues

    def _record_retirement(self, agent: ActiveAgent):
        """Record agent retirement in history"""
        retirement_record = {
            "event": "retirement",
            "timestamp": datetime.now().isoformat(),
            "agent_id": agent.blueprint.agent_id,
            "agent_name": agent.blueprint.name,
            "specialization": agent.blueprint.specialization,
            "creation_time": agent.creation_time.isoformat(),
            "lifetime_days": (datetime.now() - agent.creation_time).days,
            "task_count": agent.task_count,
            "success_rate": agent.success_rate,
            "retirement_reason": "performance",
        }

        self.agent_history.append(retirement_record)

    async def get_active_agents(self) -> List[ActiveAgent]:
        """Get list of all active agents"""
        return list(self.active_agents.values())

    async def get_agent_by_id(self, agent_id: str) -> Optional[ActiveAgent]:
        """Get specific agent by ID"""
        return self.active_agents.get(agent_id)

    async def get_system_status(self) -> Dict[str, Any]:
        """Get comprehensive system status"""
        try:
            embryo_status = self.embryo_pool.get_pool_status()

            # Calculate system metrics
            uptime = datetime.now() - self.system_start_time
            agent_specializations = {}
            agent_autonomy_levels = {}

            for agent in self.active_agents.values():
                spec = agent.blueprint.specialization
                autonomy = agent.blueprint.autonomy_level

                agent_specializations[spec] = agent_specializations.get(spec, 0) + 1
                agent_autonomy_levels[autonomy] = (
                    agent_autonomy_levels.get(autonomy, 0) + 1
                )

            return {
                "system": {
                    "uptime": str(uptime),
                    "total_births": self.total_births,
                    "total_retirements": self.total_retirements,
                    "active_agents": len(self.active_agents),
                    "max_agents": self.max_active_agents,
                },
                "embryo_pool": embryo_status,
                "active_agents": {
                    "count": len(self.active_agents),
                    "specializations": agent_specializations,
                    "autonomy_levels": agent_autonomy_levels,
                    "agents": [
                        {
                            "id": agent.blueprint.agent_id,
                            "name": agent.blueprint.name,
                            "specialization": agent.blueprint.specialization,
                            "autonomy": agent.blueprint.autonomy_level,
                            "creation_time": agent.creation_time.isoformat(),
                            "task_count": agent.task_count,
                            "success_rate": agent.success_rate,
                        }
                        for agent in self.active_agents.values()
                    ],
                },
                "recent_history": self.agent_history[-10:],  # Last 10 events
            }

        except Exception as e:
            self.logger.error(f"Error getting system status: {e}")
            return {"error": str(e)}

    async def force_agent_birth(self) -> Optional[ActiveAgent]:
        """Force creation of a new agent from best available embryo"""
        try:
            if len(self.active_agents) >= self.max_active_agents:
                self.logger.warning("Cannot force birth: maximum agents reached")
                return None

            # Get best embryo
            embryo_status = self.embryo_pool.get_pool_status()
            embryos = embryo_status.get("embryos", [])

            if not embryos:
                self.logger.warning("No embryos available for forced birth")
                return None

            # Find best embryo
            best_embryo = max(embryos, key=lambda e: e.get("fitness_score", 0))

            # Force birth
            return await self._birth_agent(best_embryo)

        except Exception as e:
            self.logger.error(f"Error in forced agent birth: {e}")
            return None
