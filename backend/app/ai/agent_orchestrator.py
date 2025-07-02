"""
ALims Central AI Brain - Agent Orchestrator
Coordinates specialized agents for complex multi-agent tasks
"""

import asyncio
import json
import logging
from typing import Dict, Any, List, Optional
from datetime import datetime, timedelta
from pathlib import Path
from enum import Enum

logger = logging.getLogger(__name__)


class TaskStatus(Enum):
    """Task execution status"""

    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"


class TaskPriority(Enum):
    """Task priority levels"""

    LOW = "low"
    NORMAL = "normal"
    HIGH = "high"
    URGENT = "urgent"


class OrchestrationTask:
    """Represents a task being orchestrated"""

    def __init__(
        self,
        task_id: str,
        description: str,
        priority: TaskPriority = TaskPriority.NORMAL,
    ):
        self.task_id = task_id
        self.description = description
        self.priority = priority
        self.status = TaskStatus.PENDING
        self.created_at = datetime.now()
        self.started_at = None
        self.completed_at = None
        self.subtasks = []
        self.agent_assignments = {}
        self.results = {}
        self.errors = []
        self.orchestration_plan = None

    def to_dict(self) -> Dict[str, Any]:
        """Convert task to dictionary"""
        return {
            "task_id": self.task_id,
            "description": self.description,
            "priority": self.priority.value,
            "status": self.status.value,
            "created_at": self.created_at.isoformat(),
            "started_at": self.started_at.isoformat() if self.started_at else None,
            "completed_at": (
                self.completed_at.isoformat() if self.completed_at else None
            ),
            "subtasks": self.subtasks,
            "agent_assignments": self.agent_assignments,
            "results": self.results,
            "errors": self.errors,
        }


class AgentOrchestrator:
    """Coordinates specialized agents for complex tasks"""

    def __init__(self, central_brain):
        self.central_brain = central_brain
        self.prompt_template = self._load_prompt_template()

        # Task management
        self.active_tasks = {}
        self.completed_tasks = {}
        self.task_counter = 0

        # Agent registry
        self.available_agents = {}
        self.agent_capabilities = {}
        self.agent_performance = {}

        # Orchestration metrics
        self.orchestration_count = 0
        self.success_rate = 0.0
        self.average_completion_time = 0.0

        logger.info("AgentOrchestrator initialized")

    def _load_prompt_template(self) -> str:
        """Load the orchestration prompt template"""
        try:
            prompt_path = Path("app/ai/prompts/agent_orchestration.txt")
            if prompt_path.exists():
                return prompt_path.read_text()
            else:
                return self._get_fallback_prompt()
        except Exception as e:
            logger.error(f"Failed to load orchestration prompt template: {e}")
            return self._get_fallback_prompt()

    def _get_fallback_prompt(self) -> str:
        """Fallback orchestration prompt"""
        return """You are the Agent Orchestrator for ALims.

Task: {task_description}
Available agents: {available_agents}

Create a coordination plan to accomplish this task using available agents.
Respond with a structured plan in JSON format."""

    async def coordinate_task(
        self, task_description: str, context: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """Coordinate multiple agents for a complex task"""

        try:
            # Create orchestration task
            task_id = f"task_{self.task_counter:04d}"
            self.task_counter += 1

            priority = self._determine_priority(task_description, context)
            task = OrchestrationTask(task_id, task_description, priority)
            self.active_tasks[task_id] = task

            logger.info(f"🎭 Starting orchestration for task: {task_id}")

            # Analyze task and create orchestration plan
            orchestration_plan = await self._create_orchestration_plan(task, context)
            task.orchestration_plan = orchestration_plan

            if not orchestration_plan.get("success", False):
                task.status = TaskStatus.FAILED
                task.errors.append("Failed to create orchestration plan")
                return {
                    "success": False,
                    "error": "Could not create orchestration plan",
                    "task_id": task_id,
                }

            # Execute the orchestration plan
            task.status = TaskStatus.IN_PROGRESS
            task.started_at = datetime.now()

            execution_result = await self._execute_orchestration_plan(
                task, orchestration_plan
            )

            # Update task status
            if execution_result.get("success", False):
                task.status = TaskStatus.COMPLETED
                task.completed_at = datetime.now()
                task.results = execution_result.get("results", {})
            else:
                task.status = TaskStatus.FAILED
                task.errors.extend(execution_result.get("errors", []))

            # Move to completed tasks
            self.completed_tasks[task_id] = self.active_tasks.pop(task_id)

            # Update metrics
            self._update_orchestration_metrics(task)

            logger.info(f"✅ Orchestration completed for task: {task_id}")

            return {
                "success": execution_result.get("success", False),
                "task_id": task_id,
                "orchestration_plan": orchestration_plan,
                "results": execution_result.get("results", {}),
                "execution_time": (
                    (task.completed_at - task.started_at).total_seconds()
                    if task.completed_at
                    else None
                ),
                "agents_used": list(task.agent_assignments.keys()),
            }

        except Exception as e:
            logger.error(f"❌ Orchestration failed: {e}")
            return {"success": False, "error": str(e)}

    async def _create_orchestration_plan(
        self, task: OrchestrationTask, context: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """Create detailed orchestration plan using AI"""

        try:
            # Gather available agents and their capabilities
            available_agents = await self._get_available_agents()

            # Build orchestration context
            orchestration_context = {
                "task_description": task.description,
                "available_agents": available_agents,
                "user_context": context or {},
                "system_capabilities": await self._get_system_capabilities(),
                "priority_level": task.priority.value,
                "resource_constraints": await self._get_resource_constraints(),
            }

            # Format prompt with context
            formatted_prompt = self._format_orchestration_prompt(orchestration_context)

            # Generate orchestration plan using AI
            plan_response = await self.central_brain.ollama_client.generate_response(
                prompt="Create a detailed orchestration plan for this complex task",
                system_prompt=formatted_prompt,
            )

            # Parse the orchestration plan
            orchestration_plan = self._parse_orchestration_plan(plan_response)

            # Validate the plan
            validation_result = self._validate_orchestration_plan(
                orchestration_plan, available_agents
            )

            if validation_result["valid"]:
                return {"success": True, "plan": orchestration_plan}
            else:
                return {"success": False, "error": validation_result["error"]}

        except Exception as e:
            logger.error(f"Failed to create orchestration plan: {e}")
            return {"success": False, "error": str(e)}

    async def _execute_orchestration_plan(
        self, task: OrchestrationTask, plan: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Execute the orchestration plan"""

        try:
            orchestration_plan = plan.get("plan", {})
            subtasks = orchestration_plan.get("subtasks", [])

            if not subtasks:
                return {
                    "success": False,
                    "errors": ["No subtasks in orchestration plan"],
                }

            # Execute subtasks according to the plan
            execution_results = {}
            errors = []

            for subtask in subtasks:
                subtask_id = subtask.get("id", "unknown")
                agent_id = subtask.get("assigned_agent", "unknown")

                logger.info(f"Executing subtask {subtask_id} with agent {agent_id}")

                try:
                    # Delegate to specific agent
                    result = await self.delegate_to_agent(agent_id, subtask)
                    execution_results[subtask_id] = result

                    if not result.get("success", False):
                        errors.append(
                            f"Subtask {subtask_id} failed: {result.get('error', 'Unknown error')}"
                        )

                except Exception as e:
                    error_msg = f"Subtask {subtask_id} execution failed: {str(e)}"
                    errors.append(error_msg)
                    logger.error(error_msg)

            # Synthesize results
            if execution_results and len(errors) < len(subtasks):
                synthesized_result = await self.synthesize_results(
                    list(execution_results.values())
                )
                return {
                    "success": True,
                    "results": {
                        "individual_results": execution_results,
                        "synthesized_result": synthesized_result,
                        "subtasks_completed": len(execution_results),
                        "subtasks_failed": len(errors),
                    },
                    "errors": errors,
                }
            else:
                return {"success": False, "errors": errors}

        except Exception as e:
            logger.error(f"Failed to execute orchestration plan: {e}")
            return {"success": False, "errors": [str(e)]}

    async def delegate_to_agent(
        self, agent_id: str, subtask: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Delegate specific subtask to specialized agent"""

        try:
            logger.info(f"🤖 Delegating to agent: {agent_id}")

            # Check if agent is available
            if agent_id not in self.available_agents:
                return {"success": False, "error": f"Agent {agent_id} not available"}

            # For now, simulate agent delegation
            # In a full implementation, this would call actual specialized agents

            if agent_id == "user_interface":
                # Delegate to UserInterfaceAgent
                if self.central_brain.user_interface:
                    return await self._delegate_to_user_interface(subtask)

            elif agent_id == "system_controller":
                # Delegate to SystemController (when implemented)
                return await self._delegate_to_system_controller(subtask)

            elif agent_id == "pattern_validator":
                # Delegate to PatternValidator (when implemented)
                return await self._delegate_to_pattern_validator(subtask)

            elif agent_id == "embryo_trainer":
                # Delegate to EmbryoTrainer (when implemented)
                return await self._delegate_to_embryo_trainer(subtask)

            else:
                # Generic agent delegation
                return await self._delegate_to_generic_agent(agent_id, subtask)

        except Exception as e:
            logger.error(f"Failed to delegate to agent {agent_id}: {e}")
            return {"success": False, "error": str(e)}

    async def synthesize_results(
        self, agent_results: List[Dict[str, Any]]
    ) -> Dict[str, Any]:
        """Combine results from multiple agents into coherent response"""

        try:
            # Filter successful results
            successful_results = [r for r in agent_results if r.get("success", False)]

            if not successful_results:
                return {
                    "success": False,
                    "message": "No successful agent results to synthesize",
                }

            # Use AI to synthesize results intelligently
            synthesis_prompt = f"""
            Synthesize these agent results into a coherent, comprehensive response:
            
            Agent Results: {successful_results}
            
            Guidelines:
            - Combine insights from all agents
            - Resolve any conflicts or contradictions
            - Present a unified, actionable response
            - Highlight key findings and recommendations
            - Maintain clarity and coherence
            """

            synthesized_response = await self.central_brain.ollama_client.generate_response(
                prompt="Synthesize these multi-agent results into a unified response",
                system_prompt=synthesis_prompt,
            )

            return {
                "success": True,
                "synthesized_response": synthesized_response,
                "agent_count": len(successful_results),
                "synthesis_timestamp": datetime.now().isoformat(),
            }

        except Exception as e:
            logger.error(f"Failed to synthesize results: {e}")
            return {"success": False, "error": str(e)}

    async def monitor_task_progress(self, task_id: str) -> Dict[str, Any]:
        """Monitor ongoing task execution across agents"""

        if task_id in self.active_tasks:
            task = self.active_tasks[task_id]
            return {
                "task_id": task_id,
                "status": task.status.value,
                "progress": self._calculate_task_progress(task),
                "agents_involved": list(task.agent_assignments.keys()),
                "elapsed_time": (datetime.now() - task.created_at).total_seconds(),
                "estimated_completion": self._estimate_completion_time(task),
            }
        elif task_id in self.completed_tasks:
            task = self.completed_tasks[task_id]
            return task.to_dict()
        else:
            return {"error": f"Task {task_id} not found"}

    # Helper methods for agent delegation
    async def _delegate_to_user_interface(
        self, subtask: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Delegate subtask to UserInterfaceAgent"""
        try:
            message = subtask.get("description", "Process this subtask")
            result = await self.central_brain.user_interface.process_chat_message(
                message
            )
            return {"success": True, "agent": "user_interface", "result": result}
        except Exception as e:
            return {"success": False, "error": str(e)}

    async def _delegate_to_system_controller(
        self, subtask: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Delegate subtask to SystemController (placeholder)"""
        return {
            "success": True,
            "agent": "system_controller",
            "result": f"SystemController would handle: {subtask.get('description', 'Unknown task')}",
        }

    async def _delegate_to_pattern_validator(
        self, subtask: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Delegate subtask to PatternValidator (placeholder)"""
        return {
            "success": True,
            "agent": "pattern_validator",
            "result": f"PatternValidator would handle: {subtask.get('description', 'Unknown task')}",
        }

    async def _delegate_to_embryo_trainer(
        self, subtask: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Delegate subtask to EmbryoTrainer (placeholder)"""
        return {
            "success": True,
            "agent": "embryo_trainer",
            "result": f"EmbryoTrainer would handle: {subtask.get('description', 'Unknown task')}",
        }

    async def _delegate_to_generic_agent(
        self, agent_id: str, subtask: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Delegate to a generic agent (placeholder)"""
        return {
            "success": True,
            "agent": agent_id,
            "result": f"Agent {agent_id} would handle: {subtask.get('description', 'Unknown task')}",
        }

    # Helper methods for orchestration
    async def _get_available_agents(self) -> Dict[str, Any]:
        """Get list of available agents and their capabilities"""
        agents = {
            "user_interface": {
                "name": "User Interface Agent",
                "capabilities": [
                    "natural_language_processing",
                    "user_interaction",
                    "preference_learning",
                ],
                "status": (
                    "available" if self.central_brain.user_interface else "unavailable"
                ),
            },
            "system_controller": {
                "name": "System Controller",
                "capabilities": [
                    "system_commands",
                    "action_execution",
                    "safety_validation",
                ],
                "status": "planned",
            },
            "pattern_validator": {
                "name": "Pattern Validator",
                "capabilities": [
                    "pattern_analysis",
                    "coherence_checking",
                    "validation",
                ],
                "status": "planned",
            },
            "embryo_trainer": {
                "name": "Embryo Trainer",
                "capabilities": [
                    "training_assessment",
                    "specialization_recommendation",
                    "birth_readiness",
                ],
                "status": "planned",
            },
        }

        self.available_agents = agents
        return agents

    async def _get_system_capabilities(self) -> Dict[str, Any]:
        """Get current system capabilities"""
        return {
            "ai_brain_active": self.central_brain.is_running,
            "context_management": self.central_brain.context_manager is not None,
            "ollama_model": "gemma3:4b",
            "specialized_agents": len(
                [
                    a
                    for a in self.available_agents.values()
                    if a.get("status") == "available"
                ]
            ),
        }

    async def _get_resource_constraints(self) -> Dict[str, Any]:
        """Get current resource constraints"""
        return {
            "max_concurrent_agents": 5,
            "memory_limit": "8GB",
            "processing_timeout": 300,  # 5 minutes
            "priority_queue_size": 10,
        }

    def _determine_priority(
        self, task_description: str, context: Optional[Dict[str, Any]] = None
    ) -> TaskPriority:
        """Determine task priority based on description and context"""
        description_lower = task_description.lower()

        if any(
            word in description_lower
            for word in ["urgent", "emergency", "critical", "immediate"]
        ):
            return TaskPriority.URGENT
        elif any(
            word in description_lower
            for word in ["important", "high", "priority", "asap"]
        ):
            return TaskPriority.HIGH
        elif any(
            word in description_lower for word in ["low", "background", "when possible"]
        ):
            return TaskPriority.LOW
        else:
            return TaskPriority.NORMAL

    def _format_orchestration_prompt(self, context: Dict[str, Any]) -> str:
        """Format the orchestration prompt with context"""
        try:
            return self.prompt_template.format(**context)
        except Exception as e:
            logger.error(f"Error formatting orchestration prompt: {e}")
            return f"Task: {context.get('task_description', 'Unknown task')}\nCreate an orchestration plan."

    def _parse_orchestration_plan(self, response: str) -> Dict[str, Any]:
        """Parse orchestration plan from AI response"""
        try:
            # Try to extract JSON from response
            start_idx = response.find("{")
            end_idx = response.rfind("}") + 1

            if start_idx != -1 and end_idx > start_idx:
                json_str = response[start_idx:end_idx]
                return json.loads(json_str)
            else:
                # Fallback: create basic plan from text
                return self._create_fallback_plan(response)

        except json.JSONDecodeError:
            logger.warning("Failed to parse JSON orchestration plan, using fallback")
            return self._create_fallback_plan(response)

    def _create_fallback_plan(self, response: str) -> Dict[str, Any]:
        """Create fallback orchestration plan"""
        return {
            "subtasks": [
                {
                    "id": "subtask_001",
                    "description": "Process the main task",
                    "assigned_agent": "user_interface",
                    "priority": "normal",
                    "dependencies": [],
                }
            ],
            "execution_sequence": ["subtask_001"],
            "success_criteria": ["Task completed successfully"],
            "fallback_options": ["Retry with different agent"],
            "estimated_duration": 60,
        }

    def _validate_orchestration_plan(
        self, plan: Dict[str, Any], available_agents: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Validate orchestration plan"""
        try:
            subtasks = plan.get("subtasks", [])

            if not subtasks:
                return {"valid": False, "error": "No subtasks in plan"}

            # Check agent availability
            for subtask in subtasks:
                agent_id = subtask.get("assigned_agent")
                if agent_id and agent_id not in available_agents:
                    return {"valid": False, "error": f"Agent {agent_id} not available"}

            return {"valid": True}

        except Exception as e:
            return {"valid": False, "error": str(e)}

    def _calculate_task_progress(self, task: OrchestrationTask) -> float:
        """Calculate task progress percentage"""
        if task.status == TaskStatus.COMPLETED:
            return 100.0
        elif task.status == TaskStatus.FAILED:
            return 0.0
        elif task.status == TaskStatus.IN_PROGRESS:
            # Estimate based on subtasks completed
            total_subtasks = len(task.subtasks)
            if total_subtasks == 0:
                return 50.0  # Assume halfway if no subtasks
            completed_subtasks = len(
                [r for r in task.results.values() if r.get("success", False)]
            )
            return (completed_subtasks / total_subtasks) * 100.0
        else:
            return 0.0

    def _estimate_completion_time(self, task: OrchestrationTask) -> Optional[str]:
        """Estimate task completion time"""
        if task.status in [TaskStatus.COMPLETED, TaskStatus.FAILED]:
            return None

        # Simple estimation based on average completion time
        if self.average_completion_time > 0:
            estimated_seconds = self.average_completion_time
            estimated_completion = datetime.now() + timedelta(seconds=estimated_seconds)
            return estimated_completion.isoformat()

        return None

    def _update_orchestration_metrics(self, task: OrchestrationTask):
        """Update orchestration performance metrics"""
        self.orchestration_count += 1

        # Update success rate
        successful_tasks = len(
            [
                t
                for t in self.completed_tasks.values()
                if t.status == TaskStatus.COMPLETED
            ]
        )
        self.success_rate = (
            successful_tasks / len(self.completed_tasks)
            if self.completed_tasks
            else 0.0
        )

        # Update average completion time
        if (
            task.status == TaskStatus.COMPLETED
            and task.started_at
            and task.completed_at
        ):
            completion_time = (task.completed_at - task.started_at).total_seconds()
            if self.average_completion_time == 0:
                self.average_completion_time = completion_time
            else:
                # Moving average
                self.average_completion_time = (
                    self.average_completion_time + completion_time
                ) / 2

    def get_orchestrator_status(self) -> Dict[str, Any]:
        """Get current status of the Agent Orchestrator"""
        return {
            "agent_name": "AgentOrchestrator",
            "orchestration_count": self.orchestration_count,
            "active_tasks": len(self.active_tasks),
            "completed_tasks": len(self.completed_tasks),
            "success_rate": self.success_rate,
            "average_completion_time": self.average_completion_time,
            "available_agents": len(self.available_agents),
            "capabilities": [
                "multi_agent_coordination",
                "task_decomposition",
                "agent_delegation",
                "result_synthesis",
                "progress_monitoring",
            ],
        }
