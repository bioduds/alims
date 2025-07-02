"""
System Controller for ALims Central AI Brain

This module provides intelligent command translation and system action execution,
serving as the bridge between user intentions and system capabilities.
"""

import asyncio
import json
import logging
import time
from datetime import datetime
from enum import Enum
from typing import Dict, List, Optional, Any, Union
from dataclasses import dataclass, asdict
import re

logger = logging.getLogger(__name__)


class CommandType(Enum):
    """Types of user commands"""

    QUERY = "query"
    ACTION = "action"
    CONFIGURATION = "configuration"
    AGENT_MANAGEMENT = "agent_management"
    DATA_OPERATION = "data_operation"
    PROCESS_CONTROL = "process_control"
    SYSTEM_MAINTENANCE = "system_maintenance"
    HELP_REQUEST = "help_request"


class ComplexityLevel(Enum):
    """Command complexity levels"""

    SIMPLE = "simple"
    MODERATE = "moderate"
    COMPLEX = "complex"
    CRITICAL = "critical"


class RiskLevel(Enum):
    """Risk levels for system actions"""

    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    CRITICAL = "critical"


class ActionType(Enum):
    """Recommended action types"""

    EXECUTE = "execute"
    REQUEST_CONFIRMATION = "request_confirmation"
    REQUEST_CLARIFICATION = "request_clarification"
    DENY = "deny"
    DELEGATE = "delegate"


class ValidationStatus(Enum):
    """Safety validation status"""

    SAFE = "safe"
    REQUIRES_CONFIRMATION = "requires_confirmation"
    REQUIRES_CLARIFICATION = "requires_clarification"
    UNSAFE = "unsafe"


@dataclass
class IntentAnalysis:
    """Analysis of user intent"""

    primary_goal: str
    command_type: CommandType
    complexity_level: ComplexityLevel
    parameters: Dict[str, Any]
    confidence_score: float


@dataclass
class CapabilityAssessment:
    """Assessment of system capabilities"""

    required_capabilities: List[str]
    available_resources: Dict[str, Any]
    feasibility_score: int  # 1-10 scale
    required_agents: List[str]
    resource_requirements: Dict[str, Any]


@dataclass
class SafetyValidation:
    """Safety validation results"""

    risk_level: RiskLevel
    safety_concerns: List[str]
    permission_requirements: List[str]
    validation_status: ValidationStatus
    warnings: List[str]


@dataclass
class ActionPlan:
    """Detailed action execution plan"""

    execution_steps: List[Dict[str, Any]]
    estimated_duration: float
    success_criteria: List[str]
    rollback_plan: List[Dict[str, Any]]
    dependencies: List[str]


@dataclass
class SystemAction:
    """Complete system action specification"""

    action_id: str
    intent_analysis: IntentAnalysis
    capability_assessment: CapabilityAssessment
    safety_validation: SafetyValidation
    action_plan: ActionPlan
    recommended_action: ActionType
    justification: str
    user_feedback: str
    next_steps: List[str]
    created_at: datetime
    executed_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    status: str = "pending"
    results: Optional[Dict[str, Any]] = None


class SystemController:
    """
    Intelligent system controller for command translation and execution.

    The SystemController serves as the bridge between user intentions and system
    capabilities, providing safe and intelligent command interpretation and execution.
    """

    def __init__(self, central_brain):
        """Initialize the System Controller"""
        self.central_brain = central_brain
        self.action_history: List[SystemAction] = []
        self.active_actions: Dict[str, SystemAction] = {}
        self.security_level = "standard"  # standard, elevated, restricted
        self.action_counter = 0

        # Command pattern recognition
        self.command_patterns = {
            CommandType.QUERY: [
                r"what\s+is",
                r"how\s+many",
                r"show\s+me",
                r"list",
                r"status",
                r"tell\s+me",
                r"explain",
                r"describe",
                r"find",
                r"search",
            ],
            CommandType.ACTION: [
                r"create",
                r"start",
                r"stop",
                r"run",
                r"execute",
                r"launch",
                r"kill",
                r"restart",
                r"pause",
                r"resume",
                r"update",
            ],
            CommandType.CONFIGURATION: [
                r"set",
                r"configure",
                r"change",
                r"modify",
                r"adjust",
                r"enable",
                r"disable",
                r"toggle",
                r"switch",
            ],
            CommandType.AGENT_MANAGEMENT: [
                r"agent",
                r"birth",
                r"embryo",
                r"train",
                r"specialize",
                r"remove\s+agent",
                r"delete\s+agent",
            ],
            CommandType.HELP_REQUEST: [
                r"help",
                r"how\s+do\s+i",
                r"tutorial",
                r"guide",
                r"explain\s+how",
            ],
        }

        # Risk assessment patterns
        self.high_risk_patterns = [
            r"delete\s+all",
            r"remove\s+all",
            r"format",
            r"wipe",
            r"destroy",
            r"kill\s+all",
            r"shutdown\s+system",
            r"reset\s+system",
        ]

        self.medium_risk_patterns = [
            r"delete",
            r"remove",
            r"kill",
            r"stop",
            r"disable",
            r"modify\s+system",
            r"change\s+config",
        ]

        logger.info("SystemController initialized")

    async def translate_user_command(
        self, user_command: str, user_context: Dict[str, Any] = None
    ) -> SystemAction:
        """
        Translate natural language command into structured system action.

        Args:
            user_command: Natural language command from user
            user_context: Additional context about user and system state

        Returns:
            SystemAction: Complete action specification with analysis
        """
        try:
            logger.info(f"Translating user command: {user_command}")

            # Generate unique action ID
            self.action_counter += 1
            action_id = f"action_{self.action_counter:04d}"

            # Build context for AI analysis
            context = await self._build_analysis_context(
                user_command, user_context or {}
            )

            # Get AI analysis
            ai_response = await self._get_ai_analysis(context)

            # Parse AI response into structured components
            system_action = await self._parse_ai_response(
                action_id, user_command, ai_response
            )

            # Store action for tracking
            self.active_actions[action_id] = system_action
            self.action_history.append(system_action)

            logger.info(f"Command translated successfully: {action_id}")
            return system_action

        except Exception as e:
            logger.error(f"Error translating command: {e}")
            # Return safe fallback action
            return await self._create_fallback_action(user_command, str(e))

    async def execute_system_action(self, action: SystemAction) -> Dict[str, Any]:
        """
        Execute a validated system action safely.

        Args:
            action: SystemAction to execute

        Returns:
            Dict containing execution results
        """
        try:
            logger.info(f"Executing system action: {action.action_id}")

            # Update action status
            action.executed_at = datetime.now()
            action.status = "executing"

            # Validate action is safe to execute
            if not await self._validate_execution_safety(action):
                action.status = "failed"
                return {
                    "success": False,
                    "error": "Action failed safety validation",
                    "action_id": action.action_id,
                }

            # Execute based on recommended action type
            if action.recommended_action == ActionType.EXECUTE:
                results = await self._execute_action_steps(action)
            elif action.recommended_action == ActionType.DELEGATE:
                results = await self._delegate_to_agents(action)
            else:
                results = {
                    "success": False,
                    "error": f"Action type {action.recommended_action.value} not executable",
                    "requires_user_input": True,
                }

            # Update action with results
            action.results = results
            action.completed_at = datetime.now()
            action.status = "completed" if results.get("success") else "failed"

            logger.info(f"Action execution completed: {action.action_id}")
            return results

        except Exception as e:
            logger.error(f"Error executing action {action.action_id}: {e}")
            action.status = "failed"
            action.results = {"success": False, "error": str(e)}
            return action.results

    async def validate_action_safety(self, action: SystemAction) -> bool:
        """
        Validate that an action is safe to execute.

        Args:
            action: SystemAction to validate

        Returns:
            bool: True if action is safe to execute
        """
        try:
            # Check validation status
            if action.safety_validation.validation_status == ValidationStatus.UNSAFE:
                return False

            # Check risk level
            if action.safety_validation.risk_level == RiskLevel.CRITICAL:
                return False

            # Check for high-risk patterns in original command
            command_lower = action.intent_analysis.primary_goal.lower()
            for pattern in self.high_risk_patterns:
                if re.search(pattern, command_lower):
                    logger.warning(f"High-risk pattern detected: {pattern}")
                    return False

            # Validate required permissions
            if not await self._check_user_permissions(
                action.safety_validation.permission_requirements
            ):
                return False

            # Check system resources
            if not await self._check_system_resources(
                action.capability_assessment.resource_requirements
            ):
                return False

            return True

        except Exception as e:
            logger.error(f"Error validating action safety: {e}")
            return False

    async def get_action_status(self, action_id: str) -> Optional[Dict[str, Any]]:
        """Get status of a specific action"""
        action = self.active_actions.get(action_id)
        if not action:
            return None

        return {
            "action_id": action_id,
            "status": action.status,
            "created_at": action.created_at.isoformat(),
            "executed_at": (
                action.executed_at.isoformat() if action.executed_at else None
            ),
            "completed_at": (
                action.completed_at.isoformat() if action.completed_at else None
            ),
            "results": action.results,
        }

    async def get_system_capabilities(self) -> Dict[str, Any]:
        """Get current system capabilities"""
        return {
            "agent_management": {
                "can_create_agents": True,
                "can_modify_agents": True,
                "can_remove_agents": True,
                "max_agents": 50,
            },
            "system_control": {
                "can_start_processes": True,
                "can_stop_processes": True,
                "can_modify_config": True,
                "security_level": self.security_level,
            },
            "data_operations": {
                "can_query_data": True,
                "can_modify_data": True,
                "can_export_data": True,
            },
            "integration": {
                "available_apis": ["ollama", "system", "file_system"],
                "external_services": [],
            },
        }

    async def _build_analysis_context(
        self, user_command: str, user_context: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Build context for AI analysis"""
        system_state = await self._get_system_state()
        capabilities = await self.get_system_capabilities()

        return {
            "user_command": user_command,
            "user_context": user_context,
            "system_state": system_state,
            "available_capabilities": capabilities,
            "security_level": self.security_level,
            "previous_actions": [
                {
                    "command": action.intent_analysis.primary_goal,
                    "type": action.intent_analysis.command_type.value,
                    "status": action.status,
                }
                for action in self.action_history[-5:]  # Last 5 actions
            ],
        }

    async def _get_ai_analysis(self, context: Dict[str, Any]) -> str:
        """Get AI analysis of the command"""
        try:
            # Load system control prompt
            prompt_path = "app/ai/prompts/system_control.txt"
            with open(prompt_path, "r") as f:
                prompt_template = f.read()

            # Format prompt with context
            formatted_prompt = prompt_template.format(**context)

            # Get AI response
            response = await self.central_brain.ollama_client.generate_response(
                formatted_prompt,
                context={"type": "system_control", "command": context["user_command"]},
            )

            return response

        except Exception as e:
            logger.error(f"Error getting AI analysis: {e}")
            return self._create_fallback_analysis(context["user_command"])

    async def _parse_ai_response(
        self, action_id: str, user_command: str, ai_response: str
    ) -> SystemAction:
        """Parse AI response into structured SystemAction"""
        try:
            # Extract structured sections from AI response
            sections = self._extract_response_sections(ai_response)

            # Parse intent analysis
            intent_analysis = self._parse_intent_analysis(
                sections.get("INTENT ANALYSIS", "")
            )

            # Parse capability assessment
            capability_assessment = self._parse_capability_assessment(
                sections.get("CAPABILITY ASSESSMENT", "")
            )

            # Parse safety validation
            safety_validation = self._parse_safety_validation(
                sections.get("SAFETY VALIDATION", "")
            )

            # Parse action plan
            action_plan = self._parse_action_plan(sections.get("ACTION PLAN", ""))

            # Parse recommended action
            recommended_section = sections.get("RECOMMENDED ACTION", "")
            recommended_action, justification, user_feedback, next_steps = (
                self._parse_recommended_action(recommended_section)
            )

            return SystemAction(
                action_id=action_id,
                intent_analysis=intent_analysis,
                capability_assessment=capability_assessment,
                safety_validation=safety_validation,
                action_plan=action_plan,
                recommended_action=recommended_action,
                justification=justification,
                user_feedback=user_feedback,
                next_steps=next_steps,
                created_at=datetime.now(),
            )

        except Exception as e:
            logger.error(f"Error parsing AI response: {e}")
            return await self._create_fallback_action(user_command, f"Parse error: {e}")

    def _extract_response_sections(self, response: str) -> Dict[str, str]:
        """Extract structured sections from AI response"""
        sections = {}
        current_section = None
        current_content = []

        for line in response.split("\n"):
            line = line.strip()
            if line.startswith("**") and line.endswith(":**"):
                # Save previous section
                if current_section:
                    sections[current_section] = "\n".join(current_content).strip()

                # Start new section
                current_section = line[2:-3]  # Remove ** and :**
                current_content = []
            elif current_section:
                current_content.append(line)

        # Save last section
        if current_section:
            sections[current_section] = "\n".join(current_content).strip()

        return sections

    def _parse_intent_analysis(self, content: str) -> IntentAnalysis:
        """Parse intent analysis section"""
        try:
            lines = content.split("\n")
            primary_goal = ""
            command_type = CommandType.QUERY
            complexity_level = ComplexityLevel.SIMPLE
            parameters = {}

            for line in lines:
                if "Primary goal:" in line:
                    primary_goal = line.split(":", 1)[1].strip()
                elif "Command type:" in line:
                    type_str = line.split(":", 1)[1].strip().lower()
                    command_type = (
                        CommandType(type_str)
                        if type_str in [t.value for t in CommandType]
                        else CommandType.QUERY
                    )
                elif "Complexity level:" in line:
                    complexity_str = line.split(":", 1)[1].strip().lower()
                    complexity_level = (
                        ComplexityLevel(complexity_str)
                        if complexity_str in [c.value for c in ComplexityLevel]
                        else ComplexityLevel.SIMPLE
                    )
                elif "Parameters extracted:" in line:
                    params_str = line.split(":", 1)[1].strip()
                    # Simple parameter extraction
                    if params_str and params_str != "None":
                        parameters = {"raw_params": params_str}

            return IntentAnalysis(
                primary_goal=primary_goal or "Unknown goal",
                command_type=command_type,
                complexity_level=complexity_level,
                parameters=parameters,
                confidence_score=0.8,
            )

        except Exception as e:
            logger.error(f"Error parsing intent analysis: {e}")
            return IntentAnalysis(
                primary_goal="Parse error",
                command_type=CommandType.QUERY,
                complexity_level=ComplexityLevel.SIMPLE,
                parameters={},
                confidence_score=0.1,
            )

    def _parse_capability_assessment(self, content: str) -> CapabilityAssessment:
        """Parse capability assessment section"""
        try:
            lines = content.split("\n")
            required_capabilities = []
            available_resources = {}
            feasibility_score = 5
            required_agents = []

            for line in lines:
                if "Required capabilities:" in line:
                    caps_str = line.split(":", 1)[1].strip()
                    required_capabilities = [
                        cap.strip() for cap in caps_str.split(",") if cap.strip()
                    ]
                elif "Feasibility score:" in line:
                    score_str = line.split(":", 1)[1].strip()
                    try:
                        feasibility_score = int(re.search(r"\d+", score_str).group())
                    except:
                        feasibility_score = 5
                elif "Required agents:" in line:
                    agents_str = line.split(":", 1)[1].strip()
                    required_agents = [
                        agent.strip()
                        for agent in agents_str.split(",")
                        if agent.strip()
                    ]

            return CapabilityAssessment(
                required_capabilities=required_capabilities,
                available_resources=available_resources,
                feasibility_score=max(1, min(10, feasibility_score)),
                required_agents=required_agents,
                resource_requirements={},
            )

        except Exception as e:
            logger.error(f"Error parsing capability assessment: {e}")
            return CapabilityAssessment(
                required_capabilities=[],
                available_resources={},
                feasibility_score=5,
                required_agents=[],
                resource_requirements={},
            )

    def _parse_safety_validation(self, content: str) -> SafetyValidation:
        """Parse safety validation section"""
        try:
            lines = content.split("\n")
            risk_level = RiskLevel.LOW
            safety_concerns = []
            permission_requirements = []
            validation_status = ValidationStatus.SAFE
            warnings = []

            for line in lines:
                if "Risk level:" in line:
                    risk_str = line.split(":", 1)[1].strip().lower()
                    risk_level = (
                        RiskLevel(risk_str)
                        if risk_str in [r.value for r in RiskLevel]
                        else RiskLevel.LOW
                    )
                elif "Safety concerns:" in line:
                    concerns_str = line.split(":", 1)[1].strip()
                    if concerns_str and concerns_str != "None":
                        safety_concerns = [
                            concern.strip() for concern in concerns_str.split(",")
                        ]
                elif "Validation status:" in line:
                    status_str = line.split(":", 1)[1].strip().lower()
                    validation_status = (
                        ValidationStatus(status_str)
                        if status_str in [v.value for v in ValidationStatus]
                        else ValidationStatus.SAFE
                    )

            return SafetyValidation(
                risk_level=risk_level,
                safety_concerns=safety_concerns,
                permission_requirements=permission_requirements,
                validation_status=validation_status,
                warnings=warnings,
            )

        except Exception as e:
            logger.error(f"Error parsing safety validation: {e}")
            return SafetyValidation(
                risk_level=RiskLevel.MEDIUM,
                safety_concerns=["Parse error - defaulting to safe"],
                permission_requirements=[],
                validation_status=ValidationStatus.REQUIRES_CONFIRMATION,
                warnings=[],
            )

    def _parse_action_plan(self, content: str) -> ActionPlan:
        """Parse action plan section"""
        try:
            lines = content.split("\n")
            execution_steps = []
            estimated_duration = 5.0
            success_criteria = []
            rollback_plan = []

            for line in lines:
                if "Execution steps:" in line:
                    steps_str = line.split(":", 1)[1].strip()
                    if steps_str:
                        execution_steps = [
                            {"step": step.strip()} for step in steps_str.split(",")
                        ]
                elif "Estimated duration:" in line:
                    duration_str = line.split(":", 1)[1].strip()
                    try:
                        estimated_duration = float(
                            re.search(r"[\d.]+", duration_str).group()
                        )
                    except:
                        estimated_duration = 5.0
                elif "Success criteria:" in line:
                    criteria_str = line.split(":", 1)[1].strip()
                    if criteria_str:
                        success_criteria = [
                            criterion.strip() for criterion in criteria_str.split(",")
                        ]

            return ActionPlan(
                execution_steps=execution_steps,
                estimated_duration=estimated_duration,
                success_criteria=success_criteria,
                rollback_plan=rollback_plan,
                dependencies=[],
            )

        except Exception as e:
            logger.error(f"Error parsing action plan: {e}")
            return ActionPlan(
                execution_steps=[],
                estimated_duration=5.0,
                success_criteria=[],
                rollback_plan=[],
                dependencies=[],
            )

    def _parse_recommended_action(self, content: str) -> tuple:
        """Parse recommended action section"""
        try:
            lines = content.split("\n")
            action_type = ActionType.REQUEST_CLARIFICATION
            justification = ""
            user_feedback = ""
            next_steps = []

            for line in lines:
                if "Action type:" in line:
                    type_str = line.split(":", 1)[1].strip().lower()
                    action_type = (
                        ActionType(type_str)
                        if type_str in [a.value for a in ActionType]
                        else ActionType.REQUEST_CLARIFICATION
                    )
                elif "Justification:" in line:
                    justification = line.split(":", 1)[1].strip()
                elif "User feedback:" in line:
                    user_feedback = line.split(":", 1)[1].strip()
                elif "Next steps:" in line:
                    steps_str = line.split(":", 1)[1].strip()
                    if steps_str:
                        next_steps = [step.strip() for step in steps_str.split(",")]

            return action_type, justification, user_feedback, next_steps

        except Exception as e:
            logger.error(f"Error parsing recommended action: {e}")
            return (
                ActionType.REQUEST_CLARIFICATION,
                "Parse error",
                "I need clarification",
                [],
            )

    def _create_fallback_analysis(self, user_command: str) -> str:
        """Create fallback analysis when AI fails"""
        return f"""
**INTENT ANALYSIS:**
- Primary goal: {user_command}
- Command type: query
- Complexity level: simple
- Parameters extracted: None

**CAPABILITY ASSESSMENT:**
- Required capabilities: basic_query
- Available resources: limited
- Feasibility score: 5
- Required agents: user_interface

**SAFETY VALIDATION:**
- Risk level: low
- Safety concerns: None
- Permission requirements: None
- Validation status: safe

**ACTION PLAN:**
- Execution steps: Process as basic query
- Estimated duration: 2 seconds
- Success criteria: Provide response
- Rollback plan: None needed

**RECOMMENDED ACTION:**
- Action type: execute
- Justification: Simple query with low risk
- User feedback: I'll help you with that request
- Next steps: Process query
"""

    async def _create_fallback_action(
        self, user_command: str, error: str
    ) -> SystemAction:
        """Create fallback action for error cases"""
        self.action_counter += 1
        action_id = f"fallback_{self.action_counter:04d}"

        return SystemAction(
            action_id=action_id,
            intent_analysis=IntentAnalysis(
                primary_goal=user_command,
                command_type=CommandType.QUERY,
                complexity_level=ComplexityLevel.SIMPLE,
                parameters={"error": error},
                confidence_score=0.1,
            ),
            capability_assessment=CapabilityAssessment(
                required_capabilities=["basic_response"],
                available_resources={},
                feasibility_score=3,
                required_agents=["user_interface"],
                resource_requirements={},
            ),
            safety_validation=SafetyValidation(
                risk_level=RiskLevel.LOW,
                safety_concerns=[],
                permission_requirements=[],
                validation_status=ValidationStatus.SAFE,
                warnings=["Fallback action due to error"],
            ),
            action_plan=ActionPlan(
                execution_steps=[{"step": "Provide error response"}],
                estimated_duration=1.0,
                success_criteria=["User informed of issue"],
                rollback_plan=[],
                dependencies=[],
            ),
            recommended_action=ActionType.EXECUTE,
            justification="Fallback response for error condition",
            user_feedback=f"I encountered an issue processing your request: {error}",
            next_steps=["Provide fallback response"],
            created_at=datetime.now(),
        )

    async def _get_system_state(self) -> Dict[str, Any]:
        """Get current system state"""
        return {
            "active_agents": len(getattr(self.central_brain, "agent_registry", {})),
            "system_health": "operational",
            "resource_usage": {"cpu": "normal", "memory": "normal"},
            "security_level": self.security_level,
            "active_actions": len(self.active_actions),
        }

    async def _validate_execution_safety(self, action: SystemAction) -> bool:
        """Validate action is safe to execute"""
        return await self.validate_action_safety(action)

    async def _execute_action_steps(self, action: SystemAction) -> Dict[str, Any]:
        """Execute action steps"""
        try:
            results = []
            for step in action.action_plan.execution_steps:
                step_result = await self._execute_single_step(step, action)
                results.append(step_result)

                # Stop if step failed
                if not step_result.get("success", False):
                    break

            success = all(result.get("success", False) for result in results)

            return {
                "success": success,
                "results": results,
                "message": (
                    "Action completed successfully"
                    if success
                    else "Action partially completed"
                ),
                "action_id": action.action_id,
            }

        except Exception as e:
            logger.error(f"Error executing action steps: {e}")
            return {"success": False, "error": str(e), "action_id": action.action_id}

    async def _execute_single_step(
        self, step: Dict[str, Any], action: SystemAction
    ) -> Dict[str, Any]:
        """Execute a single action step"""
        try:
            step_description = step.get("step", "Unknown step")
            logger.info(f"Executing step: {step_description}")

            # Simulate step execution
            await asyncio.sleep(0.1)

            return {
                "success": True,
                "step": step_description,
                "message": f"Step completed: {step_description}",
            }

        except Exception as e:
            logger.error(f"Error executing step: {e}")
            return {
                "success": False,
                "step": step.get("step", "Unknown"),
                "error": str(e),
            }

    async def _delegate_to_agents(self, action: SystemAction) -> Dict[str, Any]:
        """Delegate action to specialized agents"""
        try:
            required_agents = action.capability_assessment.required_agents

            if not required_agents:
                return {
                    "success": False,
                    "error": "No agents specified for delegation",
                    "action_id": action.action_id,
                }

            # Use agent orchestrator if available
            if hasattr(self.central_brain, "agent_orchestrator"):
                task = {
                    "description": action.intent_analysis.primary_goal,
                    "type": action.intent_analysis.command_type.value,
                    "parameters": action.intent_analysis.parameters,
                    "required_agents": required_agents,
                }

                orchestration_result = (
                    await self.central_brain.agent_orchestrator.coordinate_task(task)
                )

                return {
                    "success": orchestration_result.get("success", False),
                    "results": orchestration_result,
                    "message": "Task delegated to agent orchestrator",
                    "action_id": action.action_id,
                }
            else:
                return {
                    "success": False,
                    "error": "Agent orchestrator not available",
                    "action_id": action.action_id,
                }

        except Exception as e:
            logger.error(f"Error delegating to agents: {e}")
            return {"success": False, "error": str(e), "action_id": action.action_id}

    async def _check_user_permissions(self, required_permissions: List[str]) -> bool:
        """Check if user has required permissions"""
        # For now, assume user has all permissions
        # In production, this would check against user roles/permissions
        return True

    async def _check_system_resources(
        self, resource_requirements: Dict[str, Any]
    ) -> bool:
        """Check if system has required resources"""
        # For now, assume resources are available
        # In production, this would check actual system resources
        return True

    def get_metrics(self) -> Dict[str, Any]:
        """Get system controller metrics"""
        total_actions = len(self.action_history)
        successful_actions = len(
            [
                a
                for a in self.action_history
                if a.status == "completed" and a.results and a.results.get("success")
            ]
        )

        return {
            "total_actions": total_actions,
            "successful_actions": successful_actions,
            "success_rate": (
                successful_actions / total_actions if total_actions > 0 else 0
            ),
            "active_actions": len(self.active_actions),
            "security_level": self.security_level,
            "command_types": {
                cmd_type.value: len(
                    [
                        a
                        for a in self.action_history
                        if a.intent_analysis.command_type == cmd_type
                    ]
                )
                for cmd_type in CommandType
            },
        }
