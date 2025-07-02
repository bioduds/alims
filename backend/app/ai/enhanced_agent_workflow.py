"""
CelFlow Enhanced Agent Workflow System
Implements sophisticated workflow orchestration for Gemma 3:4B agent
"""

import json
import logging
import asyncio
from typing import Dict, Any, List, Optional, Tuple
from dataclasses import dataclass, field
from enum import Enum
from datetime import datetime
import re

from .enhanced_tool_system import ToolRegistry, ToolResult, ToolCallParser

logger = logging.getLogger(__name__)


class WorkflowStatus(Enum):
    """Status of workflow execution"""
    PENDING = "pending"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"


class TaskType(Enum):
    """Types of tasks in workflow"""
    ANALYSIS = "analysis"
    TOOL_CALL = "tool_call"
    REASONING = "reasoning"
    SYNTHESIS = "synthesis"
    VALIDATION = "validation"


@dataclass
class WorkflowStep:
    """Individual step in a workflow"""
    id: str
    type: TaskType
    description: str
    tool_name: Optional[str] = None
    parameters: Dict[str, Any] = field(default_factory=dict)
    dependencies: List[str] = field(default_factory=list)
    result: Optional[Any] = None
    status: WorkflowStatus = WorkflowStatus.PENDING
    error: Optional[str] = None
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None


@dataclass
class Workflow:
    """Complete workflow definition"""
    id: str
    description: str
    steps: List[WorkflowStep]
    status: WorkflowStatus = WorkflowStatus.PENDING
    context: Dict[str, Any] = field(default_factory=dict)
    results: Dict[str, Any] = field(default_factory=dict)
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None


class EnhancedAgentWorkflow:
    """Sophisticated workflow orchestrator for agent tasks"""
    
    def __init__(self, tool_registry: ToolRegistry, ollama_client):
        self.tool_registry = tool_registry
        self.ollama_client = ollama_client
        self.active_workflows: Dict[str, Workflow] = {}
        self.workflow_history: List[Workflow] = []
        self.tool_call_parser = ToolCallParser()
        
        logger.info("Enhanced Agent Workflow initialized")
    
    async def process_user_request(self, 
                                   user_message: str, 
                                   context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Process a user request through the enhanced workflow system"""
        
        try:
            logger.info(f"Processing user request: {user_message[:100]}...")
            
            # Step 1: Analyze the request and create workflow plan
            workflow = await self._plan_workflow(user_message, context or {})
            
            if not workflow:
                # Fallback to simple response
                return await self._generate_simple_response(user_message, context)
            
            # Step 2: Execute the workflow
            result = await self._execute_workflow(workflow)
            
            # Step 3: Generate final response
            final_response = await self._synthesize_final_response(workflow, user_message, result)
            
            return {
                "success": True,
                "message": final_response,
                "workflow_id": workflow.id,
                "steps_executed": len([s for s in workflow.steps if s.status == WorkflowStatus.COMPLETED]),
                "tools_used": [s.tool_name for s in workflow.steps if s.tool_name and s.status == WorkflowStatus.COMPLETED],
                "execution_time": (workflow.end_time - workflow.start_time).total_seconds() if workflow.end_time else None
            }
            
        except Exception as e:
            logger.error(f"Workflow processing failed: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "I encountered an error processing your request. Let me try a simpler approach.",
                "fallback": True
            }
    
    async def _plan_workflow(self, user_message: str, context: Dict[str, Any]) -> Optional[Workflow]:
        """Create a workflow plan for the user request"""
        
        # Generate planning prompt
        planning_prompt = self._build_planning_prompt(user_message, context)
        
        try:
            # Get workflow plan from the model
            plan_response = await self.ollama_client.generate_response(
                prompt=user_message,
                system_prompt=planning_prompt,
                context=context
            )
            
            # Parse the workflow plan
            workflow = self._parse_workflow_plan(plan_response, user_message)
            
            if workflow:
                workflow_id = f"workflow_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
                workflow.id = workflow_id
                self.active_workflows[workflow_id] = workflow
                
                logger.info(f"Created workflow with {len(workflow.steps)} steps")
                return workflow
            
            return None
            
        except Exception as e:
            logger.error(f"Workflow planning failed: {e}")
            return None
    
    def _build_planning_prompt(self, user_message: str, context: Dict[str, Any]) -> str:
        """Build the planning prompt for workflow creation"""
        
        # Get relevant tools for this context
        available_tools = self.tool_registry.get_tools_for_context(user_message)
        tool_descriptions = self.tool_registry.generate_tool_descriptions(available_tools)
        
        planning_prompt = f"""You are CelFlow AI, a sophisticated assistant that can break down complex tasks into workflows and use tools effectively.

AVAILABLE TOOLS:
{tool_descriptions}

WORKFLOW PLANNING INSTRUCTIONS:
1. Analyze the user's request carefully
2. Determine if this requires multiple steps or tool usage
3. If tools are needed, create a step-by-step workflow plan
4. If no tools are needed, respond naturally

WORKFLOW FORMAT (use this ONLY if tools are needed):
```json
{{
  "requires_workflow": true,
  "workflow_description": "Brief description of the workflow",
  "steps": [
    {{
      "id": "step_1",
      "type": "tool_call",
      "description": "What this step does",
      "tool_name": "tool_name",
      "parameters": {{"param1": "value1"}},
      "dependencies": []
    }},
    {{
      "id": "step_2", 
      "type": "synthesis",
      "description": "Combine results and respond",
      "dependencies": ["step_1"]
    }}
  ]
}}
```

SIMPLE RESPONSE (use this if no tools needed):
Just respond naturally to the user.

USER REQUEST: {user_message}

CONTEXT: {context}

IMPORTANT: Only create a workflow if tools are genuinely needed. For simple questions or conversations, just respond naturally."""

        return planning_prompt
    
    def _parse_workflow_plan(self, plan_response: str, user_message: str) -> Optional[Workflow]:
        """Parse workflow plan from model response"""
        
        try:
            # Look for JSON workflow definition
            json_pattern = r'```json\s*(\{.*?\})\s*```'
            matches = re.findall(json_pattern, plan_response, re.DOTALL)
            
            for match in matches:
                try:
                    plan_data = json.loads(match)
                    
                    if plan_data.get("requires_workflow", False):
                        workflow = Workflow(
                            id="",  # Will be set later
                            description=plan_data.get("workflow_description", "User request workflow"),
                            steps=[]
                        )
                        
                        # Parse steps
                        for step_data in plan_data.get("steps", []):
                            step = WorkflowStep(
                                id=step_data.get("id", f"step_{len(workflow.steps)}"),
                                type=TaskType(step_data.get("type", "reasoning")),
                                description=step_data.get("description", ""),
                                tool_name=step_data.get("tool_name"),
                                parameters=step_data.get("parameters", {}),
                                dependencies=step_data.get("dependencies", [])
                            )
                            workflow.steps.append(step)
                        
                        return workflow
                        
                except json.JSONDecodeError:
                    continue
            
            return None
            
        except Exception as e:
            logger.error(f"Error parsing workflow plan: {e}")
            return None
    
    async def _execute_workflow(self, workflow: Workflow) -> Dict[str, Any]:
        """Execute a workflow step by step"""
        
        workflow.status = WorkflowStatus.RUNNING
        workflow.start_time = datetime.now()
        
        try:
            # Execute steps in dependency order
            executed_steps = set()
            max_iterations = len(workflow.steps) * 2  # Prevent infinite loops
            iteration = 0
            
            while len(executed_steps) < len(workflow.steps) and iteration < max_iterations:
                iteration += 1
                made_progress = False
                
                for step in workflow.steps:
                    if step.id in executed_steps:
                        continue
                    
                    # Check if dependencies are satisfied
                    if all(dep in executed_steps for dep in step.dependencies):
                        await self._execute_step(step, workflow)
                        executed_steps.add(step.id)
                        made_progress = True
                
                if not made_progress:
                    break
            
            # Check final status
            failed_steps = [s for s in workflow.steps if s.status == WorkflowStatus.FAILED]
            if failed_steps:
                workflow.status = WorkflowStatus.FAILED
            else:
                workflow.status = WorkflowStatus.COMPLETED
            
            workflow.end_time = datetime.now()
            
            # Collect results
            results = {}
            for step in workflow.steps:
                if step.result is not None:
                    results[step.id] = step.result
            
            workflow.results = results
            
            return results
            
        except Exception as e:
            logger.error(f"Workflow execution failed: {e}")
            workflow.status = WorkflowStatus.FAILED
            workflow.end_time = datetime.now()
            return {}
    
    async def _execute_step(self, step: WorkflowStep, workflow: Workflow) -> None:
        """Execute a single workflow step"""
        
        step.status = WorkflowStatus.RUNNING
        step.start_time = datetime.now()
        
        try:
            if step.type == TaskType.TOOL_CALL and step.tool_name:
                # Execute tool
                result = await self.tool_registry.execute_tool(step.tool_name, step.parameters)
                step.result = result
                
                if result.success:
                    step.status = WorkflowStatus.COMPLETED
                else:
                    step.status = WorkflowStatus.FAILED
                    step.error = result.error
            
            elif step.type == TaskType.ANALYSIS:
                # Perform analysis step
                analysis_result = await self._perform_analysis(step, workflow)
                step.result = analysis_result
                step.status = WorkflowStatus.COMPLETED
            
            elif step.type == TaskType.SYNTHESIS:
                # Synthesize results from previous steps
                synthesis_result = await self._perform_synthesis(step, workflow)
                step.result = synthesis_result
                step.status = WorkflowStatus.COMPLETED
            
            else:
                # Generic reasoning step
                step.result = {"status": "completed", "description": step.description}
                step.status = WorkflowStatus.COMPLETED
            
            step.end_time = datetime.now()
            
        except Exception as e:
            logger.error(f"Step execution failed: {e}")
            step.status = WorkflowStatus.FAILED
            step.error = str(e)
            step.end_time = datetime.now()
    
    async def _perform_analysis(self, step: WorkflowStep, workflow: Workflow) -> Dict[str, Any]:
        """Perform analysis step"""
        
        # Get previous results for context
        previous_results = {s.id: s.result for s in workflow.steps if s.result is not None}
        
        analysis_prompt = f"""Analyze the following information based on the step requirements:

Step Description: {step.description}
Previous Results: {json.dumps(previous_results, indent=2)}
Workflow Context: {json.dumps(workflow.context, indent=2)}

Provide a structured analysis."""

        response = await self.ollama_client.generate_response(
            prompt=analysis_prompt,
            system_prompt="You are performing analysis as part of a multi-step workflow. Provide clear, structured insights."
        )
        
        return {"analysis": response, "timestamp": datetime.now().isoformat()}
    
    async def _perform_synthesis(self, step: WorkflowStep, workflow: Workflow) -> Dict[str, Any]:
        """Synthesize results from multiple workflow steps"""
        
        # Collect all previous results
        all_results = {}
        for prev_step in workflow.steps:
            if prev_step.result is not None and prev_step.id != step.id:
                all_results[prev_step.id] = {
                    "description": prev_step.description,
                    "result": prev_step.result
                }
        
        synthesis_prompt = f"""Synthesize the following workflow results into a coherent response:

Synthesis Goal: {step.description}
All Step Results: {json.dumps(all_results, indent=2)}
Original Context: {json.dumps(workflow.context, indent=2)}

Provide a synthesized response that combines all the information meaningfully."""

        response = await self.ollama_client.generate_response(
            prompt=synthesis_prompt,
            system_prompt="You are synthesizing results from multiple workflow steps. Create a comprehensive, coherent response."
        )
        
        return {"synthesis": response, "timestamp": datetime.now().isoformat()}
    
    async def _synthesize_final_response(self, workflow: Workflow, user_message: str, results: Dict[str, Any]) -> str:
        """Generate the final response to the user"""
        
        # Collect all meaningful results
        meaningful_results = []
        
        for step in workflow.steps:
            if step.result and step.status == WorkflowStatus.COMPLETED:
                if isinstance(step.result, dict):
                    if step.result.get("success"):
                        # Tool execution result
                        content = step.result.get("content", "")
                        if content:
                            meaningful_results.append(f"**{step.description}**: {content}")
                    elif "analysis" in step.result:
                        # Analysis result
                        meaningful_results.append(f"**Analysis**: {step.result['analysis']}")
                    elif "synthesis" in step.result:
                        # Synthesis result - this might be the final answer
                        return step.result["synthesis"]
        
        # If we have meaningful results, synthesize them
        if meaningful_results:
            synthesis_prompt = f"""Based on the workflow execution results, provide a comprehensive response to the user's original request.

User's Original Request: {user_message}
Workflow Results:
{chr(10).join(meaningful_results)}

Provide a helpful, complete response that addresses the user's request using the gathered information."""

            final_response = await self.ollama_client.generate_response(
                prompt=synthesis_prompt,
                system_prompt="Synthesize workflow results into a helpful response for the user."
            )
            
            return final_response
        
        # Fallback response
        return "I've processed your request through multiple steps, but I couldn't gather meaningful results. Let me try a different approach."
    
    async def _generate_simple_response(self, user_message: str, context: Optional[Dict[str, Any]]) -> Dict[str, Any]:
        """Generate a simple response when no workflow is needed"""
        
        # Use basic tool calling logic
        available_tools = self.tool_registry.get_tools_for_context(user_message)
        
        # Check if we should search the web for this query
        if self._should_search_web(user_message):
            web_tool = self.tool_registry.get_tool("web_search")
            if web_tool:
                search_result = await self.tool_registry.execute_tool("web_search", {"query": user_message})
                if search_result.success:
                    context = context or {}
                    context["web_search_results"] = search_result.content
        
        # Generate response with available context
        system_prompt = self._build_simple_system_prompt(available_tools)
        
        response = await self.ollama_client.generate_response(
            prompt=user_message,
            system_prompt=system_prompt,
            context=context
        )
        
        return {
            "success": True,
            "message": response,
            "workflow_used": False,
            "tools_used": ["web_search"] if context and context.get("web_search_results") else []
        }
    
    def _should_search_web(self, message: str) -> bool:
        """Determine if the message would benefit from web search"""
        search_indicators = [
            "what is", "who is", "when is", "where is", "how is",
            "current", "latest", "recent", "news", "weather",
            "today", "now", "2024", "2025", "price", "cost"
        ]
        
        message_lower = message.lower()
        return any(indicator in message_lower for indicator in search_indicators)
    
    def _build_simple_system_prompt(self, available_tools: List) -> str:
        """Build system prompt for simple responses"""
        
        tool_list = [tool.name for tool in available_tools] if available_tools else []
        
        return f"""You are CelFlow AI, a helpful and intelligent assistant.

Available capabilities: {', '.join(tool_list) if tool_list else 'general conversation'}

Provide helpful, accurate responses. If you have web search results in the context, use them to provide current information."""
    
    def get_workflow_status(self, workflow_id: str) -> Optional[Dict[str, Any]]:
        """Get status of a specific workflow"""
        workflow = self.active_workflows.get(workflow_id)
        if not workflow:
            return None
        
        return {
            "id": workflow.id,
            "description": workflow.description,
            "status": workflow.status.value,
            "steps_completed": len([s for s in workflow.steps if s.status == WorkflowStatus.COMPLETED]),
            "total_steps": len(workflow.steps),
            "start_time": workflow.start_time.isoformat() if workflow.start_time else None,
            "end_time": workflow.end_time.isoformat() if workflow.end_time else None
        }
    
    def get_system_stats(self) -> Dict[str, Any]:
        """Get system statistics"""
        tool_stats = self.tool_registry.get_execution_stats()
        
        return {
            "active_workflows": len(self.active_workflows),
            "completed_workflows": len(self.workflow_history),
            "tool_stats": tool_stats,
            "system_status": "operational"
        }
