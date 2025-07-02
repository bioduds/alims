"""
ALims Enhanced Tool System
Implements modern tool calling patterns for Gemma 3:4B agent
"""

import json
import logging
import asyncio
from abc import ABC, abstractmethod
from typing import Dict, Any, List, Optional, Union, Callable
from dataclasses import dataclass
from enum import Enum
from datetime import datetime
import traceback

logger = logging.getLogger(__name__)


class ToolCategory(Enum):
    """Categories for organizing tools"""
    WEB_SEARCH = "web_search"
    FILE_SYSTEM = "file_system"
    CODE_EXECUTION = "code_execution"
    DATA_ANALYSIS = "data_analysis"
    COMMUNICATION = "communication"
    SYSTEM_CONTROL = "system_control"
    EXTERNAL_API = "external_api"
    UTILITY = "utility"


@dataclass
class ToolParameter:
    """Definition of a tool parameter"""
    name: str
    type: str
    description: str
    required: bool = True
    default: Any = None
    enum_values: Optional[List[str]] = None


@dataclass
class ToolResult:
    """Result from tool execution"""
    success: bool
    content: Any
    error: Optional[str] = None
    metadata: Optional[Dict[str, Any]] = None
    execution_time: Optional[float] = None


class Tool(ABC):
    """Abstract base class for all tools"""
    
    def __init__(self):
        self.name = self.get_name()
        self.description = self.get_description()
        self.category = self.get_category()
        self.parameters = self.get_parameters()
        self.execution_count = 0
        self.last_execution = None
    
    @abstractmethod
    def get_name(self) -> str:
        """Return the tool name"""
        pass
    
    @abstractmethod
    def get_description(self) -> str:
        """Return the tool description"""
        pass
    
    @abstractmethod
    def get_category(self) -> ToolCategory:
        """Return the tool category"""
        pass
    
    @abstractmethod
    def get_parameters(self) -> List[ToolParameter]:
        """Return the tool parameters"""
        pass
    
    @abstractmethod
    async def execute(self, **kwargs) -> ToolResult:
        """Execute the tool with given parameters"""
        pass
    
    def validate_parameters(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Validate and process parameters"""
        validated = {}
        
        for param in self.parameters:
            if param.name in params:
                validated[param.name] = params[param.name]
            elif param.required and param.default is None:
                raise ValueError(f"Required parameter '{param.name}' missing")
            elif param.default is not None:
                validated[param.name] = param.default
        
        return validated
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert tool to dictionary for prompt generation"""
        return {
            "name": self.name,
            "description": self.description,
            "category": self.category.value,
            "parameters": [
                {
                    "name": p.name,
                    "type": p.type,
                    "description": p.description,
                    "required": p.required,
                    "default": p.default,
                    "enum_values": p.enum_values
                }
                for p in self.parameters
            ]
        }


class WebSearchTool(Tool):
    """Enhanced web search tool"""
    
    def __init__(self, search_client):
        self.search_client = search_client
        super().__init__()
    
    def get_name(self) -> str:
        return "web_search"
    
    def get_description(self) -> str:
        return "Search the web for current information and real-time data"
    
    def get_category(self) -> ToolCategory:
        return ToolCategory.WEB_SEARCH
    
    def get_parameters(self) -> List[ToolParameter]:
        return [
            ToolParameter(
                name="query",
                type="string",
                description="The search query to execute",
                required=True
            ),
            ToolParameter(
                name="max_results",
                type="integer",
                description="Maximum number of results to return",
                required=False,
                default=5
            )
        ]
    
    async def execute(self, **kwargs) -> ToolResult:
        """Execute web search"""
        start_time = datetime.now()
        
        try:
            validated_params = self.validate_parameters(kwargs)
            query = validated_params["query"]
            max_results = validated_params["max_results"]
            
            logger.info(f"Executing web search: {query}")
            
            # Use the existing web search implementation
            search_results = await self.search_client(query)
            
            self.execution_count += 1
            self.last_execution = datetime.now()
            
            execution_time = (datetime.now() - start_time).total_seconds()
            
            return ToolResult(
                success=True,
                content=search_results,
                metadata={
                    "query": query,
                    "max_results": max_results,
                    "result_count": len(search_results.split('\n')) if search_results else 0
                },
                execution_time=execution_time
            )
            
        except Exception as e:
            logger.error(f"Web search failed: {e}")
            execution_time = (datetime.now() - start_time).total_seconds()
            
            return ToolResult(
                success=False,
                content=None,
                error=str(e),
                execution_time=execution_time
            )


class CodeExecutionTool(Tool):
    """Safe code execution tool"""
    
    def __init__(self, executor):
        self.executor = executor
        super().__init__()
    
    def get_name(self) -> str:
        return "execute_code"
    
    def get_description(self) -> str:
        return "Execute Python code safely with visualization output"
    
    def get_category(self) -> ToolCategory:
        return ToolCategory.CODE_EXECUTION
    
    def get_parameters(self) -> List[ToolParameter]:
        return [
            ToolParameter(
                name="code",
                type="string",
                description="Python code to execute",
                required=True
            ),
            ToolParameter(
                name="algorithm_type",
                type="string",
                description="Type of algorithm being executed",
                required=False,
                default="general",
                enum_values=["math", "data_analysis", "visualization", "general"]
            )
        ]
    
    async def execute(self, **kwargs) -> ToolResult:
        """Execute code safely"""
        start_time = datetime.now()
        
        try:
            validated_params = self.validate_parameters(kwargs)
            code = validated_params["code"]
            algorithm_type = validated_params["algorithm_type"]
            
            logger.info(f"Executing code: {algorithm_type}")
            
            # Use the simple algorithm executor for safety
            result = await self.executor.execute_algorithm(code, algorithm_type)
            
            self.execution_count += 1
            self.last_execution = datetime.now()
            
            execution_time = (datetime.now() - start_time).total_seconds()
            
            return ToolResult(
                success=result.get("success", False),
                content=result.get("result"),
                error=result.get("error"),
                metadata={
                    "algorithm_type": algorithm_type,
                    "has_visualization": result.get("has_visualization", False),
                    "output_files": result.get("output_files", [])
                },
                execution_time=execution_time
            )
            
        except Exception as e:
            logger.error(f"Code execution failed: {e}")
            execution_time = (datetime.now() - start_time).total_seconds()
            
            return ToolResult(
                success=False,
                content=None,
                error=str(e),
                execution_time=execution_time
            )


class ToolRegistry:
    """Registry for managing and organizing tools"""
    
    def __init__(self):
        self.tools: Dict[str, Tool] = {}
        self.categories: Dict[ToolCategory, List[str]] = {}
        self.execution_history: List[Dict[str, Any]] = []
        
        # Initialize categories
        for category in ToolCategory:
            self.categories[category] = []
    
    def register_tool(self, tool: Tool) -> None:
        """Register a new tool"""
        if tool.name in self.tools:
            logger.warning(f"Tool '{tool.name}' already registered, replacing")
        
        self.tools[tool.name] = tool
        
        # Add to category
        if tool.name not in self.categories[tool.category]:
            self.categories[tool.category].append(tool.name)
        
        logger.info(f"Registered tool: {tool.name} ({tool.category.value})")
    
    def get_tool(self, name: str) -> Optional[Tool]:
        """Get a tool by name"""
        return self.tools.get(name)
    
    def get_tools_by_category(self, category: ToolCategory) -> List[Tool]:
        """Get all tools in a category"""
        tool_names = self.categories.get(category, [])
        return [self.tools[name] for name in tool_names if name in self.tools]
    
    def get_all_tools(self) -> List[Tool]:
        """Get all registered tools"""
        return list(self.tools.values())
    
    def get_tools_for_context(self, context: str, max_tools: int = 10) -> List[Tool]:
        """Get relevant tools based on context"""
        context_lower = context.lower()
        relevant_tools = []
        
        # Score tools based on context relevance
        tool_scores = []
        
        for tool in self.tools.values():
            score = 0
            
            # Check if tool name appears in context
            if tool.name.lower() in context_lower:
                score += 10
            
            # Check if tool description keywords appear in context
            description_words = tool.description.lower().split()
            for word in description_words:
                if word in context_lower and len(word) > 3:
                    score += 1
            
            # Bonus for certain categories based on context
            if "search" in context_lower and tool.category == ToolCategory.WEB_SEARCH:
                score += 5
            if any(word in context_lower for word in ["code", "execute", "run", "algorithm"]) and tool.category == ToolCategory.CODE_EXECUTION:
                score += 5
            if any(word in context_lower for word in ["file", "read", "write", "save"]) and tool.category == ToolCategory.FILE_SYSTEM:
                score += 5
            
            if score > 0:
                tool_scores.append((tool, score))
        
        # Sort by score and return top tools
        tool_scores.sort(key=lambda x: x[1], reverse=True)
        return [tool for tool, score in tool_scores[:max_tools]]
    
    async def execute_tool(self, name: str, parameters: Dict[str, Any]) -> ToolResult:
        """Execute a tool by name"""
        tool = self.get_tool(name)
        if not tool:
            return ToolResult(
                success=False,
                content=None,
                error=f"Tool '{name}' not found"
            )
        
        try:
            result = await tool.execute(**parameters)
            
            # Log execution
            self.execution_history.append({
                "tool_name": name,
                "parameters": parameters,
                "success": result.success,
                "timestamp": datetime.now().isoformat(),
                "execution_time": result.execution_time
            })
            
            return result
            
        except Exception as e:
            logger.error(f"Tool execution failed: {e}")
            return ToolResult(
                success=False,
                content=None,
                error=f"Tool execution error: {str(e)}"
            )
    
    def generate_tool_descriptions(self, tools: Optional[List[Tool]] = None) -> str:
        """Generate formatted tool descriptions for prompts"""
        if tools is None:
            tools = self.get_all_tools()
        
        descriptions = []
        
        for tool in tools:
            desc = f"**{tool.name}** ({tool.category.value}):\n"
            desc += f"  Description: {tool.description}\n"
            desc += f"  Parameters:\n"
            
            for param in tool.parameters:
                required_str = "required" if param.required else "optional"
                default_str = f" (default: {param.default})" if param.default is not None else ""
                enum_str = f" (options: {', '.join(param.enum_values)})" if param.enum_values else ""
                
                desc += f"    - {param.name} ({param.type}, {required_str}): {param.description}{default_str}{enum_str}\n"
            
            descriptions.append(desc)
        
        return "\n".join(descriptions)
    
    def get_execution_stats(self) -> Dict[str, Any]:
        """Get execution statistics"""
        total_executions = len(self.execution_history)
        successful_executions = sum(1 for exec in self.execution_history if exec["success"])
        
        tool_usage = {}
        for exec in self.execution_history:
            tool_name = exec["tool_name"]
            tool_usage[tool_name] = tool_usage.get(tool_name, 0) + 1
        
        return {
            "total_executions": total_executions,
            "successful_executions": successful_executions,
            "success_rate": successful_executions / total_executions if total_executions > 0 else 0,
            "tool_usage": tool_usage,
            "registered_tools": len(self.tools),
            "categories": {cat.value: len(tools) for cat, tools in self.categories.items() if tools}
        }


class ToolCallParser:
    """Parser for extracting tool calls from model responses"""
    
    @staticmethod
    def parse_tool_call(response: str) -> Optional[Dict[str, Any]]:
        """Parse a tool call from model response"""
        try:
            # Look for JSON blocks in the response
            import re
            
            # Pattern to match JSON blocks
            json_pattern = r'```json\s*(\{.*?\})\s*```'
            matches = re.findall(json_pattern, response, re.DOTALL)
            
            for match in matches:
                try:
                    parsed = json.loads(match)
                    if parsed.get("action") == "tool_call":
                        return {
                            "tool": parsed.get("tool"),
                            "arguments": parsed.get("arguments", {}),
                            "reasoning": parsed.get("reasoning", "")
                        }
                except json.JSONDecodeError:
                    continue
            
            # If no JSON block, try to parse inline JSON
            try:
                # Look for action: tool_call pattern
                if '"action": "tool_call"' in response:
                    # Extract JSON-like structure
                    start = response.find('{')
                    end = response.rfind('}') + 1
                    if start != -1 and end > start:
                        json_str = response[start:end]
                        parsed = json.loads(json_str)
                        if parsed.get("action") == "tool_call":
                            return {
                                "tool": parsed.get("tool"),
                                "arguments": parsed.get("arguments", {}),
                                "reasoning": parsed.get("reasoning", "")
                            }
            except:
                pass
            
            return None
            
        except Exception as e:
            logger.error(f"Error parsing tool call: {e}")
            return None
    
    @staticmethod
    def should_use_tools(response: str, available_tools: List[str]) -> bool:
        """Determine if the response suggests tool usage"""
        response_lower = response.lower()
        
        # Check for explicit tool indicators
        tool_indicators = [
            "let me search",
            "i'll search",
            "i need to search",
            "let me check",
            "i'll check",
            "let me run",
            "i'll execute",
            "let me calculate",
            "i need to find"
        ]
        
        for indicator in tool_indicators:
            if indicator in response_lower:
                return True
        
        # Check if any tool names are mentioned
        for tool_name in available_tools:
            if tool_name.lower() in response_lower:
                return True
        
        return False
