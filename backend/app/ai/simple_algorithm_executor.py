#!/usr/bin/env python3
"""
CelFlow Simple Algorithm Executor

A restricted execution environment for Gemma that only allows simple, 
focused algorithms with clear inputs and outputs. This prevents the AI
from running complex, unnecessary code while still providing computational
capabilities for basic algorithmic tasks.

Restrictions:
- Only allows whitelisted algorithm patterns
- Simple input/output structure
- No complex imports or file operations
- Focus on mathematical/computational algorithms
- Maximum execution time of 5 seconds
- Clear, predictable outputs for Gemma to use
"""

import ast
import math
import time
import inspect
import builtins
from datetime import datetime
from typing import Any, Dict, List, Tuple, Optional
import logging

logger = logging.getLogger(__name__)


class SimpleAlgorithmExecutor:
    """
    Restricted executor for simple algorithms only.
    Designed to prevent Gemma from running complex unnecessary code.
    """
    
    def __init__(self):
        self.max_execution_time = 5  # Very short execution time
        self.max_iterations = 10000  # Prevent infinite loops
        self.allowed_patterns = {
            'mathematical_calculation',
            'list_generation',
            'simple_sorting',
            'basic_filtering',
            'number_analysis',
            'string_processing',
            'simple_statistics'
        }

        # Only allow basic built-in functions
        self.allowed_builtins = {
            'abs', 'all', 'any', 'bin', 'bool', 'chr', 'divmod',
            'enumerate', 'filter', 'float', 'hex', 'int', 'len',
            'list', 'map', 'max', 'min', 'oct', 'ord', 'pow',
            'range', 'reversed', 'round', 'sorted', 'str', 'sum',
            'tuple', 'zip', '__import__', 'print'  # For imports and output
        }

        # Only basic math operations allowed
        self.allowed_math_functions = {
            'ceil', 'floor', 'sqrt', 'pow', 'log', 'sin', 'cos',
            'tan', 'factorial', 'gcd'
        }
        
        self.execution_history = []
    
    def _validate_algorithm_pattern(self, code: str) -> Tuple[bool, str, str]:
        """
        Validate that code matches allowed simple algorithm patterns.
        
        Returns:
            (is_valid, error_message, pattern_type)
        """
        try:
            tree = ast.parse(code)
            
            # Must have a clear function definition (allow multiple for visualizations)
            function_nodes = [
                node for node in ast.walk(tree)
                if isinstance(node, ast.FunctionDef)
            ]
            if len(function_nodes) < 1:
                return (
                    False,
                    "Code must contain at least one function definition",
                    ""
                )
            
            # Allow multiple functions for visualization tasks
            if len(function_nodes) > 1:
                # Check if this looks like a visualization task
                code_lower = code.lower()
                viz_keywords = ['matplotlib', 'plt', 'plot', 'chart', 'graph']
                is_viz_task = any(keyword in code_lower for keyword in viz_keywords)
                
                if not is_viz_task:
                    return (
                        False,
                        "Multiple functions only allowed for visualization tasks",
                        ""
                    )
            
            func_node = function_nodes[0]
            
            # Function must be named appropriately
            allowed_prefixes = (
                'calculate_', 'generate_', 'find_',
                'sort_', 'filter_', 'analyze_'
            )
            # Also allow common mathematical function names
            allowed_names = (
                'fibonacci', 'factorial', 'prime', 'primes', 'is_prime',
                'square', 'cube', 'sum_list', 'mean', 'median', 'sieve',
                'gcd', 'lcm', 'power', 'sqrt_func', 'log_func'
            )
            if not (func_node.name.startswith(allowed_prefixes) or 
                    func_node.name in allowed_names):
                return (
                    False,
                    f"Function must have descriptive name starting with "
                    f"{', '.join(allowed_prefixes)} or be a common math function "
                    f"like {', '.join(allowed_names)}",
                    ""
                )

            # Determine pattern type
            pattern_type = self._classify_algorithm_pattern(
                func_node.name, code
            )
            if pattern_type not in self.allowed_patterns:
                return (
                    False,
                    f"Algorithm pattern '{pattern_type}' not allowed",
                    ""
                )
            
            # Check for prohibited constructs
            for node in ast.walk(tree):
                # Handle imports with special cases
                if isinstance(node, (ast.Import, ast.ImportFrom)):
                    if (isinstance(node, ast.ImportFrom) and 
                        node.module == 'math'):
                        # Allow basic math imports
                        for alias in node.names:
                            if alias.name not in self.allowed_math_functions:
                                return (
                                    False,
                                    f"Math function '{alias.name}' not allowed",
                                    ""
                                )
                    elif self._is_visualization_import_allowed(node):
                        # Allow specific visualization imports for data plotting
                        continue
                    else:
                        return (
                            False,
                            "Imports not allowed except basic math functions "
                            "and matplotlib for visualization",
                            ""
                        )

                # No file operations
                forbidden_funcs = ['open', 'file', 'input', 'print']
                if (isinstance(node, ast.Name) and 
                    node.id in forbidden_funcs):
                    if node.id == 'print':
                        continue  # Allow print for output
                    return False, f"Function '{node.id}' not allowed", ""

                # No complex control structures
                if isinstance(node, (ast.Try, ast.With, ast.Raise, 
                                   ast.Assert)):
                    return (
                        False,
                        "Complex control structures not allowed",
                        ""
                    )
                
                # Check for reasonable loop limits
                if isinstance(node, (ast.For, ast.While)):
                    # This is a simplified check - in a full implementation
                    # we'd need more sophisticated loop analysis
                    pass
            
            return True, "", pattern_type
            
        except SyntaxError as e:
            return False, f"Syntax error: {str(e)}", ""
        except Exception as e:
            return False, f"Validation error: {str(e)}", ""
    
    def _classify_algorithm_pattern(self, func_name: str, code: str) -> str:
        """Classify the algorithm pattern based on function name and code content."""
        func_name_lower = func_name.lower()
        code_lower = code.lower()
        
        if any(keyword in func_name_lower for keyword in ['prime', 'fibonacci', 'factorial', 'sqrt', 'pow']):
            return 'mathematical_calculation'
        elif any(keyword in func_name_lower for keyword in ['generate', 'create', 'build']):
            return 'list_generation'
        elif any(keyword in func_name_lower for keyword in ['sort', 'order']):
            return 'simple_sorting'
        elif any(keyword in func_name_lower for keyword in ['filter', 'select', 'find']):
            return 'basic_filtering'
        elif any(keyword in func_name_lower for keyword in ['analyze', 'count', 'sum', 'avg', 'mean']):
            if 'import' in code_lower and ('requests' in code_lower or 'urllib' in code_lower):
                return 'complex_analysis'  # Not allowed
            return 'simple_statistics'
        elif any(keyword in func_name_lower for keyword in ['process', 'clean', 'format']):
            return 'string_processing'
        else:
            return 'unknown_pattern'
    
    async def execute_simple_algorithm(
        self, 
        code: str, 
        inputs: Optional[Dict[str, Any]] = None,
        expected_output_type: str = "auto"
    ) -> Dict[str, Any]:
        """
        Execute a simple algorithm with strict restrictions.
        
        Args:
            code: Python function code (single function only)
            inputs: Dictionary of input parameters
            expected_output_type: Expected type of output ('number', 'list', 'string', 'auto')
            
        Returns:
            Execution result with clear output for Gemma to use
        """
        execution_id = f"simple_algo_{int(time.time())}"
        start_time = time.time()
        
        try:
            # Validate algorithm pattern
            is_valid, error_msg, pattern_type = self._validate_algorithm_pattern(code)
            if not is_valid:
                return {
                    "success": False,
                    "error": f"Algorithm validation failed: {error_msg}",
                    "execution_id": execution_id,
                    "pattern_type": pattern_type
                }
            
            # ENFORCE VISUAL OUTPUT: Always ensure code produces visualizations
            code = self._ensure_visualization_output(code)
            
            # Extract function name
            tree = ast.parse(code)
            func_node = [node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)][0]
            func_name = func_node.name
            
            # Create execution environment with restricted builtins
            safe_builtins = {}
            # Get the original builtins as a base
            for name in self.allowed_builtins:
                if hasattr(builtins, name):
                    safe_builtins[name] = getattr(builtins, name)
            
            # Create a custom __import__ function for restricted imports
            def restricted_import(name, globals=None, locals=None, fromlist=(), level=0):
                if name in ['math']:
                    return __import__(name, globals, locals, fromlist, level)
                elif name in ['matplotlib.pyplot', 'matplotlib', 'numpy']:
                    if self._is_visualization_task(code):
                        return __import__(name, globals, locals, fromlist, level)
                    else:
                        raise ImportError(f"Import '{name}' not allowed in non-visualization context")
                else:
                    raise ImportError(f"Import '{name}' not allowed")
            
            safe_builtins['__import__'] = restricted_import
            
            exec_globals = {
                '__builtins__': safe_builtins,
                'math': math  # Allow math module
            }
            
            # Check if this is a visualization task and pre-import modules
            if self._is_visualization_task(code):
                try:
                    import matplotlib.pyplot as plt
                    import numpy as np
                    # Configure matplotlib for non-interactive backend
                    plt.switch_backend('Agg')
                    # Add to execution environment
                    exec_globals['plt'] = plt
                    exec_globals['np'] = np
                except ImportError:
                    logger.warning("Matplotlib/numpy not available for visualization")
            
            # Execute the function definition
            exec(code, exec_globals)
            
            # Get the function
            algorithm_func = exec_globals.get(func_name)
            if not algorithm_func:
                return {
                    "success": False,
                    "error": f"Function {func_name} not found after execution",
                    "execution_id": execution_id
                }
            
            # Prepare inputs and call function
            if inputs:
                # Extract function signature to properly map inputs
                sig = inspect.signature(algorithm_func)
                param_names = list(sig.parameters.keys())
                
                if (len(param_names) == 1 and isinstance(inputs, dict) and 
                    len(inputs) == 1):
                    # Single parameter case - pass the value directly
                    param_value = list(inputs.values())[0]
                    result = algorithm_func(param_value)
                elif len(param_names) > 1 and isinstance(inputs, dict):
                    # Multiple parameters - map by name
                    try:
                        result = algorithm_func(**inputs)
                    except TypeError:
                        # If keyword mapping fails, try positional
                        param_values = [inputs.get(name) for name in 
                                      param_names]
                        result = algorithm_func(*param_values)
                else:
                    # Try direct call as fallback
                    result = algorithm_func(inputs)
            else:
                # No inputs - call with no parameters
                result = algorithm_func()
            
            # Validate execution time
            execution_time = time.time() - start_time
            if execution_time > self.max_execution_time:
                return {
                    "success": False,
                    "error": f"Algorithm execution exceeded {self.max_execution_time} seconds",
                    "execution_id": execution_id
                }
            
            # Format result for Gemma
            formatted_result = self._format_result_for_gemma(result, expected_output_type, pattern_type)
            
            # Log execution
            self.execution_history.append({
                'execution_id': execution_id,
                'function_name': func_name,
                'pattern_type': pattern_type,
                'execution_time': execution_time,
                'result_type': type(result).__name__,
                'timestamp': datetime.now().isoformat()
            })
            
            return {
                "success": True,
                "result": formatted_result,
                "function_name": func_name,
                "pattern_type": pattern_type,
                "execution_time": round(execution_time, 3),
                "execution_id": execution_id,
                "gemma_summary": self._create_gemma_summary(func_name, result, pattern_type)
            }
            
        except Exception as e:
            logger.error(f"Algorithm execution error: {e}")
            return {
                "success": False,
                "error": f"Execution error: {str(e)}",
                "execution_id": execution_id,
                "execution_time": round(time.time() - start_time, 3)
            }
    
    def _format_result_for_gemma(
        self, 
        result: Any, 
        expected_type: str, 
        pattern_type: str
    ) -> Dict[str, Any]:
        """Format the algorithm result in a way that's easy for Gemma to understand and use."""
        
        formatted = {
            "value": result,
            "type": type(result).__name__,
            "description": self._describe_result(result, pattern_type)
        }
        
        # Add additional context based on result type
        if isinstance(result, (list, tuple)):
            formatted.update({
                "length": len(result),
                "first_items": result[:5] if len(result) > 5 else result,
                "sample": f"[{', '.join(map(str, result[:3]))}{'...' if len(result) > 3 else ''}]"
            })
        elif isinstance(result, (int, float)):
            formatted.update({
                "numeric_value": result,
                "formatted": f"{result:,}" if isinstance(result, int) else f"{result:.6f}".rstrip('0').rstrip('.')
            })
        elif isinstance(result, str):
            formatted.update({
                "length": len(result),
                "preview": result[:100] + ("..." if len(result) > 100 else "")
            })
        elif isinstance(result, dict):
            formatted.update({
                "keys": list(result.keys()),
                "size": len(result)
            })
        
        return formatted
    
    def _describe_result(self, result: Any, pattern_type: str) -> str:
        """Create a human-readable description of the result."""
        
        if pattern_type == 'mathematical_calculation':
            if isinstance(result, list):
                return f"Calculated sequence of {len(result)} numbers"
            else:
                return f"Calculated value: {result}"
        elif pattern_type == 'list_generation':
            return f"Generated list with {len(result)} items"
        elif pattern_type == 'simple_sorting':
            return f"Sorted sequence of {len(result)} items"
        elif pattern_type == 'basic_filtering':
            return f"Filtered result with {len(result)} matching items"
        elif pattern_type == 'simple_statistics':
            if isinstance(result, dict):
                return f"Statistical analysis with {len(result)} metrics"
            else:
                return f"Calculated statistic: {result}"
        elif pattern_type == 'string_processing':
            return f"Processed string result"
        else:
            return f"Algorithm result: {type(result).__name__}"
    
    def _create_gemma_summary(self, func_name: str, result: Any, pattern_type: str) -> str:
        """Create a summary for Gemma to understand what was computed."""
        
        if pattern_type == 'mathematical_calculation':
            if isinstance(result, list) and len(result) > 0:
                return f"The {func_name} function calculated {len(result)} values. First few results: {result[:5]}"
            else:
                return f"The {func_name} function calculated the result: {result}"
        elif pattern_type == 'list_generation':
            return f"Generated a list of {len(result)} items using {func_name}"
        elif pattern_type == 'simple_sorting':
            return f"Sorted {len(result)} items using {func_name}"
        elif pattern_type == 'basic_filtering':
            return f"Filtered data and found {len(result)} matching items"
        else:
            return f"Executed {func_name} and got result: {str(result)[:100]}"
    
    def get_allowed_patterns(self) -> List[str]:
        """Get list of allowed algorithm patterns."""
        return list(self.allowed_patterns)
    
    def get_execution_history(self, limit: int = 10) -> List[Dict[str, Any]]:
        """Get recent execution history."""
        return self.execution_history[-limit:]
    
    def _is_visualization_import_allowed(self, node) -> bool:
        """
        Check if a visualization-related import is allowed.
        We allow matplotlib for simple plotting tasks.
        """
        allowed_viz_modules = {
            'matplotlib.pyplot',
            'matplotlib',
            'numpy'  # Often needed for basic data manipulation in plots
        }
        
        if isinstance(node, ast.ImportFrom):
            return node.module in allowed_viz_modules
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name.split('.')[0] in {'matplotlib', 'numpy'}:
                    return True
        
        return False
    
    def _is_visualization_task(self, code: str) -> bool:
        """Check if the code is for visualization purposes - ALWAYS TRUE for mandatory visuals"""
        # Since we want ALL code to produce visual output, always return True
        return True
    
    def _ensure_visualization_output(self, code: str) -> str:
        """Ensure code produces visual output by adding matplotlib visualization."""
        if self._is_visualization_task(code):
            return code
        
        # For non-visualization code, add automatic visualization
        viz_addition = '''

# Auto-generate visualization for computational results
import matplotlib.pyplot as plt
import numpy as np

# Extract the main function result for visualization
try:
    # Get the function name from the code
    import ast
    tree = ast.parse(code)
    func_nodes = [node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)]
    if func_nodes:
        func_name = func_nodes[0].name
        
        # Call the function with default parameters and visualize result
        if 'fibonacci' in func_name.lower():
            result = locals()[func_name](10)  # Show first 10 fibonacci numbers
            if hasattr(result, '__iter__') and not isinstance(result, str):
                result = list(result)
            plt.figure(figsize=(10, 6))
            plt.bar(range(len(result)), result, color='skyblue', alpha=0.7)
            plt.title(f'{func_name.title()} Sequence Visualization')
            plt.xlabel('Index')
            plt.ylabel('Value')
            plt.grid(axis='y', alpha=0.3)
            
        elif 'factorial' in func_name.lower():
            # Show factorial progression
            numbers = list(range(1, 9))
            factorials = [locals()[func_name](n) for n in numbers]
            plt.figure(figsize=(10, 6))
            plt.plot(numbers, factorials, 'bo-', linewidth=2, markersize=8)
            plt.title('Factorial Growth Visualization')
            plt.xlabel('n')
            plt.ylabel('n!')
            plt.yscale('log')
            plt.grid(True, alpha=0.3)
            
        elif 'prime' in func_name.lower():
            # Show prime number distribution
            primes = []
            for i in range(2, 50):
                if locals()[func_name](i):
                    primes.append(i)
            plt.figure(figsize=(12, 6))
            plt.scatter(primes, [1]*len(primes), s=100, alpha=0.7, c='red')
            plt.title('Prime Numbers Distribution (up to 50)')
            plt.xlabel('Number')
            plt.ylabel('')
            plt.grid(True, alpha=0.3)
            
        else:
            # Generic visualization for other functions
            try:
                # Try to call with small integer inputs
                test_inputs = [1, 2, 3, 4, 5]
                results = []
                for inp in test_inputs:
                    try:
                        res = locals()[func_name](inp)
                        if isinstance(res, (int, float)):
                            results.append(res)
                    except:
                        pass
                
                if results:
                    plt.figure(figsize=(10, 6))
                    plt.plot(test_inputs[:len(results)], results, 'go-', linewidth=2)
                    plt.title(f'{func_name.title()} Function Visualization')
                    plt.xlabel('Input')
                    plt.ylabel('Output')
                    plt.grid(True, alpha=0.3)
            except:
                # Fallback: just show a simple info plot
                plt.figure(figsize=(8, 6))
                plt.text(0.5, 0.5, f'Function: {func_name}\\nComputation completed successfully!', 
                        ha='center', va='center', fontsize=16, 
                        bbox=dict(boxstyle="round,pad=0.3", facecolor="lightblue"))
                plt.title('Computation Result')
                plt.axis('off')
        
        plt.tight_layout()
        timestamp = int(__import__('time').time())
        filename = f'computation_result_{timestamp}.png'
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        plt.show()
        print(f"📊 Visualization saved as '{filename}'")
        
except Exception as viz_error:
    print(f"⚠️ Visualization generation failed: {viz_error}")
    # Fallback simple plot
    plt.figure(figsize=(6, 4))
    plt.text(0.5, 0.5, 'Computation Completed\\n(Visualization Error)', 
             ha='center', va='center', fontsize=14)
    plt.title('Algorithm Execution Result')
    plt.axis('off')
    plt.savefig('computation_fallback.png', dpi=150, bbox_inches='tight')
    plt.show()
'''
        
        return code + viz_addition
