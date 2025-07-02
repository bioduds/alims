#!/usr/bin/env python3
"""
Enhanced Logging System for CelFlow
Provides detailed, structured logging with better visibility into system operations
"""

import logging
import json
import time
from datetime import datetime
from typing import Dict, Any, Optional
from pathlib import Path

class CelFlowLogger:
    """Enhanced logger with structured logging for CelFlow operations"""
    
    def __init__(self, component_name: str):
        self.component_name = component_name
        self.logger = logging.getLogger(f"celflow.{component_name}")
        
        # Create logs directory if it doesn't exist
        logs_dir = Path("logs")
        logs_dir.mkdir(exist_ok=True)
        
        # Set up file handler for this component
        handler = logging.FileHandler(logs_dir / f"{component_name}.log")
        formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S'
        )
        handler.setFormatter(formatter)
        
        # Prevent duplicate handlers
        if not self.logger.handlers:
            self.logger.addHandler(handler)
            self.logger.setLevel(logging.INFO)
    
    def log_lambda_execution(
        self, 
        code: str, 
        purpose: str, 
        executor_type: str,
        result: Dict[str, Any],
        execution_time: float = 0.0
    ):
        """Log Lambda code execution with full context"""
        log_data = {
            "timestamp": datetime.now().isoformat(),
            "component": "lambda_execution",
            "executor_type": executor_type,
            "purpose": purpose,
            "code_length": len(code),
            "code_preview": code[:200] + "..." if len(code) > 200 else code,
            "execution_time": execution_time,
            "success": result.get("success", False),
            "error": result.get("error"),
            "function_name": result.get("function_name"),
            "pattern_type": result.get("pattern_type"),
            "result_type": type(result.get("result", {})).__name__
        }
        
        self.logger.info(f"🚀 LAMBDA_EXECUTION: {json.dumps(log_data, indent=2)}")
    
    def log_routing_decision(
        self, 
        code: str, 
        purpose: str, 
        decision: str, 
        reasoning: str
    ):
        """Log executor routing decisions"""
        log_data = {
            "timestamp": datetime.now().isoformat(),
            "component": "executor_routing",
            "purpose": purpose,
            "decision": decision,
            "reasoning": reasoning,
            "code_indicators": self._analyze_code_indicators(code)
        }
        
        self.logger.info(f"🧭 ROUTING_DECISION: {json.dumps(log_data, indent=2)}")
    
    def log_user_interaction(
        self, 
        user_message: str, 
        ai_response: str, 
        code_executed: bool = False,
        execution_result: Optional[Dict] = None
    ):
        """Log user interactions with AI"""
        log_data = {
            "timestamp": datetime.now().isoformat(),
            "component": "user_interaction",
            "user_message_length": len(user_message),
            "user_message_preview": user_message[:100] + "..." if len(user_message) > 100 else user_message,
            "ai_response_length": len(ai_response),
            "code_executed": code_executed,
            "execution_success": execution_result.get("success") if execution_result else None
        }
        
        self.logger.info(f"💬 USER_INTERACTION: {json.dumps(log_data, indent=2)}")
    
    def log_system_event(self, event_type: str, details: Dict[str, Any]):
        """Log general system events"""
        log_data = {
            "timestamp": datetime.now().isoformat(),
            "component": "system_event",
            "event_type": event_type,
            "details": details
        }
        
        self.logger.info(f"⚙️ SYSTEM_EVENT: {json.dumps(log_data, indent=2)}")
    
    def _analyze_code_indicators(self, code: str) -> Dict[str, Any]:
        """Analyze code for various indicators"""
        code_lower = code.lower()
        
        return {
            "has_imports": "import " in code_lower,
            "has_matplotlib": "matplotlib" in code_lower,
            "has_numpy": "numpy" in code_lower,
            "has_file_ops": any(op in code_lower for op in ["open(", "file(", "with open"]),
            "has_network": any(net in code_lower for net in ["requests", "urllib", "http"]),
            "has_exec_eval": any(danger in code_lower for danger in ["exec(", "eval("]),
            "function_count": code_lower.count("def "),
            "is_visualization": any(viz in code_lower for viz in ["plot", "chart", "graph", "visualization"])
        }
    
    def error(self, message: str, details: Optional[Dict] = None):
        """Log error with optional structured details"""
        if details:
            self.logger.error(f"❌ {message} | Details: {json.dumps(details)}")
        else:
            self.logger.error(f"❌ {message}")
    
    def warning(self, message: str, details: Optional[Dict] = None):
        """Log warning with optional structured details"""
        if details:
            self.logger.warning(f"⚠️ {message} | Details: {json.dumps(details)}")
        else:
            self.logger.warning(f"⚠️ {message}")
    
    def info(self, message: str, details: Optional[Dict] = None):
        """Log info with optional structured details"""
        if details:
            self.logger.info(f"ℹ️ {message} | Details: {json.dumps(details)}")
        else:
            self.logger.info(f"ℹ️ {message}")
    
    def success(self, message: str, details: Optional[Dict] = None):
        """Log success with optional structured details"""
        if details:
            self.logger.info(f"✅ {message} | Details: {json.dumps(details)}")
        else:
            self.logger.info(f"✅ {message}")

# Global logger instances for key components
lambda_logger = CelFlowLogger("lambda_execution")
central_brain_logger = CelFlowLogger("central_brain")
user_interface_logger = CelFlowLogger("user_interface")
system_logger = CelFlowLogger("system")

def create_component_logger(component_name: str) -> CelFlowLogger:
    """Create a logger for a specific component"""
    return CelFlowLogger(component_name)
