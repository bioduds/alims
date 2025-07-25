#!/usr/bin/env python3
"""
ALIMS Advanced Debugging System
Comprehensive tracing and debugging for Main Interface Agent and all sub-agents
"""

import asyncio
import json
import logging
import traceback
from contextlib import contextmanager
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Union
from dataclasses import dataclass, asdict
import inspect
import sys
from functools import wraps

class DebugLevel(Enum):
    TRACE = "TRACE"      # Every function call, parameter, return value
    DEBUG = "DEBUG"      # Key decision points, state changes
    INFO = "INFO"        # High-level operations, agent interactions
    WARN = "WARN"        # Recoverable issues, fallbacks
    ERROR = "ERROR"      # Failures, exceptions
    CRITICAL = "CRITICAL" # System failures

@dataclass
class AgentTraceEvent:
    """Individual agent trace event"""
    timestamp: str
    agent_id: str
    agent_type: str
    event_type: str  # INIT, RECEIVE_MESSAGE, PROCESS, RESPOND, ERROR, STATE_CHANGE
    message: str
    data: Dict[str, Any]
    level: DebugLevel
    conversation_id: Optional[str] = None
    parent_trace_id: Optional[str] = None
    trace_id: Optional[str] = None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            **asdict(self),
            'level': self.level.value,
            'formatted_time': datetime.fromisoformat(self.timestamp).strftime("%H:%M:%S.%f")[:-3]
        }

class ALIMSDebugTracer:
    """Advanced debugging and tracing system for ALIMS"""
    
    def __init__(self, 
                 log_level: DebugLevel = DebugLevel.DEBUG,
                 console_output: bool = True,
                 file_output: bool = True,
                 structured_output: bool = True):
        
        self.log_level = log_level
        self.console_output = console_output
        self.file_output = file_output
        self.structured_output = structured_output
        
        # Trace storage
        self.trace_events: List[AgentTraceEvent] = []
        self.active_conversations: Dict[str, List[AgentTraceEvent]] = {}
        self.agent_states: Dict[str, Dict[str, Any]] = {}
        
        # Setup logging
        self._setup_logging()
        
        # Performance tracking
        self.performance_metrics: Dict[str, List[float]] = {}
        
    def _setup_logging(self):
        """Setup advanced logging configuration"""
        # Create logs directory
        log_dir = Path("logs/debug")
        log_dir.mkdir(parents=True, exist_ok=True)
        
        # Configure logger
        self.logger = logging.getLogger("ALIMS_DEBUG")
        self.logger.setLevel(logging.DEBUG)
        
        # Remove existing handlers
        for handler in self.logger.handlers[:]:
            self.logger.removeHandler(handler)
        
        # File handler with detailed format
        if self.file_output:
            file_handler = logging.FileHandler(
                log_dir / f"alims_debug_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
            )
            file_formatter = logging.Formatter(
                '%(asctime)s.%(msecs)03d | %(levelname)-8s | %(name)s | %(message)s',
                datefmt='%H:%M:%S'
            )
            file_handler.setFormatter(file_formatter)
            self.logger.addHandler(file_handler)
        
        # Console handler with colored output
        if self.console_output:
            console_handler = logging.StreamHandler(sys.stdout)
            console_formatter = ColoredFormatter()
            console_handler.setFormatter(console_formatter)
            self.logger.addHandler(console_handler)

    def trace_agent_event(self, 
                         agent_id: str,
                         agent_type: str,
                         event_type: str,
                         message: str,
                         data: Dict[str, Any] = None,
                         level: DebugLevel = DebugLevel.DEBUG,
                         conversation_id: str = None) -> str:
        """Record an agent trace event"""
        
        event = AgentTraceEvent(
            timestamp=datetime.now().isoformat(),
            agent_id=agent_id,
            agent_type=agent_type,
            event_type=event_type,
            message=message,
            data=data or {},
            level=level,
            conversation_id=conversation_id,
            trace_id=f"{agent_id}_{datetime.now().strftime('%H%M%S%f')}"
        )
        
        # Store event
        self.trace_events.append(event)
        
        # Store by conversation
        if conversation_id:
            if conversation_id not in self.active_conversations:
                self.active_conversations[conversation_id] = []
            self.active_conversations[conversation_id].append(event)
        
        # Log based on level
        if self._should_log(level):
            self._log_event(event)
        
        return event.trace_id

    def _should_log(self, level: DebugLevel) -> bool:
        """Check if event should be logged based on current log level"""
        level_order = {
            DebugLevel.TRACE: 0,
            DebugLevel.DEBUG: 1,
            DebugLevel.INFO: 2,
            DebugLevel.WARN: 3,
            DebugLevel.ERROR: 4,
            DebugLevel.CRITICAL: 5
        }
        return level_order[level] >= level_order[self.log_level]

    def _log_event(self, event: AgentTraceEvent):
        """Log event to configured outputs"""
        
        # Format message
        formatted_msg = f"🤖 {event.agent_type}[{event.agent_id}] | {event.event_type} | {event.message}"
        
        if event.conversation_id:
            formatted_msg += f" | Conv: {event.conversation_id}"
        
        if event.data:
            formatted_msg += f" | Data: {json.dumps(event.data, indent=None)[:200]}..."
        
        # Log to appropriate level
        log_method = {
            DebugLevel.TRACE: self.logger.debug,
            DebugLevel.DEBUG: self.logger.debug,
            DebugLevel.INFO: self.logger.info,
            DebugLevel.WARN: self.logger.warning,
            DebugLevel.ERROR: self.logger.error,
            DebugLevel.CRITICAL: self.logger.critical
        }[event.level]
        
        log_method(formatted_msg)

    @contextmanager
    def trace_agent_operation(self, agent_id: str, agent_type: str, operation: str, conversation_id: str = None):
        """Context manager for tracing agent operations with timing"""
        start_time = datetime.now()
        trace_id = self.trace_agent_event(
            agent_id=agent_id,
            agent_type=agent_type,
            event_type="OPERATION_START",
            message=f"Starting {operation}",
            level=DebugLevel.TRACE,
            conversation_id=conversation_id
        )
        
        try:
            yield trace_id
        except Exception as e:
            self.trace_agent_event(
                agent_id=agent_id,
                agent_type=agent_type,
                event_type="OPERATION_ERROR",
                message=f"Error in {operation}: {str(e)}",
                data={
                    "operation": operation,
                    "error": str(e),
                    "traceback": traceback.format_exc()
                },
                level=DebugLevel.ERROR,
                conversation_id=conversation_id
            )
            raise
        finally:
            duration = (datetime.now() - start_time).total_seconds()
            self.trace_agent_event(
                agent_id=agent_id,
                agent_type=agent_type,
                event_type="OPERATION_END",
                message=f"Completed {operation} in {duration:.3f}s",
                data={
                    "operation": operation,
                    "duration_seconds": duration
                },
                level=DebugLevel.TRACE,
                conversation_id=conversation_id
            )
            
            # Track performance
            if operation not in self.performance_metrics:
                self.performance_metrics[operation] = []
            self.performance_metrics[operation].append(duration)

    def update_agent_state(self, agent_id: str, agent_type: str, state_update: Dict[str, Any], conversation_id: str = None):
        """Update and trace agent state changes"""
        
        if agent_id not in self.agent_states:
            self.agent_states[agent_id] = {}
        
        old_state = self.agent_states[agent_id].copy()
        self.agent_states[agent_id].update(state_update)
        
        # Identify changes
        changes = {}
        for key, new_value in state_update.items():
            old_value = old_state.get(key, "<UNSET>")
            if old_value != new_value:
                changes[key] = {"from": old_value, "to": new_value}
        
        if changes:
            self.trace_agent_event(
                agent_id=agent_id,
                agent_type=agent_type,
                event_type="STATE_CHANGE",
                message=f"State updated: {', '.join(changes.keys())}",
                data={
                    "changes": changes,
                    "full_state": self.agent_states[agent_id]
                },
                level=DebugLevel.DEBUG,
                conversation_id=conversation_id
            )

    def get_conversation_trace(self, conversation_id: str) -> List[Dict[str, Any]]:
        """Get full trace for a conversation"""
        if conversation_id in self.active_conversations:
            return [event.to_dict() for event in self.active_conversations[conversation_id]]
        return []

    def get_agent_state(self, agent_id: str) -> Dict[str, Any]:
        """Get current agent state"""
        return self.agent_states.get(agent_id, {})

    def get_performance_summary(self) -> Dict[str, Dict[str, float]]:
        """Get performance metrics summary"""
        summary = {}
        for operation, times in self.performance_metrics.items():
            if times:
                summary[operation] = {
                    "count": len(times),
                    "avg_seconds": sum(times) / len(times),
                    "min_seconds": min(times),
                    "max_seconds": max(times),
                    "total_seconds": sum(times)
                }
        return summary

    def export_trace_data(self, conversation_id: str = None) -> Dict[str, Any]:
        """Export trace data for external analysis"""
        if conversation_id:
            events = self.get_conversation_trace(conversation_id)
        else:
            events = [event.to_dict() for event in self.trace_events]
        
        return {
            "export_timestamp": datetime.now().isoformat(),
            "conversation_id": conversation_id,
            "events": events,
            "agent_states": self.agent_states,
            "performance_metrics": self.get_performance_summary(),
            "total_events": len(events)
        }

class ColoredFormatter(logging.Formatter):
    """Colored console formatter"""
    
    COLORS = {
        'DEBUG': '\033[36m',     # Cyan
        'INFO': '\033[32m',      # Green
        'WARNING': '\033[33m',   # Yellow
        'ERROR': '\033[31m',     # Red
        'CRITICAL': '\033[91m'   # Bright Red
    }
    RESET = '\033[0m'
    
    def format(self, record):
        color = self.COLORS.get(record.levelname, '')
        record.levelname = f"{color}{record.levelname}{self.RESET}"
        return super().format(record)

# Global tracer instance
_global_tracer: Optional[ALIMSDebugTracer] = None

def get_debug_tracer() -> ALIMSDebugTracer:
    """Get or create global debug tracer"""
    global _global_tracer
    if _global_tracer is None:
        _global_tracer = ALIMSDebugTracer()
    return _global_tracer

def trace_agent_call(agent_type: str = None):
    """Decorator for automatic agent method tracing"""
    def decorator(func):
        @wraps(func)
        async def async_wrapper(self, *args, **kwargs):
            tracer = get_debug_tracer()
            agent_id = getattr(self, 'agent_id', getattr(self, 'id', 'unknown'))
            operation = f"{func.__name__}"
            
            with tracer.trace_agent_operation(agent_id, agent_type or self.__class__.__name__, operation):
                # Log parameters
                tracer.trace_agent_event(
                    agent_id=agent_id,
                    agent_type=agent_type or self.__class__.__name__,
                    event_type="METHOD_CALL",
                    message=f"Calling {operation}",
                    data={
                        "args": str(args)[:200],
                        "kwargs": {k: str(v)[:100] for k, v in kwargs.items()}
                    },
                    level=DebugLevel.TRACE
                )
                
                result = await func(self, *args, **kwargs)
                
                # Log result
                tracer.trace_agent_event(
                    agent_id=agent_id,
                    agent_type=agent_type or self.__class__.__name__,
                    event_type="METHOD_RETURN",
                    message=f"Returning from {operation}",
                    data={"result_type": type(result).__name__},
                    level=DebugLevel.TRACE
                )
                
                return result
        
        @wraps(func)
        def sync_wrapper(self, *args, **kwargs):
            tracer = get_debug_tracer()
            agent_id = getattr(self, 'agent_id', getattr(self, 'id', 'unknown'))
            operation = f"{func.__name__}"
            
            with tracer.trace_agent_operation(agent_id, agent_type or self.__class__.__name__, operation):
                return func(self, *args, **kwargs)
        
        return async_wrapper if asyncio.iscoroutinefunction(func) else sync_wrapper
    return decorator

if __name__ == "__main__":
    # Test the debugging system
    tracer = ALIMSDebugTracer(log_level=DebugLevel.TRACE)
    
    # Test trace events
    tracer.trace_agent_event(
        agent_id="main_interface_001",
        agent_type="MainInterfaceAgent", 
        event_type="INIT",
        message="Agent initialized",
        level=DebugLevel.INFO
    )
    
    # Test state tracking
    tracer.update_agent_state(
        agent_id="main_interface_001",
        agent_type="MainInterfaceAgent",
        state_update={"status": "READY", "conversations": 1}
    )
    
    print("\n🔍 Debug system test completed!")
