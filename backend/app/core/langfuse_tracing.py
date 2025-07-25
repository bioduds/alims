"""
Langfuse Tracing Integration for ALIMS
TLA+ Validated comprehensive tracing system

This module implements the formally verified Langfuse tracing integration
that follows the TLA+ specification LangfuseTracingIntegrationSimple.tla

Key properties verified by TLA+:
- Unique operation IDs (no conflicts)
- Proper state transitions (PENDING → SUCCESS/ERROR)
- Buffer management with auto-flush
- Connection state handling
- Resource bounds enforcement

Author: ALIMS Development Team
Date: July 21, 2025
TLA+ Validated: ✅
"""

import asyncio
import logging
import uuid
import time
import functools
import os
from datetime import datetime
from typing import Dict, Any, Optional, List, Callable, Union
from dataclasses import dataclass, field
from enum import Enum
import json
from contextlib import asynccontextmanager

# Load environment variables
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

try:
    from langfuse import Langfuse
    LANGFUSE_AVAILABLE = True
except ImportError:
    LANGFUSE_AVAILABLE = False
    Langfuse = None

logger = logging.getLogger(__name__)


class TraceLevel(str, Enum):
    """Trace levels matching TLA+ specification"""
    DEBUG = "DEBUG"
    INFO = "INFO"
    WARN = "WARN"
    ERROR = "ERROR"


class OperationType(str, Enum):
    """Operation types for tracing"""
    LLM = "LLM"              # Ollama/LLM calls
    API = "API"              # HTTP API calls
    AGENT = "AGENT"          # Agent conversations
    WORKFLOW = "WORKFLOW"    # LangGraph workflows
    DATABASE = "DATABASE"    # Database operations
    SYSTEM = "SYSTEM"        # System events


class TraceState(str, Enum):
    """Trace states matching TLA+ specification"""
    PENDING = "PENDING"
    SUCCESS = "SUCCESS" 
    ERROR = "ERROR"


@dataclass
class TraceRecord:
    """Trace record matching TLA+ specification"""
    id: str
    operation_type: OperationType
    level: TraceLevel
    timestamp: float
    duration: Optional[float] = None
    metadata: Dict[str, Any] = field(default_factory=dict)
    parent_trace_id: Optional[str] = None
    state: TraceState = TraceState.PENDING
    error_message: Optional[str] = None


class LangfuseTracker:
    """
    TLA+ Validated Langfuse tracing system
    
    Implements the validated specification for comprehensive ALIMS tracing.
    Ensures all operations are tracked with proper state management.
    """
    
    def __init__(self, 
                 max_buffer_size: int = 50,
                 max_traces: int = 1000,
                 auto_flush: bool = True,
                 enabled: bool = True):
        self.max_buffer_size = max_buffer_size
        self.max_traces = max_traces
        self.auto_flush = auto_flush
        self.enabled = enabled
        
        # TLA+ state variables
        self.traces: Dict[str, TraceRecord] = {}
        self.trace_buffer: List[TraceRecord] = []
        self.active_ops: set = set()
        self.langfuse_state = "DISCONNECTED"
        
        # Langfuse client
        self.langfuse_client: Optional[Langfuse] = None
        
        # Thread safety
        self._lock = asyncio.Lock()
        
        logger.info(f"LangfuseTracker initialized (enabled={enabled}, buffer_size={max_buffer_size})")
    
    async def initialize(self) -> bool:
        """Initialize Langfuse connection following TLA+ ConnectLangfuse action"""
        if not self.enabled or not LANGFUSE_AVAILABLE:
            logger.warning("Langfuse tracing disabled (not available or disabled)")
            return False
        
        # Check for required environment variables
        if not os.getenv('LANGFUSE_PUBLIC_KEY') or not os.getenv('LANGFUSE_SECRET_KEY'):
            logger.warning("Langfuse environment variables not found")
            return False
        
        try:
            self.langfuse_client = Langfuse()
            # Test connection
            await asyncio.get_event_loop().run_in_executor(None, self._test_connection)
            self.langfuse_state = "CONNECTED"
            logger.info("✅ Langfuse tracing enabled and connected")
            return True
            
        except Exception as e:
            self.langfuse_state = "ERROR"
            logger.error(f"❌ Failed to initialize Langfuse: {e}")
            return False
    
    def _test_connection(self):
        """Test Langfuse connection synchronously"""
        if self.langfuse_client:
            try:
                # Test auth with dataset check
                self.langfuse_client.get_dataset("test")
            except Exception as e:
                if "401" in str(e) or "Unauthorized" in str(e):
                    raise Exception("Langfuse authentication failed")
                # 404 is expected for non-existent dataset, means auth works
            
            # Create a simple test event
            self.langfuse_client.create_event(
                name="alims_trace_test",
                metadata={"source": "alims_initialization", "test": True}
            )
            self.langfuse_client.flush()
    
    async def start_trace(self, 
                         operation_type: OperationType,
                         name: str,
                         metadata: Optional[Dict[str, Any]] = None,
                         parent_trace_id: Optional[str] = None,
                         level: TraceLevel = TraceLevel.INFO) -> str:
        """
        Start tracing an operation - implements TLA+ StartTrace action
        
        Returns unique operation ID for correlation
        """
        if not self.enabled:
            return ""
        
        async with self._lock:
            # Generate unique operation ID (TLA+ requirement)
            op_id = f"{operation_type.value}_{int(time.time() * 1000000)}_{uuid.uuid4().hex[:8]}"
            
            # Verify uniqueness (TLA+ constraint)
            if op_id in self.traces or op_id in self.active_ops:
                logger.error(f"Duplicate operation ID detected: {op_id}")
                return ""
            
            # Check resource bounds (TLA+ constraint)
            if len(self.traces) >= self.max_traces:
                logger.warning("Maximum traces reached, skipping new trace")
                return ""
            
            # Create trace record
            trace = TraceRecord(
                id=op_id,
                operation_type=operation_type,
                level=level,
                timestamp=time.time(),
                metadata=metadata or {},
                parent_trace_id=parent_trace_id,
                state=TraceState.PENDING
            )
            
            # Update state (TLA+ state transition)
            self.traces[op_id] = trace
            self.active_ops.add(op_id)
            self.trace_buffer.append(trace)
            
            # Auto-flush if buffer full (TLA+ AutoFlush action)
            if self.auto_flush and len(self.trace_buffer) >= self.max_buffer_size:
                await self._flush_buffer()
            
            logger.debug(f"Started trace {op_id} for {operation_type.value}:{name}")
            return op_id
    
    async def complete_trace(self, 
                            op_id: str, 
                            result: Optional[Dict[str, Any]] = None,
                            duration: Optional[float] = None) -> bool:
        """Complete a trace successfully - implements TLA+ CompleteTrace action"""
        if not self.enabled or not op_id:
            return True
        
        async with self._lock:
            # Verify operation exists and is active (TLA+ constraint)
            if op_id not in self.active_ops or op_id not in self.traces:
                logger.warning(f"Attempting to complete non-existent trace: {op_id}")
                return False
            
            trace = self.traces[op_id]
            
            # Update trace state (TLA+ state transition)
            trace.state = TraceState.SUCCESS
            trace.duration = duration or (time.time() - trace.timestamp)
            if result:
                trace.metadata.update({"result": result})
            
            # Remove from active operations
            self.active_ops.discard(op_id)
            
            # Send to Langfuse if connected
            if self.langfuse_state == "CONNECTED":
                await self._send_to_langfuse(trace)
            
            logger.debug(f"Completed trace {op_id} (duration: {trace.duration:.3f}s)")
            return True
    
    async def fail_trace(self, 
                        op_id: str, 
                        error: Union[str, Exception],
                        duration: Optional[float] = None) -> bool:
        """Fail a trace with error - implements TLA+ FailTrace action"""
        if not self.enabled or not op_id:
            return True
        
        async with self._lock:
            # Verify operation exists and is active (TLA+ constraint)
            if op_id not in self.active_ops or op_id not in self.traces:
                logger.warning(f"Attempting to fail non-existent trace: {op_id}")
                return False
            
            trace = self.traces[op_id]
            
            # Update trace state (TLA+ state transition)
            trace.state = TraceState.ERROR
            trace.duration = duration or (time.time() - trace.timestamp)
            trace.error_message = str(error)
            trace.level = TraceLevel.ERROR
            
            # Remove from active operations
            self.active_ops.discard(op_id)
            
            # Send to Langfuse if connected
            if self.langfuse_state == "CONNECTED":
                await self._send_to_langfuse(trace)
            
            logger.debug(f"Failed trace {op_id}: {trace.error_message}")
            return True
    
    async def _flush_buffer(self) -> bool:
        """Flush trace buffer to Langfuse - implements TLA+ FlushBuffer action"""
        if self.langfuse_state != "CONNECTED" or not self.trace_buffer:
            return False
        
        try:
            # Send all buffered traces
            for trace in self.trace_buffer:
                await self._send_to_langfuse(trace)
            
            # Clear buffer (TLA+ state transition)
            self.trace_buffer.clear()
            logger.debug(f"Flushed trace buffer to Langfuse")
            return True
            
        except Exception as e:
            self.langfuse_state = "ERROR"  # TLA+ LangfuseError action
            logger.error(f"Failed to flush buffer: {e}")
            return False
    
    async def _send_to_langfuse(self, trace: TraceRecord):
        """Send individual trace to Langfuse"""
        if not self.langfuse_client:
            return
        
        try:
            # Run in executor to avoid blocking
            await asyncio.get_event_loop().run_in_executor(
                None, self._send_trace_sync, trace
            )
        except Exception as e:
            logger.error(f"Failed to send trace {trace.id}: {e}")
    
    def _send_trace_sync(self, trace: TraceRecord):
        """Send trace to Langfuse synchronously"""
        if not self.langfuse_client:
            return
        
        # Create Langfuse event (not trace - that's the correct API)
        self.langfuse_client.create_event(
            name=f"{trace.operation_type.value}_{trace.id[:8]}",
            metadata={
                **trace.metadata,
                "operation_type": trace.operation_type.value,
                "level": trace.level.value,
                "state": trace.state.value,
                "timestamp": trace.timestamp,
                "duration": trace.duration,
                "parent_trace_id": trace.parent_trace_id,
                "source": "ALIMS",
                "error_message": trace.error_message,
                "trace_id": trace.id
            }
        )
        
        # Flush to ensure delivery
        self.langfuse_client.flush()
    
    async def get_active_traces(self) -> List[str]:
        """Get list of active trace IDs"""
        async with self._lock:
            return list(self.active_ops)
    
    async def get_trace_stats(self) -> Dict[str, Any]:
        """Get tracing statistics"""
        async with self._lock:
            return {
                "total_traces": len(self.traces),
                "active_traces": len(self.active_ops),
                "buffer_size": len(self.trace_buffer),
                "langfuse_state": self.langfuse_state,
                "max_buffer_size": self.max_buffer_size,
                "max_traces": self.max_traces,
                "enabled": self.enabled
            }


# Global tracker instance
_tracker: Optional[LangfuseTracker] = None


async def get_tracker() -> LangfuseTracker:
    """Get global tracker instance"""
    global _tracker
    if _tracker is None:
        _tracker = LangfuseTracker()
        await _tracker.initialize()
    return _tracker


def trace_operation(operation_type: OperationType, 
                   name: Optional[str] = None,
                   level: TraceLevel = TraceLevel.INFO,
                   include_args: bool = False,
                   include_result: bool = True):
    """
    Decorator for automatic operation tracing
    
    Usage:
        @trace_operation(OperationType.LLM, "ollama_chat")
        async def chat_with_ollama(message: str):
            return await ollama_client.chat(message)
    """
    def decorator(func: Callable) -> Callable:
        @functools.wraps(func)
        async def async_wrapper(*args, **kwargs):
            tracker = await get_tracker()
            
            # Prepare metadata
            metadata = {
                "function": func.__name__,
                "module": func.__module__,
            }
            
            if include_args:
                metadata["args"] = str(args)[:500]  # Limit size
                metadata["kwargs"] = {k: str(v)[:500] for k, v in kwargs.items()}
            
            # Start trace
            trace_id = await tracker.start_trace(
                operation_type=operation_type,
                name=name or func.__name__,
                metadata=metadata,
                level=level
            )
            
            try:
                # Execute function
                result = await func(*args, **kwargs)
                
                # Complete trace with result
                result_metadata = {"result": str(result)[:500]} if include_result else {}
                await tracker.complete_trace(trace_id, result_metadata)
                
                return result
                
            except Exception as e:
                # Fail trace with error
                await tracker.fail_trace(trace_id, e)
                raise
        
        @functools.wraps(func)
        def sync_wrapper(*args, **kwargs):
            # For sync functions, run in async context
            return asyncio.create_task(async_wrapper(*args, **kwargs))
        
        # Return appropriate wrapper based on function type
        return async_wrapper if asyncio.iscoroutinefunction(func) else sync_wrapper
    
    return decorator


@asynccontextmanager
async def trace_context(operation_type: OperationType, 
                       name: str,
                       metadata: Optional[Dict[str, Any]] = None,
                       level: TraceLevel = TraceLevel.INFO):
    """
    Context manager for manual tracing
    
    Usage:
        async with trace_context(OperationType.WORKFLOW, "sample_processing") as trace_id:
            # Your operation here
            await process_sample()
    """
    tracker = await get_tracker()
    trace_id = await tracker.start_trace(
        operation_type=operation_type,
        name=name,
        metadata=metadata,
        level=level
    )
    
    try:
        yield trace_id
        await tracker.complete_trace(trace_id)
    except Exception as e:
        await tracker.fail_trace(trace_id, e)
        raise
