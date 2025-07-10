"""
Tensor Calendar System - TLA+ Verified Laboratory Scheduling

This module implements the formally verified Tensor Calendar System with comprehensive
fairness constraints and vector database storage for multi-dimensional laboratory scheduling.

Based on TLA+ specification: plans/feature-20250710-tensor-calendar-vector-storage/tla/TensorCalendarVectorStorageSimple.tla

ENHANCED WITH: Unified Memory Tensor System - Revolutionary 4D Memory Architecture
"""

from .vector_storage import VectorTensorStorage
from .models import (
    TensorCalendar,
    Sample,
    Resource,
    Workflow,
    Schedule,
    CalendarEvent,
    SystemMetrics
)
from .exceptions import (
    TensorConstraintError,
    TensorNotFoundError,
    TensorAlreadyExistsError,
    InvalidEmbeddingError,
    StorageCapacityError,
    VectorDatabaseError,
    SystemStateError
)

# UNIFIED MEMORY TENSOR SYSTEM - Revolutionary 4D Memory Architecture
from .memory_system import (
    MemoryTensorSystem,
    get_memory_system,
    shutdown_memory_system,
    ConversationMemoryContext,
    WorkflowMemoryContext
)

from .memory_models import (
    UnifiedMemory,
    MemoryType,
    MemoryScope,
    ModalityType,
    TemporalContext,
    SemanticContext,
    ConversationalContext,
    WorkflowContext,
    MemoryQuery,
    MemorySearchResult,
    MemoryInsight,
    MemoryTensorConfiguration
)

from .unified_memory_tensor import (
    UnifiedMemoryTensorEngine
)

__all__ = [
    # Tensor Calendar System
    "VectorTensorStorage",
    "TensorCalendar",
    "Sample",
    "Resource", 
    "Workflow",
    "Schedule",
    "CalendarEvent",
    "SystemMetrics",
    "TensorConstraintError",
    "TensorNotFoundError",
    "TensorAlreadyExistsError",
    "InvalidEmbeddingError",
    "StorageCapacityError",
    "VectorDatabaseError",
    "SystemStateError",

    # Unified Memory Tensor System - Revolutionary 4D Memory Architecture
    "MemoryTensorSystem",
    "get_memory_system",
    "shutdown_memory_system",
    "ConversationMemoryContext",
    "WorkflowMemoryContext",
    "UnifiedMemory",
    "MemoryType",
    "MemoryScope",
    "ModalityType",
    "TemporalContext",
    "SemanticContext",
    "ConversationalContext",
    "WorkflowContext",
    "MemoryQuery",
    "MemorySearchResult",
    "MemoryInsight",
    "MemoryTensorConfiguration",
    "UnifiedMemoryTensorEngine"
]

__version__ = "2.0.0"  # Updated for Unified Memory Tensor integration
__description__ = "TLA+ Verified Tensor Calendar + Revolutionary 4D Memory Architecture"

# TLA+ validation status
__tla_validated__ = True
__tensor_calendar_tla__ = "TensorCalendarVectorStorageSimple.tla v1.0"
__memory_tensor_tla__ = "UnifiedMemoryTensor.tla v1.0"

# Revolutionary Memory System Info
__memory_architecture__ = "4D: Semantic × Temporal × Contextual × Modal"
__memory_capabilities__ = [
    "Natural language memory queries",
    "Perfect conversation continuity",
    "Automatic relationship discovery",
    "Temporal pattern recognition",
    "Cross-modal content search",
    "Real-time system health monitoring"
]
