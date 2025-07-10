"""
Tensor Calendar System - TLA+ Verified Laboratory Scheduling

This module implements the formally verified Tensor Calendar System with comprehensive
fairness constraints and vector database storage for multi-dimensional laboratory scheduling.

Based on TLA+ specification: plans/feature-20250710-tensor-calendar-vector-storage/tla/TensorCalendarVectorStorageSimple.tla
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

__all__ = [
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
    "SystemStateError"
]

__version__ = "1.0.0"
__description__ = "TLA+ Verified Tensor Calendar System with Fairness Constraints"
