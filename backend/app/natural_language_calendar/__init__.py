"""
Natural Language Calendar Workflow Package
Based on TLA+ validated specification: NaturalLanguageCalendarWorkflow.tla

This package implements a complete natural language driven calendar workflow
that integrates with the TLA+ verified tensor calendar and vector storage systems.

Core Workflow: "schedule a PCR for these samples" → full execution

Author: ALIMS Development Team  
Date: January 10, 2025
Status: TLA+ Validated Implementation
"""

from .workflow import (
    NaturalLanguageCalendarWorkflow,
    IntentParser,
    CalendarOrchestrator,
    ResponseGenerator
)

from .models import (
    NLRequest,
    ParsedIntent,
    CalendarOperation,
    StorageRequest,
    WorkflowResponse,
    IntentType,
    OperationType,
    OperationStatus,
    SystemState,
    ResponseStatus,
    SystemMetrics,
    ComponentStates,
    ScheduleData,
    WorkflowConfiguration
)

from .exceptions import (
    WorkflowConstraintError,
    CapacityExceededError,
    InvalidStateTransitionError,
    ProcessingConstraintError,
    StorageConsistencyError,
    RequestNotFoundError,
    DuplicateRequestError,
    InvalidIntentError,
    InvalidResourceError,
    InvalidUserError,
    OperationNotFoundError,
    PrerequisiteNotMetError,
    VectorStorageError,
    IntentParsingError,
    CalendarOperationError,
    ResponseGenerationError
)


__all__ = [
    # Main workflow class
    "NaturalLanguageCalendarWorkflow",
    
    # Component classes
    "IntentParser",
    "CalendarOrchestrator", 
    "ResponseGenerator",
    
    # Data models
    "NLRequest",
    "ParsedIntent",
    "CalendarOperation",
    "StorageRequest",
    "WorkflowResponse",
    "ScheduleData",
    "WorkflowConfiguration",
    "SystemMetrics",
    "ComponentStates",
    
    # Enums
    "IntentType",
    "OperationType",
    "OperationStatus",
    "SystemState",
    "ResponseStatus",
    
    # Exceptions
    "WorkflowConstraintError",
    "CapacityExceededError",
    "InvalidStateTransitionError",
    "ProcessingConstraintError",
    "StorageConsistencyError",
    "RequestNotFoundError",
    "DuplicateRequestError",
    "InvalidIntentError",
    "InvalidResourceError",
    "InvalidUserError",
    "OperationNotFoundError",
    "PrerequisiteNotMetError",
    "VectorStorageError",
    "IntentParsingError",
    "CalendarOperationError",
    "ResponseGenerationError"
]


# Version info
__version__ = "1.0.0"
__tla_validated__ = True
__specification__ = "NaturalLanguageCalendarWorkflow.tla"
__model_checker__ = "TLC 2.19"
__validation_date__ = "2025-01-10"


def create_workflow(config: dict) -> NaturalLanguageCalendarWorkflow:
    """
    Factory function to create a configured Natural Language Calendar Workflow
    
    Args:
        config: Configuration dictionary with workflow settings
        
    Returns:
        Configured NaturalLanguageCalendarWorkflow instance
        
    Example:
        >>> config = {
        ...     "max_requests": 100,
        ...     "users": ["alice", "bob", "charlie"],
        ...     "resources": ["microscope1", "pcr_machine1", "sequencer1"],
        ...     "vector_storage_config": {
        ...         "qdrant_url": "http://localhost:6333",
        ...         "collection_name": "alims_schedules"
        ...     }
        ... }
        >>> workflow = create_workflow(config)
        >>> await workflow.initialize()
    """
    return NaturalLanguageCalendarWorkflow(config)


async def process_scheduling_request(workflow: NaturalLanguageCalendarWorkflow,
                                   user: str, request: str) -> WorkflowResponse:
    """
    Convenience function to process a scheduling request
    
    Args:
        workflow: Initialized workflow instance
        user: User making the request
        request: Natural language request (e.g., "schedule a PCR for these samples")
        
    Returns:
        WorkflowResponse with the result
        
    Example:
        >>> response = await process_scheduling_request(
        ...     workflow, "alice", "schedule a PCR for samples A, B, C"
        ... )
        >>> print(response.message)
        "Successfully scheduled pcr_machine1 for alice"
    """
    return await workflow.process_natural_language_request(user, request)
