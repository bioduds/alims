"""
Exceptions for Natural Language Calendar Workflow
Based on TLA+ validated specification constraints

These exceptions ensure the implementation maintains TLA+ proven invariants.
"""


class WorkflowConstraintError(Exception):
    """
    Base exception for TLA+ constraint violations
    
    Raised when an operation would violate a TLA+ validated invariant:
    - SystemCapacityInvariant
    - StateConsistencyInvariant  
    - ProcessingInvariant
    - StorageConsistencyInvariant
    """
    pass


class CapacityExceededError(WorkflowConstraintError):
    """
    Raised when SystemCapacityInvariant would be violated
    
    TLA+ Constraint:
    - Cardinality(nl_requests) <= MAX_REQUESTS
    - Cardinality(DOMAIN parsed_intents) <= MAX_PARSED_INTENTS
    - Cardinality(calendar_operations) <= MAX_CALENDAR_OPS
    - Cardinality(storage_requests) <= MAX_STORAGE_OPS
    """
    def __init__(self, component: str, current: int, maximum: int):
        self.component = component
        self.current = current
        self.maximum = maximum
        super().__init__(
            f"Maximum {component} capacity exceeded: {current}/{maximum}"
        )


class InvalidStateTransitionError(WorkflowConstraintError):
    """
    Raised when StateConsistencyInvariant would be violated
    
    TLA+ Constraint:
    - intent_parser_state ∈ {"IDLE", "PARSING", "ERROR"}
    - orchestrator_state ∈ {"READY", "ORCHESTRATING", "ERROR"}
    - vector_storage_state ∈ {"AVAILABLE", "BUSY", "ERROR"}
    - response_generator_state ∈ {"IDLE", "GENERATING", "ERROR"}
    """
    def __init__(self, component: str, current_state: str, attempted_state: str):
        self.component = component
        self.current_state = current_state
        self.attempted_state = attempted_state
        super().__init__(
            f"Invalid state transition for {component}: {current_state} -> {attempted_state}"
        )


class ProcessingConstraintError(WorkflowConstraintError):
    """
    Raised when ProcessingInvariant would be violated
    
    TLA+ Constraint:
    - total_processed >= 0
    - successful_schedules >= 0  
    - failed_operations >= 0
    """
    def __init__(self, metric: str, value: int):
        self.metric = metric
        self.value = value
        super().__init__(
            f"Processing constraint violated: {metric} cannot be negative (value: {value})"
        )


class StorageConsistencyError(WorkflowConstraintError):
    """
    Raised when StorageConsistencyInvariant would be violated
    
    TLA+ Constraint:
    ∀ schedule_id ∈ stored_schedules:
      ∃ op ∈ calendar_operations:
        ∧ op.id = schedule_id
        ∧ op.status = "COMPLETED"
    """
    def __init__(self, schedule_id: int, reason: str):
        self.schedule_id = schedule_id
        self.reason = reason
        super().__init__(
            f"Storage consistency violated for schedule {schedule_id}: {reason}"
        )


class RequestNotFoundError(WorkflowConstraintError):
    """
    Raised when attempting to operate on non-existent request
    
    TLA+ Constraint: Operations must be performed on valid request_ids
    """
    def __init__(self, request_id: int, operation: str):
        self.request_id = request_id
        self.operation = operation
        super().__init__(
            f"Request {request_id} not found for operation: {operation}"
        )


class DuplicateRequestError(WorkflowConstraintError):
    """
    Raised when attempting to create duplicate request
    
    TLA+ Constraint: request_id ∉ nl_requests for ReceiveNLRequest
    """
    def __init__(self, request_id: int):
        self.request_id = request_id
        super().__init__(
            f"Request {request_id} already exists"
        )


class InvalidIntentError(WorkflowConstraintError):
    """
    Raised when parsed intent is invalid
    
    TLA+ Constraint: Intent types must be from INTENT_TYPES
    """
    def __init__(self, intent_type: str, valid_types: list):
        self.intent_type = intent_type
        self.valid_types = valid_types
        super().__init__(
            f"Invalid intent type '{intent_type}'. Valid types: {valid_types}"
        )


class InvalidResourceError(WorkflowConstraintError):
    """
    Raised when referenced resource is invalid
    
    TLA+ Constraint: Resources must be from RESOURCES
    """
    def __init__(self, resource: str, valid_resources: list):
        self.resource = resource
        self.valid_resources = valid_resources
        super().__init__(
            f"Invalid resource '{resource}'. Valid resources: {valid_resources}"
        )


class InvalidUserError(WorkflowConstraintError):
    """
    Raised when referenced user is invalid
    
    TLA+ Constraint: Users must be from USERS
    """
    def __init__(self, user: str, valid_users: list):
        self.user = user
        self.valid_users = valid_users
        super().__init__(
            f"Invalid user '{user}'. Valid users: {valid_users}"
        )


class OperationNotFoundError(WorkflowConstraintError):
    """
    Raised when attempting to operate on non-existent operation
    """
    def __init__(self, operation_id: int, operation_type: str):
        self.operation_id = operation_id
        self.operation_type = operation_type
        super().__init__(
            f"{operation_type} operation {operation_id} not found"
        )


class PrerequisiteNotMetError(WorkflowConstraintError):
    """
    Raised when operation prerequisites are not met
    
    TLA+ Constraint: Operations must follow valid state transitions
    """
    def __init__(self, operation: str, missing_prerequisite: str):
        self.operation = operation
        self.missing_prerequisite = missing_prerequisite
        super().__init__(
            f"Cannot perform {operation}: missing prerequisite {missing_prerequisite}"
        )


class ConfigurationError(WorkflowConstraintError):
    """
    Raised when configuration violates TLA+ constraints
    """
    def __init__(self, parameter: str, value: any, constraint: str):
        self.parameter = parameter
        self.value = value
        self.constraint = constraint
        super().__init__(
            f"Configuration error: {parameter}={value} violates constraint {constraint}"
        )


class TemporalPropertyViolationError(WorkflowConstraintError):
    """
    Raised when a temporal property might be violated
    
    TLA+ Properties:
    - EventuallyProcessed: All requests eventually get responses
    - SystemAvailability: System eventually returns to ready state
    - ProgressProperty: System can make progress
    """
    def __init__(self, property_name: str, description: str):
        self.property_name = property_name
        self.description = description
        super().__init__(
            f"Temporal property {property_name} may be violated: {description}"
        )


class VectorStorageError(WorkflowConstraintError):
    """
    Raised when vector storage operations fail
    
    Ensures integration with TLA+ verified tensor calendar vector storage
    """
    def __init__(self, operation: str, error_message: str):
        self.operation = operation
        self.error_message = error_message
        super().__init__(
            f"Vector storage {operation} failed: {error_message}"
        )


class IntentParsingError(WorkflowConstraintError):
    """
    Raised when natural language intent parsing fails
    """
    def __init__(self, content: str, error_details: str):
        self.content = content
        self.error_details = error_details
        super().__init__(
            f"Failed to parse intent from '{content}': {error_details}"
        )


class CalendarOperationError(WorkflowConstraintError):
    """
    Raised when calendar operations fail
    """
    def __init__(self, operation_type: str, resource: str, error_details: str):
        self.operation_type = operation_type
        self.resource = resource
        self.error_details = error_details
        super().__init__(
            f"Calendar {operation_type} failed for {resource}: {error_details}"
        )


class ResponseGenerationError(WorkflowConstraintError):
    """
    Raised when response generation fails
    """
    def __init__(self, request_id: int, error_details: str):
        self.request_id = request_id
        self.error_details = error_details
        super().__init__(
            f"Failed to generate response for request {request_id}: {error_details}"
        )


# Exception mappings for TLA+ constraint validation
TLA_CONSTRAINT_EXCEPTIONS = {
    "SystemCapacityInvariant": CapacityExceededError,
    "StateConsistencyInvariant": InvalidStateTransitionError,
    "ProcessingInvariant": ProcessingConstraintError,
    "StorageConsistencyInvariant": StorageConsistencyError,
    "EventuallyProcessed": TemporalPropertyViolationError,
    "SystemAvailability": TemporalPropertyViolationError,
    "ProgressProperty": TemporalPropertyViolationError
}
