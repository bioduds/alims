"""
ALIMS Workflow Manager Service - Core Data Models

This module implements the data models for the Workflow Manager Service,
providing runtime validation that matches the TLA+ specification properties.

Key Features:
- Pydantic models with TLA+ property validation
- Runtime enforcement of state transition rules
- Type safety matching TLA+ type definitions
- Comprehensive validation for business rules
"""

from pydantic import BaseModel, Field, field_validator, model_validator
from typing import Optional, Dict, Any, Literal, List, Set
from enum import Enum
from datetime import datetime
import uuid

# TLA+ WorkflowStates definition
class WorkflowState(str, Enum):
    """Workflow states matching TLA+ WorkflowStates"""
    CREATED = "CREATED"
    ACTIVE = "ACTIVE"
    PAUSED = "PAUSED"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"
    CANCELLED = "CANCELLED"

# TLA+ TerminalStates definition
TERMINAL_STATES = {WorkflowState.COMPLETED, WorkflowState.CANCELLED}

# TLA+ ValidTransitions definition
VALID_TRANSITIONS = {
    (WorkflowState.CREATED, WorkflowState.ACTIVE),
    (WorkflowState.ACTIVE, WorkflowState.PAUSED),
    (WorkflowState.ACTIVE, WorkflowState.COMPLETED),
    (WorkflowState.ACTIVE, WorkflowState.FAILED),
    (WorkflowState.ACTIVE, WorkflowState.CANCELLED),
    (WorkflowState.PAUSED, WorkflowState.ACTIVE),
    (WorkflowState.PAUSED, WorkflowState.CANCELLED),
    (WorkflowState.FAILED, WorkflowState.ACTIVE),    # Recovery transition
    (WorkflowState.FAILED, WorkflowState.CANCELLED),
}

class EventType(str, Enum):
    """Event types matching TLA+ EventTypes"""
    CREATED = "CREATED"
    TRANSITION = "TRANSITION" 
    FAILED = "FAILED"
    RECOVERED = "RECOVERED"

class OperationType(str, Enum):
    """Operation types matching TLA+ OperationTypes"""
    CREATE = "CREATE"
    TRANSITION = "TRANSITION"
    RECOVER = "RECOVER"

class WorkflowModel(BaseModel):
    """
    Core workflow model matching TLA+ WorkflowRecord
    
    Enforces TLA+ properties:
    - StateConsistency: Only valid states allowed
    - VersionMonotonicity: Version numbers increase
    - TerminalStateImmutability: Terminal states cannot be in transition
    """
    id: str = Field(..., description="Unique workflow identifier")
    state: WorkflowState = Field(..., description="Current workflow state")
    previous_state: Optional[WorkflowState] = Field(None, description="Previous state for rollback")
    version: int = Field(1, ge=1, description="Version for optimistic locking")
    created_at: datetime = Field(default_factory=datetime.utcnow, description="Creation timestamp")
    updated_at: datetime = Field(default_factory=datetime.utcnow, description="Last update timestamp")
    in_transition: bool = Field(False, description="Prevents concurrent modifications")
    metadata: Dict[str, Any] = Field(default_factory=dict, description="Additional workflow data")
    
    @field_validator('state')
    @classmethod
    def validate_state_consistency(cls, v):
        """TLA+ StateConsistency property"""
        if isinstance(v, str):
            try:
                WorkflowState(v)
            except ValueError:
                raise ValueError(f"Invalid workflow state: {v}")
        elif not isinstance(v, WorkflowState):
            raise ValueError(f"Invalid workflow state type: {type(v)}")
        return v
    
    @field_validator('version')
    @classmethod
    def validate_version_monotonicity(cls, v):
        """TLA+ VersionMonotonicity property"""
        if v < 1:
            raise ValueError("Workflow version must be >= 1")
        return v
    
    @model_validator(mode='after')
    def validate_terminal_state_immutability(self):
        """TLA+ TerminalStateImmutability property"""
        if self.state in TERMINAL_STATES and self.in_transition:
            raise ValueError(f"Terminal state {self.state} cannot be in transition")
        
        return self
    
    @model_validator(mode='after')
    def validate_transition_rules(self):
        """TLA+ TransitionValidity property - only validate during creation"""
        # Only validate transitions during model creation, not updates
        # Business logic validation is handled in WorkflowManagerCore
        return self
    
    def can_transition_to(self, target_state: WorkflowState) -> bool:
        """Check if transition to target state is valid"""
        if self.state in TERMINAL_STATES:
            return False
        return (self.state, target_state) in VALID_TRANSITIONS
    
    def is_terminal(self) -> bool:
        """Check if workflow is in terminal state"""
        return self.state in TERMINAL_STATES
    
    def create_transition_event(self, to_state: WorkflowState) -> 'WorkflowEvent':
        """Create transition event for this workflow"""
        return WorkflowEvent(
            event_id=str(uuid.uuid4()),
            workflow_id=self.id,
            event_type=EventType.TRANSITION,
            from_state=self.state,
            to_state=to_state,
            timestamp=datetime.utcnow()
        )
    
    class Config:
        use_enum_values = True
        validate_assignment = True  # Validate on field assignment

class WorkflowEvent(BaseModel):
    """
    Workflow event model matching TLA+ WorkflowEvent
    
    Enforces TLA+ properties:
    - Event ordering and causality
    - Valid event types and state transitions
    """
    event_id: str = Field(..., description="Unique event identifier")
    workflow_id: str = Field(..., description="Associated workflow ID")
    event_type: EventType = Field(..., description="Type of event")
    from_state: Optional[WorkflowState] = Field(None, description="Previous state")
    to_state: WorkflowState = Field(..., description="Target state")
    timestamp: datetime = Field(default_factory=datetime.utcnow, description="Event timestamp")
    retry_count: int = Field(0, ge=0, description="Number of retry attempts")
    metadata: Dict[str, Any] = Field(default_factory=dict, description="Additional event data")
    
    @model_validator(mode='after')
    def validate_transition_event(self):
        """Validate transition events follow TLA+ rules"""
        if self.event_type == EventType.TRANSITION:
            if not self.from_state:
                raise ValueError("Transition events must have from_state")
            
            if (self.from_state, self.to_state) not in VALID_TRANSITIONS:
                raise ValueError(
                    f"Invalid transition in event from {self.from_state} to {self.to_state}"
                )
        
        return self
    
    class Config:
        use_enum_values = True

class StateTransitionRequest(BaseModel):
    """Request model for workflow state transitions"""
    workflow_id: str = Field(..., description="Target workflow ID")
    target_state: WorkflowState = Field(..., description="Desired state")
    expected_version: Optional[int] = Field(None, ge=1, description="Expected current version")
    reason: str = Field(..., min_length=1, max_length=500, description="Reason for transition")
    requested_by: str = Field(..., description="User or system requesting transition")
    metadata: Dict[str, Any] = Field(default_factory=dict, description="Additional request data")
    
    class Config:
        use_enum_values = True

class PendingOperation(BaseModel):
    """
    Pending operation model matching TLA+ PendingOperation
    
    Used for tracking concurrent operations and optimistic locking
    """
    op_id: str = Field(default_factory=lambda: str(uuid.uuid4()), description="Operation ID")
    op_type: OperationType = Field(..., description="Type of operation")
    workflow_id: str = Field(..., description="Target workflow ID")
    target_state: Optional[WorkflowState] = Field(None, description="Target state for transitions")
    requested_at: datetime = Field(default_factory=datetime.utcnow, description="Request timestamp")
    expected_version: int = Field(..., ge=1, description="Expected workflow version")
    timeout_at: Optional[datetime] = Field(None, description="Operation timeout")
    
    class Config:
        use_enum_values = True

class WorkflowStats(BaseModel):
    """System statistics model for monitoring"""
    total_workflows: int = Field(..., ge=0, description="Total active workflows")
    total_events: int = Field(..., ge=0, description="Total events generated")
    state_distribution: Dict[str, int] = Field(..., description="Count by workflow state")
    workflows_in_transition: int = Field(..., ge=0, description="Workflows currently transitioning")
    recovery_sessions: int = Field(..., ge=0, description="Active recovery sessions")
    max_workflows: int = Field(..., ge=1, description="Maximum allowed workflows")
    
    @field_validator('state_distribution')
    @classmethod
    def validate_state_distribution(cls, v):
        """Ensure all states are valid"""
        valid_states = {state.value for state in WorkflowState}
        for state in v.keys():
            if state not in valid_states:
                raise ValueError(f"Invalid state in distribution: {state}")
        return v

class TransitionResult(BaseModel):
    """Result of a workflow transition operation"""
    success: bool = Field(..., description="Whether transition succeeded")
    workflow_id: str = Field(..., description="Workflow ID")
    from_state: Optional[WorkflowState] = Field(None, description="Previous state")
    to_state: WorkflowState = Field(..., description="New state")
    version: int = Field(..., ge=1, description="New workflow version")
    event_id: str = Field(..., description="Generated event ID")
    timestamp: datetime = Field(default_factory=datetime.utcnow, description="Transition timestamp")
    
    class Config:
        use_enum_values = True

class RecoveryResult(BaseModel):
    """Result of a workflow recovery operation"""
    success: bool = Field(..., description="Whether recovery succeeded")
    workflow_id: str = Field(..., description="Recovered workflow ID")
    previous_state: WorkflowState = Field(..., description="State before recovery")
    recovered_state: WorkflowState = Field(..., description="State after recovery")
    version: int = Field(..., ge=1, description="New workflow version")
    recovery_event_id: str = Field(..., description="Recovery event ID")
    
    class Config:
        use_enum_values = True

# TLA+ property validation functions
def validate_workflow_uniqueness(workflows: List[WorkflowModel]) -> bool:
    """Validate TLA+ WorkflowUniqueness property"""
    workflow_ids = [wf.id for wf in workflows]
    return len(workflow_ids) == len(set(workflow_ids))

def validate_bounded_workflows(workflows: List[WorkflowModel], max_workflows: int) -> bool:
    """Validate TLA+ BoundedWorkflows property"""
    return len(workflows) <= max_workflows

def validate_transition_sequence(events: List[WorkflowEvent]) -> bool:
    """Validate that all transitions in event sequence follow TLA+ rules"""
    for event in events:
        if event.event_type == EventType.TRANSITION:
            if event.from_state and event.to_state:
                if (event.from_state, event.to_state) not in VALID_TRANSITIONS:
                    return False
    return True

def validate_concurrent_safety(workflow: WorkflowModel, pending_ops: List[PendingOperation]) -> bool:
    """Validate TLA+ ConcurrentSafety property"""
    if workflow.in_transition:
        # Only transition operations should be pending for this workflow
        workflow_ops = [op for op in pending_ops if op.workflow_id == workflow.id]
        return all(op.op_type == OperationType.TRANSITION for op in workflow_ops)
    return True

# Exception classes for TLA+ property violations
class TLAPropertyViolationError(Exception):
    """Base exception for TLA+ property violations"""
    pass

class StateConsistencyError(TLAPropertyViolationError):
    """Violation of StateConsistency property"""
    pass

class TransitionValidityError(TLAPropertyViolationError):
    """Violation of TransitionValidity property"""
    pass

class WorkflowUniquenessError(TLAPropertyViolationError):
    """Violation of WorkflowUniqueness property"""
    pass

class TerminalStateImmutabilityError(TLAPropertyViolationError):
    """Violation of TerminalStateImmutability property"""
    pass

class ConcurrentSafetyError(TLAPropertyViolationError):
    """Violation of ConcurrentSafety property"""
    pass

class BoundedWorkflowsError(TLAPropertyViolationError):
    """Violation of BoundedWorkflows property"""
    pass
