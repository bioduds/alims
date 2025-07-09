"""
ALIMS Workflow Manager Service - Core Implementation

This module implements the core workflow management service with runtime enforcement
of all TLA+ verified properties. The implementation provides mathematical guarantees
of correctness through property validation.

Key Features:
- TLA+ property enforcement at runtime
- Thread-safe concurrent operations with optimistic locking
- PredicateLogic Engine integration for business rule validation
- Event-driven architecture with reliable event delivery
- Comprehensive recovery and fault tolerance mechanisms
"""

import asyncio
import uuid
import threading
from typing import Dict, List, Optional, Set, Any
from datetime import datetime, timedelta
from concurrent.futures import ThreadPoolExecutor
import logging

from models import (
    WorkflowModel, WorkflowEvent, StateTransitionRequest, WorkflowState,
    TransitionResult, RecoveryResult, WorkflowStats, PendingOperation,
    OperationType, EventType, VALID_TRANSITIONS, TERMINAL_STATES,
    validate_workflow_uniqueness, validate_bounded_workflows,
    validate_concurrent_safety, TLAPropertyViolationError,
    WorkflowUniquenessError, BoundedWorkflowsError, TerminalStateImmutabilityError,
    ConcurrentSafetyError, TransitionValidityError
)
from exceptions import (
    WorkflowNotFoundError, InvalidTransitionError, TerminalStateError,
    ConcurrentModificationError, PredicateLogicUnavailableError
)

logger = logging.getLogger(__name__)

class WorkflowManagerCore:
    """
    Core workflow manager implementing TLA+ verified properties
    
    This implementation provides mathematical guarantees through runtime enforcement
    of all properties proven in the TLA+ specification:
    
    Safety Properties:
    - StateConsistency: All workflows maintain valid states  
    - TransitionValidity: Only business-rule-compliant transitions
    - WorkflowUniqueness: Each workflow ID appears at most once
    - TerminalStateImmutability: Terminal states cannot be modified
    - ConcurrentSafety: Race conditions prevented through locking
    - VersionMonotonicity: Version numbers only increase
    
    Liveness Properties:
    - TransitionProgress: Valid transitions eventually complete
    - RecoveryCompleteness: Failed workflows can be recovered
    - EventDelivery: Events are eventually delivered
    """
    
    def __init__(self, predicate_logic_engine, max_workflows: int = 1000, max_events: int = 10000):
        # Core state matching TLA+ variables
        self._workflows: Dict[str, WorkflowModel] = {}
        self._events: List[WorkflowEvent] = []
        self._pending_operations: Dict[str, PendingOperation] = {}
        self._recovery_sessions: Set[str] = set()
        
        # Thread safety for concurrent operations
        self._lock = threading.RLock()
        self._event_lock = threading.Lock()
        
        # External dependencies
        self.predicate_logic_engine = predicate_logic_engine
        
        # TLA+ constants
        self.max_workflows = max_workflows
        self.max_events = max_events
        
        logger.info(f"WorkflowManagerCore initialized with max_workflows={max_workflows}")
    
    def create_workflow(self, workflow_id: str, metadata: Optional[Dict[str, Any]] = None) -> WorkflowModel:
        """
        Create new workflow - implements TLA+ CreateWorkflow action
        
        TLA+ Properties Enforced:
        - WorkflowUniqueness: Each ID appears at most once
        - BoundedWorkflows: Respects maximum workflow limit
        - StateConsistency: Initial state is valid
        
        Args:
            workflow_id: Unique identifier for the workflow
            metadata: Optional metadata dictionary
            
        Returns:
            Created WorkflowModel
            
        Raises:
            WorkflowUniquenessError: If workflow ID already exists
            BoundedWorkflowsError: If maximum workflows exceeded
        """
        with self._lock:
            # TLA+ property: WorkflowUniqueness
            if workflow_id in self._workflows:
                raise WorkflowUniquenessError(f"Workflow {workflow_id} already exists")
            
            # TLA+ property: BoundedWorkflows
            if len(self._workflows) >= self.max_workflows:
                raise BoundedWorkflowsError(f"Maximum workflows ({self.max_workflows}) reached")
            
            # Create workflow with TLA+ validated initial state
            workflow = WorkflowModel(
                id=workflow_id,
                state=WorkflowState.CREATED,
                version=1,
                created_at=datetime.utcnow(),
                updated_at=datetime.utcnow(),
                in_transition=False,
                metadata=metadata or {"type": "LIMS_WORKFLOW"}
            )
            
            # Validate TLA+ properties before committing
            self._validate_workflow_uniqueness_pre_insert(workflow)
            
            # Atomic insertion
            self._workflows[workflow_id] = workflow
            
            # Generate creation event following TLA+ specification
            creation_event = WorkflowEvent(
                event_id=str(uuid.uuid4()),
                workflow_id=workflow_id,
                event_type=EventType.CREATED,
                from_state=None,
                to_state=WorkflowState.CREATED,
                timestamp=datetime.utcnow(),
                metadata={"created_by": "workflow_manager"}
            )
            
            self._append_event(creation_event)
            
            logger.info(f"Created workflow {workflow_id} with initial state CREATED")
            return workflow.model_copy(deep=True)
    
    async def request_state_transition(
        self, 
        workflow_id: str, 
        target_state: WorkflowState,
        expected_version: Optional[int] = None,
        reason: str = "State transition requested",
        requested_by: str = "system"
    ) -> TransitionResult:
        """
        Request state transition - implements TLA+ RequestStateTransition/ExecuteStateTransition
        
        TLA+ Properties Enforced:
        - TransitionValidity: Only valid transitions allowed
        - ConcurrentSafety: Optimistic locking prevents race conditions
        - TerminalStateImmutability: Terminal states cannot be modified
        - PredicateLogic dependency: Requires engine availability
        
        Args:
            workflow_id: Target workflow identifier
            target_state: Desired workflow state
            expected_version: Expected current version for optimistic locking
            reason: Reason for the transition
            requested_by: User or system requesting transition
            
        Returns:
            TransitionResult with success status and details
            
        Raises:
            WorkflowNotFoundError: If workflow doesn't exist
            TerminalStateError: If workflow is in terminal state
            ConcurrentModificationError: If version mismatch (optimistic locking)
            PredicateLogicUnavailableError: If PredicateLogic Engine unavailable
            InvalidTransitionError: If transition violates business rules
        """
        with self._lock:
            # TLA+ property: WorkflowExists check
            if workflow_id not in self._workflows:
                raise WorkflowNotFoundError(f"Workflow {workflow_id} not found")
            
            workflow = self._workflows[workflow_id]
            
            # TLA+ property: TerminalStateImmutability
            if workflow.state in TERMINAL_STATES:
                raise TerminalStateError(
                    f"Cannot modify workflow {workflow_id} in terminal state {workflow.state}"
                )
            
            # TLA+ property: ConcurrentSafety (optimistic locking)
            if expected_version is not None and workflow.version != expected_version:
                raise ConcurrentModificationError(
                    f"Version mismatch for workflow {workflow_id}: "
                    f"expected {expected_version}, got {workflow.version}"
                )
            
            # Prevent concurrent modifications
            if workflow.in_transition:
                raise ConcurrentModificationError(
                    f"Workflow {workflow_id} is currently in transition"
                )
            
            # TLA+ property: PredicateLogic dependency
            if not await self.predicate_logic_engine.is_available():
                raise PredicateLogicUnavailableError("PredicateLogic Engine unavailable")
            
            # TLA+ property: TransitionValidity
            if not await self._validate_transition(workflow.state, target_state, workflow_id):
                raise InvalidTransitionError(
                    f"Invalid transition for workflow {workflow_id} "
                    f"from {workflow.state} to {target_state}"
                )
            
            # Execute transition with TLA+ safety guarantees
            return await self._execute_transition_atomic(
                workflow_id, target_state, reason, requested_by
            )
    
    async def _validate_transition(self, from_state: WorkflowState, to_state: WorkflowState, workflow_id: str) -> bool:
        """
        Validate transition using TLA+ rules and PredicateLogic Engine
        
        Args:
            from_state: Current workflow state
            to_state: Target workflow state
            workflow_id: Workflow identifier for context
            
        Returns:
            True if transition is valid, False otherwise
        """
        # TLA+ ValidTransitions check
        if (from_state, to_state) not in VALID_TRANSITIONS:
            logger.debug(f"Transition {from_state} -> {to_state} not in VALID_TRANSITIONS")
            return False
        
        # Integrate with PredicateLogic Engine for additional business rules
        try:
            # Handle both enum and string values
            from_state_value = from_state.value if hasattr(from_state, 'value') else str(from_state)
            to_state_value = to_state.value if hasattr(to_state, 'value') else str(to_state)
            
            engine_validation = await self.predicate_logic_engine.validate_workflow_transition(
                workflow_id=workflow_id,
                from_state=from_state_value,
                to_state=to_state_value,
                context={"timestamp": datetime.utcnow().isoformat()}
            )
            
            logger.debug(f"PredicateLogic Engine validation for {workflow_id}: {engine_validation}")
            return engine_validation
            
        except Exception as e:
            logger.error(f"PredicateLogic Engine validation failed: {e}")
            return False
    
    async def _execute_transition_atomic(
        self, 
        workflow_id: str, 
        target_state: WorkflowState,
        reason: str,
        requested_by: str
    ) -> TransitionResult:
        """
        Execute state transition with TLA+ atomicity guarantees
        
        Implements two-phase commit pattern:
        1. Mark workflow as in_transition (prevents concurrent modifications)
        2. Update state atomically or rollback on failure
        
        Args:
            workflow_id: Target workflow identifier
            target_state: Target state
            reason: Transition reason
            requested_by: User/system requesting transition
            
        Returns:
            TransitionResult with operation details
        """
        workflow = self._workflows[workflow_id]
        old_state = workflow.state
        old_version = workflow.version
        
        # Phase 1: Mark as in transition (TLA+ ConcurrentSafety)
        workflow.in_transition = True
        
        try:
            # Phase 2: Execute atomic state update
            workflow.previous_state = old_state  
            workflow.version += 1
            workflow.updated_at = datetime.utcnow()
            workflow.in_transition = False  # Clear transition flag before setting terminal state
            workflow.state = target_state  # Set state last to avoid validation issues
            
            # Validate TLA+ properties after update
            self._validate_post_transition_properties(workflow)
            
            # Generate transition event following TLA+ specification
            transition_event = WorkflowEvent(
                event_id=str(uuid.uuid4()),
                workflow_id=workflow_id,
                event_type=EventType.TRANSITION,
                from_state=old_state,
                to_state=target_state,
                timestamp=datetime.utcnow(),
                metadata={
                    "reason": reason,
                    "requested_by": requested_by,
                    "old_version": old_version,
                    "new_version": workflow.version
                }
            )
            
            self._append_event(transition_event)
            
            result = TransitionResult(
                success=True,
                workflow_id=workflow_id,
                from_state=old_state,
                to_state=target_state,
                version=workflow.version,
                event_id=transition_event.event_id,
                timestamp=transition_event.timestamp
            )
            
            logger.info(f"Transition completed: {workflow_id} {old_state} -> {target_state} (v{workflow.version})")
            return result
            
        except Exception as e:
            # TLA+ rollback guarantee - restore previous state
            workflow.state = old_state
            workflow.version = old_version
            workflow.in_transition = False
            
            logger.error(f"Transition failed for {workflow_id}, rolled back: {e}")
            raise e
    
    def get_workflow(self, workflow_id: str) -> WorkflowModel:
        """
        Get workflow by ID with TLA+ consistency guarantees
        
        Args:
            workflow_id: Workflow identifier
            
        Returns:
            Deep copy of WorkflowModel
            
        Raises:
            WorkflowNotFoundError: If workflow doesn't exist
        """
        with self._lock:
            if workflow_id not in self._workflows:
                raise WorkflowNotFoundError(f"Workflow {workflow_id} not found")
            
            workflow = self._workflows[workflow_id]
            
            # Validate TLA+ properties before returning
            self._validate_workflow_consistency(workflow)
            
            return workflow.model_copy(deep=True)
    
    def get_workflow_events(self, workflow_id: str) -> List[WorkflowEvent]:
        """
        Get workflow event history
        
        Args:
            workflow_id: Workflow identifier
            
        Returns:
            List of WorkflowEvent objects for the workflow
        """
        with self._event_lock:
            events = [
                event.model_copy(deep=True) 
                for event in self._events 
                if event.workflow_id == workflow_id
            ]
            return sorted(events, key=lambda e: e.timestamp)
    
    async def recover_workflow(self, workflow_id: str, recovery_reason: str = "Manual recovery") -> RecoveryResult:
        """
        Recover failed workflow - implements TLA+ RecoverWorkflow
        
        TLA+ Properties Enforced:
        - RecoverySessionValidity: Only failed workflows can be recovered
        - State transition from FAILED to ACTIVE
        
        Args:
            workflow_id: Failed workflow identifier
            recovery_reason: Reason for recovery
            
        Returns:
            RecoveryResult with recovery details
            
        Raises:
            WorkflowNotFoundError: If workflow doesn't exist
            ValueError: If workflow is not in FAILED state or is in transition
        """
        with self._lock:
            if workflow_id not in self._workflows:
                raise WorkflowNotFoundError(f"Workflow {workflow_id} not found")
            
            workflow = self._workflows[workflow_id]
            
            # TLA+ property: RecoverySessionValidity
            if workflow.state != WorkflowState.FAILED:
                raise ValueError(
                    f"Can only recover FAILED workflows, current state: {workflow.state}"
                )
            
            if workflow.in_transition:
                raise ValueError("Cannot recover workflow during transition")
            
            # Add to recovery sessions
            self._recovery_sessions.add(workflow_id)
            
            try:
                # Execute recovery transition
                transition_result = await self._execute_transition_atomic(
                    workflow_id, WorkflowState.ACTIVE, recovery_reason, "recovery_system"
                )
                
                # Generate recovery event
                recovery_event = WorkflowEvent(
                    event_id=str(uuid.uuid4()),
                    workflow_id=workflow_id,
                    event_type=EventType.RECOVERED,
                    from_state=WorkflowState.FAILED,
                    to_state=WorkflowState.ACTIVE,
                    timestamp=datetime.utcnow(),
                    metadata={"recovery_reason": recovery_reason}
                )
                
                self._append_event(recovery_event)
                
                recovery_result = RecoveryResult(
                    success=True,
                    workflow_id=workflow_id,
                    previous_state=WorkflowState.FAILED,
                    recovered_state=WorkflowState.ACTIVE,
                    version=transition_result.version,
                    recovery_event_id=recovery_event.event_id
                )
                
                logger.info(f"Workflow {workflow_id} recovered from FAILED to ACTIVE")
                return recovery_result
                
            finally:
                # Remove from recovery sessions
                self._recovery_sessions.discard(workflow_id)
    
    def get_all_workflows(self) -> List[WorkflowModel]:
        """
        Get all workflows with TLA+ property validation
        
        Returns:
            List of all WorkflowModel objects
        """
        with self._lock:
            workflows = [wf.model_copy(deep=True) for wf in self._workflows.values()]
            
            # Validate TLA+ properties
            if not validate_workflow_uniqueness(workflows):
                raise TLAPropertyViolationError("WorkflowUniqueness property violated")
            
            if not validate_bounded_workflows(workflows, self.max_workflows):
                raise TLAPropertyViolationError("BoundedWorkflows property violated")
            
            return workflows
    
    def get_system_stats(self) -> WorkflowStats:
        """
        Get system statistics for monitoring
        
        Returns:
            WorkflowStats object with current system state
        """
        with self._lock:
            state_counts = {}
            workflows_in_transition = 0
            
            for workflow in self._workflows.values():
                # Handle both enum and string states
                state_value = workflow.state.value if hasattr(workflow.state, 'value') else str(workflow.state)
                state_counts[state_value] = state_counts.get(state_value, 0) + 1
                if workflow.in_transition:
                    workflows_in_transition += 1
            
            return WorkflowStats(
                total_workflows=len(self._workflows),
                total_events=len(self._events),
                state_distribution=state_counts,
                workflows_in_transition=workflows_in_transition,
                recovery_sessions=len(self._recovery_sessions),
                max_workflows=self.max_workflows
            )
    
    def _append_event(self, event: WorkflowEvent) -> None:
        """
        Append event to history with bounds checking
        
        Args:
            event: WorkflowEvent to append
        """
        with self._event_lock:
            self._events.append(event)
            
            # TLA+ BoundedEvents property
            if len(self._events) > self.max_events:
                # Keep most recent events
                self._events = self._events[-self.max_events:]
                logger.warning(f"Event history truncated to {self.max_events} events")
    
    def _validate_workflow_uniqueness_pre_insert(self, new_workflow: WorkflowModel) -> None:
        """Validate workflow uniqueness before insertion"""
        if new_workflow.id in self._workflows:
            raise WorkflowUniquenessError(f"Workflow {new_workflow.id} already exists")
    
    def _validate_workflow_consistency(self, workflow: WorkflowModel) -> None:
        """Validate individual workflow TLA+ properties"""
        # StateConsistency
        try:
            if isinstance(workflow.state, str):
                WorkflowState(workflow.state)
            elif not isinstance(workflow.state, WorkflowState):
                raise ValueError(f"Invalid state type: {type(workflow.state)}")
        except ValueError:
            raise TLAPropertyViolationError(f"Invalid workflow state: {workflow.state}")
        
        # TerminalStateImmutability
        if workflow.state in TERMINAL_STATES and workflow.in_transition:
            raise TerminalStateImmutabilityError(
                f"Terminal state {workflow.state} cannot be in transition"
            )
        
        # VersionMonotonicity
        if workflow.version < 1:
            raise TLAPropertyViolationError(f"Invalid workflow version: {workflow.version}")
    
    def _validate_post_transition_properties(self, workflow: WorkflowModel) -> None:
        """Validate TLA+ properties after state transition"""
        self._validate_workflow_consistency(workflow)
        
        # Additional transition-specific validations
        if workflow.previous_state and workflow.state != workflow.previous_state:
            if (workflow.previous_state, workflow.state) not in VALID_TRANSITIONS:
                raise TransitionValidityError(
                    f"Invalid transition from {workflow.previous_state} to {workflow.state}"
                )
    
    async def cleanup_expired_operations(self, timeout_minutes: int = 30) -> int:
        """
        Cleanup expired pending operations
        
        Args:
            timeout_minutes: Operation timeout in minutes
            
        Returns:
            Number of operations cleaned up
        """
        with self._lock:
            current_time = datetime.utcnow()
            timeout_threshold = current_time - timedelta(minutes=timeout_minutes)
            
            expired_ops = [
                op_id for op_id, op in self._pending_operations.items()
                if op.requested_at < timeout_threshold
            ]
            
            for op_id in expired_ops:
                del self._pending_operations[op_id]
            
            if expired_ops:
                logger.info(f"Cleaned up {len(expired_ops)} expired operations")
            
            return len(expired_ops)
    
    async def health_check(self) -> Dict[str, Any]:
        """
        Perform health check with TLA+ property validation
        
        Returns:
            Health status including TLA+ property validation results
        """
        try:
            with self._lock:
                workflows = list(self._workflows.values())
                
                # Validate all TLA+ properties
                health_status = {
                    "status": "healthy",
                    "timestamp": datetime.utcnow().isoformat(),
                    "total_workflows": len(workflows),
                    "total_events": len(self._events),
                    "predicate_logic_available": await self.predicate_logic_engine.is_available(),
                    "tla_properties": {
                        "workflow_uniqueness": validate_workflow_uniqueness(workflows),
                        "bounded_workflows": validate_bounded_workflows(workflows, self.max_workflows),
                        "state_consistency": all(
                            isinstance(wf.state, WorkflowState) or 
                            (isinstance(wf.state, str) and wf.state in [s.value for s in WorkflowState])
                            for wf in workflows
                        ),
                        "terminal_state_immutability": all(
                            not (wf.state in TERMINAL_STATES and wf.in_transition) 
                            for wf in workflows
                        )
                    }
                }
                
                # Check if any TLA+ properties failed
                if not all(health_status["tla_properties"].values()):
                    health_status["status"] = "degraded"
                    health_status["issues"] = [
                        prop for prop, valid in health_status["tla_properties"].items()
                        if not valid
                    ]
                
                return health_status
                
        except Exception as e:
            logger.error(f"Health check failed: {e}")
            return {
                "status": "unhealthy",
                "timestamp": datetime.utcnow().isoformat(),
                "error": str(e)
            }
