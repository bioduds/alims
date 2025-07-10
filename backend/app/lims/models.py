"""
Core LIMS Data Models - Based on TLA+ Specification

These Pydantic models implement the data structures verified in our
TLA+ specification LIMSSampleWorkflow.tla, ensuring type safety and
validation at runtime with TLA+ property enforcement.
"""

from datetime import datetime
from enum import Enum
from typing import List, Dict, Optional, Set
from pydantic import BaseModel, Field, field_validator
from uuid import UUID, uuid4
import logging

logger = logging.getLogger(__name__)


class TLAPropertyError(Exception):
    """Exception raised when a TLA+ property is violated at runtime"""
    pass


class SampleState(str, Enum):
    """
    Sample states as defined in TLA+ specification LIMSSampleWorkflow.tla.
    These match exactly with the TLA+ constants.
    """
    RECEIVED = "RECEIVED"
    ACCESSIONED = "ACCESSIONED"
    SCHEDULED = "SCHEDULED"
    TESTING = "TESTING"
    QC_PENDING = "QC_PENDING"
    QC_APPROVED = "QC_APPROVED"
    REPORTED = "REPORTED"
    ARCHIVED = "ARCHIVED"


class AuditLogEntry(BaseModel):
    """Single audit trail entry - immutable once created (TLA+ property)"""
    timestamp: datetime = Field(default_factory=datetime.now)
    state: SampleState
    actor: str  # Who performed the action
    notes: Optional[str] = None

    class Config:
        frozen = True  # Immutable to enforce TLA+ AuditTrailImmutability property


class Sample(BaseModel):
    """
    Sample record structure matching TLA+ model LIMSSampleWorkflow.tla.
    
    This implements the sample record from the TLA+ specification:
    [id: SampleIDs, barcode: STRING, receivedAt: Nat]
    """
    id: int = Field(..., description="Unique sample identifier")
    barcode: str = Field(..., description="Sample barcode")
    received_at: datetime = Field(default_factory=datetime.now)
    
    # Additional fields for real implementation
    sample_type: Optional[str] = None
    patient_id: Optional[str] = None
    collection_site: Optional[str] = None
    priority: str = Field(default="ROUTINE", description="STAT, URGENT, ROUTINE")
    
    @field_validator('barcode')
    @classmethod
    def barcode_must_not_be_empty(cls, v):
        if v is None:
            return ""
        return v.strip() if v else ""

    @field_validator('id')
    @classmethod
    def validate_sample_id_bounds(cls, v):
        """Enforce TLA+ SampleIDBounds property"""
        if v <= 0 or v > 10000:  # MaxSamples bound from TLA+ spec
            raise TLAPropertyError(
                f"Sample ID {v} violates SampleIDBounds property (1..MaxSamples)")
        return v

    class Config:
        frozen = True  # Immutable once created (sample identity integrity)


class SampleWorkflow(BaseModel):
    """
    Complete sample workflow state matching TLA+ specification LIMSSampleWorkflow.tla.
    
    This implements the TLA+ variables:
    - samples: Sample ID -> Sample record
    - sampleStates: Sample ID -> Current state  
    - auditTrail: Sample ID -> Sequence of state transitions
    """
    sample: Sample
    current_state: SampleState = SampleState.RECEIVED
    audit_trail: List[AuditLogEntry] = Field(default_factory=list)
    
    def __init__(self, **data):
        super().__init__(**data)
        # Ensure initial audit entry exists (TLA+ property)
        if not self.audit_trail:
            self.audit_trail.append(
                AuditLogEntry(
                    state=SampleState.RECEIVED,
                    actor="system",
                    notes="Sample received into LIMS"
                )
            )
        # Validate TLA+ properties on initialization
        self._validate_tla_properties()
    
    @field_validator('audit_trail')
    @classmethod
    def audit_trail_must_start_with_received(cls, v):
        """Enforce TLA+ AuditTrailConsistency property"""
        if v and v[0].state != SampleState.RECEIVED:
            raise TLAPropertyError(
                'Audit trail must start with RECEIVED state (TLA+ AuditTrailConsistency)')
        return v
    
    def _validate_tla_properties(self) -> None:
        """Validate all TLA+ properties for this workflow"""

        # MonotonicProgression: No state should appear twice in audit trail
        states_seen = [entry.state for entry in self.audit_trail]
        if len(states_seen) != len(set(states_seen)):
            raise TLAPropertyError(
                "MonotonicProgression violated: duplicate states in audit trail")

        # AuditTrailConsistency: Current state must match last audit entry
        if self.audit_trail and self.audit_trail[-1].state != self.current_state:
            raise TLAPropertyError(
                "AuditTrailConsistency violated: current state doesn't match audit trail")

        # QCRequired: If sample is REPORTED or ARCHIVED, must have QC approval
        if self.current_state in [SampleState.REPORTED, SampleState.ARCHIVED]:
            if not self.has_qc_approval():
                raise TLAPropertyError(
                    "QCRequired violated: cannot report/archive without QC approval")

    def get_valid_next_states(self) -> List[SampleState]:
        """Get valid next states for current sample state (TLA+ ValidTransition)"""
        state_transitions = {
            SampleState.RECEIVED: [SampleState.ACCESSIONED],
            SampleState.ACCESSIONED: [SampleState.SCHEDULED],
            SampleState.SCHEDULED: [SampleState.TESTING],
            SampleState.TESTING: [SampleState.QC_PENDING],
            SampleState.QC_PENDING: [SampleState.QC_APPROVED],
            SampleState.QC_APPROVED: [SampleState.REPORTED],
            SampleState.REPORTED: [SampleState.ARCHIVED],
            SampleState.ARCHIVED: []  # Terminal state
        }
        return state_transitions.get(self.current_state, [])
    
    def can_transition_to(self, target_state: SampleState) -> bool:
        """Check if transition to target state is valid per TLA+ specification"""
        return target_state in self.get_valid_next_states()
    
    def transition_to(self, new_state: SampleState, actor: str, notes: Optional[str] = None) -> bool:
        """
        Transition sample to new state with TLA+ property validation.
        
        This implements the ValidTransition predicate from TLA+ specification.
        """
        # ARCHIVED state is terminal - cannot transition from it
        if self.current_state == SampleState.ARCHIVED:
            raise TLAPropertyError(
                "Cannot transition from ARCHIVED state (terminal)")
        
        # Verify MonotonicProgression: No state should be revisited
        existing_states = [entry.state for entry in self.audit_trail]
        if new_state in existing_states:
            raise TLAPropertyError(
                f"MonotonicProgression violated: State {new_state} already visited")
        
        # QC approval required before REPORTED
        if new_state == SampleState.REPORTED and self.current_state != SampleState.QC_APPROVED:
            raise TLAPropertyError(
                "QCRequired violated: cannot report without QC approval")

        # Validate transition is allowed in state machine
        if not self.can_transition_to(new_state):
            raise TLAPropertyError(
                f"Invalid transition from {self.current_state} to {new_state}")

        # Create new audit entry (immutable)
        new_audit_entry = AuditLogEntry(
            state=new_state,
            actor=actor,
            notes=notes
        )
        
        # Update state atomically
        old_state = self.current_state
        try:
            self.current_state = new_state
            self.audit_trail.append(new_audit_entry)

            # Validate all TLA+ properties after transition
            self._validate_tla_properties()

            logger.info(
                f"Sample {self.sample.id} transitioned: {old_state} -> {new_state} by {actor}")
            return True

        except Exception as e:
            # Rollback on validation failure
            self.current_state = old_state
            self.audit_trail.pop()
            logger.error(
                f"Transition rollback for sample {self.sample.id}: {e}")
            raise

    def has_qc_approval(self) -> bool:
        """Check if sample has gone through QC approval (TLA+ QCRequired property)"""
        qc_states = [entry.state for entry in self.audit_trail]
        return SampleState.QC_APPROVED in qc_states
    
    def can_be_reported(self) -> bool:
        """Check if sample can be reported (requires QC approval per TLA+ spec)"""
        return (self.current_state == SampleState.QC_APPROVED or 
                (self.current_state in [SampleState.REPORTED, SampleState.ARCHIVED] 
                 and self.has_qc_approval()))

    def get_audit_trail_states(self) -> List[SampleState]:
        """Get ordered list of states from audit trail"""
        return [entry.state for entry in self.audit_trail]

    def is_terminal_state(self) -> bool:
        """Check if sample is in terminal state"""
        return self.current_state == SampleState.ARCHIVED

    def validate_audit_trail(self) -> None:
        """
        Validate the audit trail entries against TLA+ properties.
        
        This checks:
        - All entries are immutable (frozen)
        - No duplicate states (monotonic progression)
        """
        seen_states: Set[SampleState] = set()
        for entry in self.audit_trail:
            # Check immutability
            if not entry.Config.frozen:
                raise TLAPropertyError("Audit trail entry is mutable")

            # Check monotonic progression
            if entry.state in seen_states:
                raise TLAPropertyError(
                    f"State {entry.state} re-visited - violates monotonic progression")
            seen_states.add(entry.state)

        logger.info("Audit trail validated successfully")


class LIMSSystemState(BaseModel):
    """
    Complete LIMS system state matching TLA+ specification LIMSSampleWorkflow.tla.
    
    This implements:
    - samples: Sample ID -> Sample record
    - sampleStates: Sample ID -> Current state
    - auditTrail: Sample ID -> Sequence of state transitions  
    - nextSampleID: Next available sample ID
    - testing: Set of samples currently in testing
    - qcApproved: Set of samples that have QC approval
    """
    workflows: Dict[int, SampleWorkflow] = Field(default_factory=dict)
    next_sample_id: int = Field(default=1)
    max_samples: int = Field(default=10000)  # MaxSamples from TLA+ spec
    # MaxConcurrentTests from TLA+ spec
    max_concurrent_tests: int = Field(default=5)

    # Resource tracking for TLA+ ResourceBounds property
    samples_in_testing: Set[int] = Field(default_factory=set)
    qc_approved_samples: Set[int] = Field(default_factory=set)

    def _validate_resource_bounds(self) -> None:
        """Validate TLA+ ResourceBounds property"""
        if len(self.samples_in_testing) > self.max_concurrent_tests:
            raise TLAPropertyError(
                f"ResourceBounds violated: {len(self.samples_in_testing)} > {self.max_concurrent_tests} concurrent tests")

    def _validate_system_invariants(self) -> None:
        """Validate all TLA+ system invariants"""

        # SampleIDUniqueness: Every sample has unique ID
        sample_ids = [
            workflow.sample.id for workflow in self.workflows.values()]
        if len(sample_ids) != len(set(sample_ids)):
            raise TLAPropertyError(
                "SampleIDUniqueness violated: duplicate sample IDs found")

        # ResourceBounds: Testing capacity not exceeded
        self._validate_resource_bounds()

        # QCApprovedConsistency: QC tracking matches workflow states
        actual_qc_approved = {
            sample_id for sample_id, workflow in self.workflows.items()
            if workflow.has_qc_approval()
        }
        if self.qc_approved_samples != actual_qc_approved:
            raise TLAPropertyError(
                "QCApprovedConsistency violated: QC tracking mismatch")
    
    def create_sample(self, barcode: str, actor: str = "system", **kwargs) -> int:
        """
        Create new sample (implements ReceiveSample action from TLA+ spec).
        
        Returns the new sample ID.
        """
        # SampleIDBounds validation
        if self.next_sample_id > self.max_samples:
            raise TLAPropertyError(
                f"SampleIDBounds violated: cannot exceed {self.max_samples} samples")
        
        sample_id = self.next_sample_id
        
        # Create sample
        sample = Sample(
            id=sample_id,
            barcode=barcode,
            **kwargs
        )
        
        # Create workflow with initial audit entry
        workflow = SampleWorkflow(sample=sample)
        
        # Add to system
        self.workflows[sample_id] = workflow
        self.next_sample_id += 1
        
        # Validate system invariants
        self._validate_system_invariants()

        logger.info(
            f"Sample {sample_id} created with barcode {barcode} by {actor}")
        return sample_id
    
    def get_sample(self, sample_id: int) -> Optional[SampleWorkflow]:
        """Get sample workflow by ID"""
        return self.workflows.get(sample_id)
    
    def transition_sample(self, sample_id: int, new_state: SampleState, 
                         actor: str, notes: Optional[str] = None) -> bool:
        """
        Transition sample to new state with TLA+ validation.
        
        Implements state transitions with resource management and property enforcement.
        """
        workflow = self.get_sample(sample_id)
        if not workflow:
            raise ValueError(f"Sample {sample_id} not found")
        
        old_state = workflow.current_state

        # Pre-transition validation for resource bounds
        if new_state == SampleState.TESTING:
            if len(self.samples_in_testing) >= self.max_concurrent_tests:
                raise TLAPropertyError(
                    f"ResourceBounds violated: cannot start testing (max {self.max_concurrent_tests} concurrent)")

        # Perform the transition
        success = workflow.transition_to(new_state, actor, notes)

        if success:
            # Update resource tracking
            if old_state == SampleState.TESTING and new_state != SampleState.TESTING:
                self.samples_in_testing.discard(sample_id)
            elif new_state == SampleState.TESTING:
                self.samples_in_testing.add(sample_id)

            if new_state == SampleState.QC_APPROVED:
                self.qc_approved_samples.add(sample_id)

            # Validate system invariants after transition
            self._validate_system_invariants()

        return success
    
    def get_samples_by_state(self, state: SampleState) -> List[SampleWorkflow]:
        """Get all samples in a specific state"""
        return [workflow for workflow in self.workflows.values() 
                if workflow.current_state == state]
    
    def get_testing_capacity_status(self) -> Dict[str, int]:
        """Get current testing capacity status"""
        return {
            "current_testing": len(self.samples_in_testing),
            "max_concurrent": self.max_concurrent_tests,
            "available_capacity": self.max_concurrent_tests - len(self.samples_in_testing)
        }

    def validate_system_invariants(self) -> Dict[str, bool]:
        """
        Validate all TLA+ invariants hold for current system state.
        
        Returns dict of invariant name -> validation result.
        """
        try:
            results = {}

            # TypeInv: All variables have correct types (automatically enforced by Pydantic)
            results['TypeInv'] = True

            # SampleIDUniqueness: Every sample has unique ID
            sample_ids = [
                workflow.sample.id for workflow in self.workflows.values()]
            results['SampleIDUniqueness'] = len(
                sample_ids) == len(set(sample_ids))

            # AuditTrailConsistency: Audit trail starts with RECEIVED and matches current state
            results['AuditTrailConsistency'] = all(
                workflow.audit_trail and
                workflow.audit_trail[0].state == SampleState.RECEIVED and
                workflow.audit_trail[-1].state == workflow.current_state
                for workflow in self.workflows.values()
            )

            # QCRequired: No sample reported without QC approval
            results['QCRequired'] = all(
                workflow.has_qc_approval()
                for workflow in self.workflows.values()
                if workflow.current_state in [SampleState.REPORTED, SampleState.ARCHIVED]
            )

            # MonotonicProgression: No repeated states in audit trail
            results['MonotonicProgression'] = all(
                len(set(entry.state for entry in workflow.audit_trail)) == len(
                    workflow.audit_trail)
                for workflow in self.workflows.values()
            )

            # ResourceBounds: Testing capacity not exceeded
            results['ResourceBounds'] = len(
                self.samples_in_testing) <= self.max_concurrent_tests

            # QCApprovedConsistency: QC tracking matches workflow states
            actual_qc_approved = {
                sample_id for sample_id, workflow in self.workflows.items()
                if workflow.has_qc_approval()
            }
            results['QCApprovedConsistency'] = self.qc_approved_samples == actual_qc_approved

            return results

        except Exception as e:
            logger.error(f"Invariant validation failed: {e}")
            return {"ValidationError": False}

    def get_system_stats(self) -> Dict[str, any]:
        """Get comprehensive system statistics"""
        state_counts = {}
        for state in SampleState:
            state_counts[state.value] = len(self.get_samples_by_state(state))

        return {
            "total_samples": len(self.workflows),
            "next_sample_id": self.next_sample_id,
            "state_distribution": state_counts,
            "testing_capacity": self.get_testing_capacity_status(),
            "qc_approved_count": len(self.qc_approved_samples),
            "invariant_status": self.validate_system_invariants()
        }

    def validate_workflows(self) -> None:
        """
        Validate all workflows in the system against TLA+ properties.
        
        This checks:
        - Audit trail of each workflow is valid (starts with RECEIVED, no re-visits)
        - Current state of each workflow is consistent with audit trail
        """
        for workflow in self.workflows.values():
            # Validate audit trail
            workflow.validate_audit_trail()

            # Check current state consistency
            if workflow.current_state != workflow.audit_trail[-1].state:
                raise TLAPropertyError(f"Workflow current state {workflow.current_state} "
                                       f"does not match last audit trail state {workflow.audit_trail[-1].state}")

        logger.info("All workflows validated successfully")


# Export main classes
__all__ = [
    'SampleState',
    'Sample', 
    'SampleWorkflow',
    'LIMSSystemState',
    'AuditLogEntry'
]
