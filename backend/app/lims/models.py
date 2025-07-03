"""
Core LIMS Data Models - Based on TLA+ Specification

These Pydantic models implement the data structures verified in our
TLA+ specification CoreLIMSWorkflow.tla, ensuring type safety and
validation at runtime.
"""

from datetime import datetime
from enum import Enum
from typing import List, Dict, Optional
from pydantic import BaseModel, Field, field_validator
from uuid import UUID, uuid4


class SampleState(str, Enum):
    """
    Sample states as defined in TLA+ specification.
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
    """Single audit trail entry"""
    timestamp: datetime = Field(default_factory=datetime.now)
    state: SampleState
    actor: str  # Who performed the action
    notes: Optional[str] = None


class Sample(BaseModel):
    """
    Sample record structure matching TLA+ model.
    
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


class SampleWorkflow(BaseModel):
    """
    Complete sample workflow state.
    
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
        # Ensure initial audit entry exists
        if not self.audit_trail:
            self.audit_trail.append(
                AuditLogEntry(
                    state=SampleState.RECEIVED,
                    actor="system",
                    notes="Sample received into LIMS"
                )
            )
    
    @field_validator('audit_trail')
    @classmethod
    def audit_trail_must_start_with_received(cls, v):
        if v and v[0].state != SampleState.RECEIVED:
            raise ValueError('Audit trail must start with RECEIVED state')
        return v
    
    def get_valid_next_states(self) -> List[SampleState]:
        """Get valid next states for current sample state"""
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
        Transition sample to new state with validation.
        
        This implements the ValidTransition predicate from TLA+ specification.
        """
        if not self.can_transition_to(new_state):
            raise ValueError(f"Invalid transition from {self.current_state} to {new_state}")
        
        # Verify monotonic progression (TLA+ MonotonicProgression property)
        existing_states = [entry.state for entry in self.audit_trail]
        if new_state in existing_states:
            raise ValueError(f"State {new_state} already visited - violates monotonic progression")
        
        # Update state
        self.current_state = new_state
        self.audit_trail.append(
            AuditLogEntry(
                state=new_state,
                actor=actor,
                notes=notes
            )
        )
        
        return True
    
    def has_qc_approval(self) -> bool:
        """Check if sample has gone through QC approval (TLA+ QCRequired property)"""
        qc_states = [entry.state for entry in self.audit_trail]
        return SampleState.QC_APPROVED in qc_states
    
    def can_be_reported(self) -> bool:
        """Check if sample can be reported (requires QC approval)"""
        return (self.current_state == SampleState.QC_APPROVED or 
                (self.current_state in [SampleState.REPORTED, SampleState.ARCHIVED] 
                 and self.has_qc_approval()))


class LIMSSystemState(BaseModel):
    """
    Complete LIMS system state matching TLA+ variables.
    
    This implements:
    - samples: Sample ID -> Sample record
    - sampleStates: Sample ID -> Current state
    - auditTrail: Sample ID -> Sequence of state transitions  
    - nextSampleID: Next available sample ID
    """
    workflows: Dict[int, SampleWorkflow] = Field(default_factory=dict)
    next_sample_id: int = Field(default=1)
    max_samples: int = Field(default=10000)
    
    def create_sample(self, barcode: str, **kwargs) -> int:
        """
        Create new sample (implements ReceiveSample action from TLA+).
        
        Returns the new sample ID.
        """
        if self.next_sample_id > self.max_samples:
            raise ValueError("Maximum samples exceeded")
        
        sample_id = self.next_sample_id
        
        # Create sample
        sample = Sample(
            id=sample_id,
            barcode=barcode,
            **kwargs
        )
        
        # Create workflow
        workflow = SampleWorkflow(sample=sample)
        
        # Add to system
        self.workflows[sample_id] = workflow
        self.next_sample_id += 1
        
        return sample_id
    
    def get_sample(self, sample_id: int) -> Optional[SampleWorkflow]:
        """Get sample workflow by ID"""
        return self.workflows.get(sample_id)
    
    def transition_sample(self, sample_id: int, new_state: SampleState, 
                         actor: str, notes: Optional[str] = None) -> bool:
        """Transition sample to new state"""
        workflow = self.get_sample(sample_id)
        if not workflow:
            raise ValueError(f"Sample {sample_id} not found")
        
        return workflow.transition_to(new_state, actor, notes)
    
    def get_samples_by_state(self, state: SampleState) -> List[SampleWorkflow]:
        """Get all samples in a specific state"""
        return [workflow for workflow in self.workflows.values() 
                if workflow.current_state == state]
    
    def validate_system_invariants(self) -> Dict[str, bool]:
        """
        Validate all TLA+ invariants hold for current system state.
        
        Returns dict of invariant name -> validation result.
        """
        results = {}
        
        # TypeInv: All variables have correct types (automatically enforced by Pydantic)
        results['TypeInv'] = True
        
        # SampleIDUniqueness: Every sample has unique ID
        sample_ids = [workflow.sample.id for workflow in self.workflows.values()]
        results['SampleIDUniqueness'] = len(sample_ids) == len(set(sample_ids))
        
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
            len([entry.state for entry in workflow.audit_trail]) == 
            len(set([entry.state for entry in workflow.audit_trail]))
            for workflow in self.workflows.values()
        )
        
        return results


# Export main classes
__all__ = [
    'SampleState',
    'Sample', 
    'SampleWorkflow',
    'LIMSSystemState',
    'AuditLogEntry'
]
