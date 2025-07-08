"""
PredicateLogic Engine Core Models

Data models derived from TLA+ type definitions, with runtime validation
to enforce mathematically verified properties.
"""

from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from typing import Any, Dict, List, Optional, Set, Union
from pydantic import BaseModel, Field, validator
import uuid
import time


class RuleState(str, Enum):
    """Rule lifecycle states from TLA+ specification."""
    DRAFT = "DRAFT"
    ACTIVE = "ACTIVE"
    INACTIVE = "INACTIVE"
    DEPRECATED = "DEPRECATED"


class EvaluationState(str, Enum):
    """Evaluation processing states from TLA+ specification."""
    PENDING = "PENDING"
    PROCESSING = "PROCESSING"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"


class FactType(str, Enum):
    """Fact types for LIMS domain from TLA+ specification."""
    SAMPLE_DATA = "SAMPLE_DATA"
    TEST_RESULT = "TEST_RESULT"
    QC_METRIC = "QC_METRIC"
    WORKFLOW_STATE = "WORKFLOW_STATE"
    USER_INPUT = "USER_INPUT"


class ConditionOperator(str, Enum):
    """Rule condition operators from TLA+ specification."""
    EQUALS = "EQUALS"
    NOT_EQUALS = "NOT_EQUALS"
    LESS_THAN = "LESS_THAN"
    GREATER_THAN = "GREATER_THAN"
    CONTAINS = "CONTAINS"
    IN_SET = "IN_SET"


class InferenceAction(str, Enum):
    """Inference step types from TLA+ specification."""
    FORWARD_CHAIN = "FORWARD_CHAIN"
    BACKWARD_CHAIN = "BACKWARD_CHAIN"
    UNIFY = "UNIFY"
    RESOLVE = "RESOLVE"
    START_EVALUATION = "START_EVALUATION"
    RESULT_TRUE = "RESULT_TRUE"
    RESULT_FALSE = "RESULT_FALSE"


@dataclass
class RuleCondition:
    """Individual rule condition with TLA+ type validation."""
    field: str
    operator: ConditionOperator
    value: str
    
    def __post_init__(self):
        if not isinstance(self.field, str) or not self.field.strip():
            raise ValueError("Field must be non-empty string")
        if not isinstance(self.value, str):
            raise ValueError("Value must be string")


@dataclass
class RuleAction:
    """Rule action with TLA+ type validation."""
    type: str
    parameters: str
    
    def __post_init__(self):
        if not isinstance(self.type, str) or not self.type.strip():
            raise ValueError("Action type must be non-empty string")
        if not isinstance(self.parameters, str):
            raise ValueError("Parameters must be string")


class Rule(BaseModel):
    """
    Rule model based on TLA+ RuleType specification.
    
    Enforces type safety and validation from formal verification.
    """
    id: str = Field(..., min_length=1, description="Unique rule identifier")
    name: str = Field(..., min_length=1, description="Human-readable rule name")
    conditions: List[RuleCondition] = Field(default_factory=list)
    actions: List[RuleAction] = Field(default_factory=list)
    priority: int = Field(default=1, ge=1, le=100, description="Rule priority (1-100)")
    state: RuleState = Field(default=RuleState.DRAFT)
    dependencies: Set[str] = Field(default_factory=set, description="Dependent rule IDs")
    created_at: datetime = Field(default_factory=datetime.utcnow)
    updated_at: datetime = Field(default_factory=datetime.utcnow)
    
    @validator('dependencies')
    def validate_no_self_dependency(cls, v, values):
        """Prevent rule from depending on itself."""
        if 'id' in values and values['id'] in v:
            raise ValueError("Rule cannot depend on itself")
        return v
    
    def can_activate(self) -> bool:
        """Check if rule can be activated (TLA+ RuleIsReady logic)."""
        return (
            self.state == RuleState.DRAFT and
            len(self.conditions) > 0  # Must have conditions to be useful
        )


class Fact(BaseModel):
    """
    Fact model based on TLA+ FactType specification.
    
    Maintains integrity constraints verified in formal model.
    """
    id: str = Field(..., min_length=1, description="Unique fact identifier")
    type: FactType = Field(..., description="Type of fact")
    attributes: Dict[str, Any] = Field(..., description="Fact attributes")
    timestamp: float = Field(default_factory=time.time, description="Creation timestamp")
    confidence: int = Field(default=100, ge=0, le=100, description="Confidence level (0-100)")
    source: Optional[str] = Field(None, description="Source of the fact")
    
    @validator('attributes')
    def validate_attributes_not_empty(cls, v):
        """Ensure fact has meaningful attributes."""
        if not v:
            raise ValueError("Fact must have at least one attribute")
        return v
    
    @validator('timestamp')
    def validate_timestamp_not_future(cls, v):
        """Ensure timestamp is not in the future."""
        if v > time.time() + 1:  # Allow 1 second tolerance for clock skew
            raise ValueError("Timestamp cannot be in the future")
        return v


class Evaluation(BaseModel):
    """
    Evaluation model based on TLA+ EvaluationType specification.
    
    Tracks rule evaluation with state management from formal model.
    """
    id: str = Field(default_factory=lambda: str(uuid.uuid4()), description="Unique evaluation ID")
    rule_id: str = Field(..., min_length=1, description="ID of rule being evaluated")
    input_facts: Set[str] = Field(..., description="IDs of facts used in evaluation")
    state: EvaluationState = Field(default=EvaluationState.PENDING)
    start_time: float = Field(default_factory=time.time)
    end_time: Optional[float] = Field(None)
    result: Optional[bool] = Field(None, description="Evaluation result")
    inference_chain: List[InferenceAction] = Field(default_factory=list)
    error_message: Optional[str] = Field(None)
    
    @validator('end_time')
    def validate_end_after_start(cls, v, values):
        """Ensure end time is after start time."""
        if v is not None and 'start_time' in values and v < values['start_time']:
            raise ValueError("End time must be after start time")
        return v
    
    @validator('result')
    def validate_result_with_state(cls, v, values):
        """Ensure result is set only for completed evaluations."""
        if 'state' in values:
            if values['state'] == EvaluationState.COMPLETED and v is None:
                raise ValueError("Completed evaluation must have a result")
            if values['state'] != EvaluationState.COMPLETED and v is not None:
                raise ValueError("Only completed evaluations can have results")
        return v
    
    def duration(self) -> Optional[float]:
        """Calculate evaluation duration."""
        if self.end_time:
            return self.end_time - self.start_time
        return None
    
    def is_terminal(self) -> bool:
        """Check if evaluation is in terminal state."""
        return self.state in {EvaluationState.COMPLETED, EvaluationState.FAILED}


class PredicateLogicEngineState(BaseModel):
    """
    Complete engine state model enforcing TLA+ invariants.
    
    This model maintains all state variables from the formal specification
    and enforces safety properties at runtime.
    """
    rules: Dict[str, Rule] = Field(default_factory=dict)
    facts: Dict[str, Fact] = Field(default_factory=dict)
    evaluation_queue: List[str] = Field(default_factory=list, description="Queue of pending evaluation IDs")
    active_evaluations: Dict[str, Evaluation] = Field(default_factory=dict)
    evaluation_results: Dict[str, bool] = Field(default_factory=dict)
    history: List[Dict[str, Any]] = Field(default_factory=list)
    
    # Configuration from TLA+ constants
    max_facts: int = Field(default=1000, ge=1)
    max_evaluations: int = Field(default=100, ge=1)
    max_inference_depth: int = Field(default=10, ge=1)
    max_trace_length: int = Field(default=100, ge=1)
    
    def validate_type_invariant(self) -> bool:
        """
        Enforce TLA+ TypeInvariant property.
        
        This validation ensures all data structures maintain their 
        expected types, as verified in the formal model.
        """
        # Rules validation
        for rule_id, rule in self.rules.items():
            if not isinstance(rule, Rule):
                raise TypeError(f"Rule {rule_id} is not of type Rule")
            if rule.id != rule_id:
                raise ValueError(f"Rule ID mismatch: {rule.id} != {rule_id}")
        
        # Facts validation  
        for fact_id, fact in self.facts.items():
            if not isinstance(fact, Fact):
                raise TypeError(f"Fact {fact_id} is not of type Fact")
            if fact.id != fact_id:
                raise ValueError(f"Fact ID mismatch: {fact.id} != {fact_id}")
        
        # Evaluations validation
        for eval_id, evaluation in self.active_evaluations.items():
            if not isinstance(evaluation, Evaluation):
                raise TypeError(f"Evaluation {eval_id} is not of type Evaluation")
            if evaluation.id != eval_id:
                raise ValueError(f"Evaluation ID mismatch: {evaluation.id} != {eval_id}")
        
        return True
    
    def validate_memory_bounds(self) -> bool:
        """
        Enforce TLA+ MemoryBounds property.
        
        Ensures the system operates within defined capacity limits.
        """
        if len(self.facts) > self.max_facts:
            raise ValueError(f"Facts count {len(self.facts)} exceeds limit {self.max_facts}")
        
        total_evaluations = len(self.evaluation_queue) + len(self.active_evaluations)
        if total_evaluations > self.max_evaluations:
            raise ValueError(f"Total evaluations {total_evaluations} exceeds limit {self.max_evaluations}")
        
        for evaluation in self.active_evaluations.values():
            if len(evaluation.inference_chain) > self.max_inference_depth:
                raise ValueError(f"Inference chain length {len(evaluation.inference_chain)} exceeds limit {self.max_inference_depth}")
        
        if len(self.history) > self.max_trace_length:
            raise ValueError(f"History length {len(self.history)} exceeds limit {self.max_trace_length}")
        
        return True
    
    def validate_fact_integrity(self) -> bool:
        """
        Enforce TLA+ FactIntegrity property.
        
        Ensures facts maintain valid confidence values and timestamps.
        """
        for fact in self.facts.values():
            if not (0 <= fact.confidence <= 100):
                raise ValueError(f"Fact {fact.id} has invalid confidence {fact.confidence}")
            
            # In TLA+ we check timestamp <= Len(history), here we ensure it's reasonable
            if fact.timestamp > time.time() + 1:
                raise ValueError(f"Fact {fact.id} has future timestamp {fact.timestamp}")
        
        return True
    
    def validate_capacity_constraints(self) -> bool:
        """
        Enforce TLA+ CapacityConstraints property.
        
        Validates system-wide capacity limits.
        """
        if len(self.evaluation_queue) > self.max_evaluations:
            raise ValueError(f"Evaluation queue length {len(self.evaluation_queue)} exceeds limit")
        
        if len(self.active_evaluations) > self.max_evaluations:
            raise ValueError(f"Active evaluations count {len(self.active_evaluations)} exceeds limit")
        
        if len(self.facts) > self.max_facts:
            raise ValueError(f"Facts count {len(self.facts)} exceeds limit")
        
        return True
    
    def validate_all_properties(self) -> bool:
        """
        Validate all TLA+ properties that can be checked at runtime.
        
        This method enforces the safety properties that were mathematically
        verified in our formal model.
        """
        self.validate_type_invariant()
        self.validate_memory_bounds()
        self.validate_fact_integrity()
        self.validate_capacity_constraints()
        return True


# Exception classes for property violations
class TLAPropertyViolationError(Exception):
    """Base exception for TLA+ property violations."""
    pass


class TypeInvariantViolationError(TLAPropertyViolationError):
    """Type safety property violation."""
    pass


class MemoryBoundsViolationError(TLAPropertyViolationError):
    """Memory bounds property violation."""
    pass


class FactIntegrityViolationError(TLAPropertyViolationError):
    """Fact integrity property violation."""
    pass


class CapacityConstraintViolationError(TLAPropertyViolationError):
    """Capacity constraint property violation."""
    pass
