"""
PredicateLogic Engine Package

TLA+ verified rule evaluation and inference engine for ALIMS.
This package provides mathematically proven safety guarantees.
"""

from .core import PredicateLogicEngine, EngineConfiguration
from .models import (
    Rule, Fact, Evaluation, 
    RuleState, EvaluationState, FactType, ConditionOperator,
    RuleCondition, RuleAction,
    TLAPropertyViolationError
)

__version__ = "1.0.0"
__author__ = "ALIMS Development Team"
__description__ = "TLA+ verified predicate logic engine with formal safety guarantees"

# Export main classes
__all__ = [
    "PredicateLogicEngine",
    "EngineConfiguration", 
    "Rule",
    "Fact",
    "Evaluation",
    "RuleState",
    "EvaluationState",
    "FactType",
    "ConditionOperator",
    "RuleCondition",
    "RuleAction",
    "TLAPropertyViolationError"
]

# Quick access factory function
def create_engine(**config_kwargs) -> PredicateLogicEngine:
    """
    Create a PredicateLogic Engine with configuration.
    
    Example:
        engine = create_engine(max_facts=500, max_evaluations=50)
    """
    config = EngineConfiguration(**config_kwargs)
    return PredicateLogicEngine(config)
