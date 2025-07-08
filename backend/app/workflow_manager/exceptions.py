"""
ALIMS Workflow Manager Service - Exception Classes

This module defines custom exceptions for the Workflow Manager Service,
aligned with TLA+ specification error conditions.
"""

class WorkflowManagerError(Exception):
    """Base exception for all Workflow Manager errors"""
    pass

# TLA+ Property Violation Exceptions
class TLAPropertyViolationError(WorkflowManagerError):
    """Base class for TLA+ property violations"""
    pass

class WorkflowUniquenessError(TLAPropertyViolationError):
    """TLA+ WorkflowUniqueness property violation"""
    pass

class BoundedWorkflowsError(TLAPropertyViolationError):
    """TLA+ BoundedWorkflows property violation"""
    pass

class TerminalStateImmutabilityError(TLAPropertyViolationError):
    """TLA+ TerminalStateImmutability property violation"""
    pass

class ConcurrentSafetyError(TLAPropertyViolationError):
    """TLA+ ConcurrentSafety property violation"""
    pass

class TransitionValidityError(TLAPropertyViolationError):
    """TLA+ TransitionValidity property violation"""
    pass

# Operational Exceptions
class WorkflowNotFoundError(WorkflowManagerError):
    """Workflow with given ID not found"""
    pass

class InvalidTransitionError(WorkflowManagerError):
    """Invalid state transition attempted"""
    pass

class TerminalStateError(WorkflowManagerError):
    """Operation not allowed on terminal state workflow"""
    pass

class ConcurrentModificationError(WorkflowManagerError):
    """Concurrent modification detected (optimistic locking failure)"""
    pass

class PredicateLogicUnavailableError(WorkflowManagerError):
    """PredicateLogic service unavailable"""
    pass

class ValidationError(WorkflowManagerError):
    """Data validation error"""
    pass

class RecoveryError(WorkflowManagerError):
    """Error during workflow recovery"""
    pass
