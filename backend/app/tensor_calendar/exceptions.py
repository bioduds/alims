"""
Exceptions for Tensor Calendar Vector Storage System
Based on TLA+ validated specification error conditions
"""


class TensorConstraintError(Exception):
    """
    Raised when TLA+ validated constraints are violated
    
    This exception indicates that an operation would violate one of the
    mathematically proven invariants from the TLA+ specification:
    - StorageCapacityInvariant: Storage capacity exceeded
    - TensorVectorConsistency: Tensor-vector mapping inconsistency
    - ValidStorageMetrics: Invalid storage metrics
    - ValidSystemState: Invalid system state transition
    """
    pass


class TensorNotFoundError(TensorConstraintError):
    """Raised when attempting to access a non-existent tensor"""
    pass


class TensorAlreadyExistsError(TensorConstraintError):
    """Raised when attempting to store a tensor that already exists"""
    pass


class InvalidEmbeddingError(TensorConstraintError):
    """Raised when tensor embedding is invalid"""
    pass


class StorageCapacityError(TensorConstraintError):
    """Raised when storage capacity would be exceeded"""
    pass


class VectorDatabaseError(TensorConstraintError):
    """Raised when vector database operations fail"""
    pass


class SystemStateError(TensorConstraintError):
    """Raised when system is in invalid state for operation"""
    pass
