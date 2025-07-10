"""
Data Models for Natural Language Calendar Workflow
Based on TLA+ validated specification: NaturalLanguageCalendarWorkflow.tla

These models represent the state and data structures validated by the TLA+ model checker.
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, Any, List, Optional, Sequence
from datetime import datetime
import json


class IntentType(Enum):
    """Intent types as defined in TLA+ specification"""
    SCHEDULE = "SCHEDULE"
    CANCEL = "CANCEL"  
    QUERY = "QUERY"
    RESCHEDULE = "RESCHEDULE"


class OperationType(Enum):
    """Calendar operation types from TLA+ specification"""
    CREATE = "CREATE"
    UPDATE = "UPDATE"
    DELETE = "DELETE"
    QUERY = "QUERY"


class OperationStatus(Enum):
    """Operation status from TLA+ specification"""
    PENDING = "PENDING"
    IN_PROGRESS = "IN_PROGRESS"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"


class SystemState(Enum):
    """System component states from TLA+ specification"""
    # Intent Parser States
    IDLE = "IDLE"
    PARSING = "PARSING"
    
    # Orchestrator States
    READY = "READY"
    ORCHESTRATING = "ORCHESTRATING"
    
    # Vector Storage States
    AVAILABLE = "AVAILABLE"
    BUSY = "BUSY"
    
    # Response Generator States
    GENERATING = "GENERATING"
    
    # Common Error State
    ERROR = "ERROR"


class ResponseStatus(Enum):
    """Response status types from TLA+ specification"""
    SUCCESS = "SUCCESS"
    PARTIAL = "PARTIAL"
    FAILED = "FAILED"


@dataclass
class NLRequest:
    """Natural language request from user"""
    request_id: int
    user: str
    content: str
    timestamp: datetime = field(default_factory=datetime.now)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "request_id": self.request_id,
            "user": self.user,
            "content": self.content,
            "timestamp": self.timestamp.isoformat()
        }


@dataclass
class ParsedIntent:
    """Parsed intent data as defined in TLA+ specification"""
    request_id: int
    type: IntentType
    resource: str
    user: str
    parameters: List[Any] = field(default_factory=list)
    timestamp: datetime = field(default_factory=datetime.now)
    confidence: float = 1.0
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "request_id": self.request_id,
            "type": self.type.value,
            "resource": self.resource,
            "user": self.user,
            "parameters": self.parameters,
            "timestamp": self.timestamp.isoformat(),
            "confidence": self.confidence
        }


@dataclass  
class CalendarOperation:
    """Calendar operation as defined in TLA+ specification"""
    id: int
    operation: OperationType
    resource: str
    user: str
    status: OperationStatus = OperationStatus.PENDING
    created_at: datetime = field(default_factory=datetime.now)
    updated_at: datetime = field(default_factory=datetime.now)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "operation": self.operation.value,
            "resource": self.resource,
            "user": self.user,
            "status": self.status.value,
            "created_at": self.created_at.isoformat(),
            "updated_at": self.updated_at.isoformat(),
            "metadata": self.metadata
        }


@dataclass
class StorageRequest:
    """Storage request as defined in TLA+ specification"""
    id: int
    operation: str  # "STORE", "RETRIEVE", "DELETE"
    data: List[Any]
    status: OperationStatus = OperationStatus.PENDING
    created_at: datetime = field(default_factory=datetime.now)
    embedding: Optional[List[float]] = None
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "operation": self.operation,
            "data": self.data,
            "status": self.status.value,
            "created_at": self.created_at.isoformat(),
            "embedding": self.embedding,
            "metadata": self.metadata
        }


@dataclass
class WorkflowResponse:
    """Response as defined in TLA+ specification"""
    request_id: int
    status: ResponseStatus
    message: str
    data: List[Any] = field(default_factory=list)
    timestamp: datetime = field(default_factory=datetime.now)
    processing_time_ms: Optional[float] = None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "request_id": self.request_id,
            "status": self.status.value,
            "message": self.message,
            "data": self.data,
            "timestamp": self.timestamp.isoformat(),
            "processing_time_ms": self.processing_time_ms
        }


@dataclass
class SystemMetrics:
    """System metrics for monitoring TLA+ validated invariants"""
    total_processed: int = 0
    successful_schedules: int = 0
    failed_operations: int = 0
    active_requests: int = 0
    parsed_intents: int = 0
    calendar_operations: int = 0
    storage_operations: int = 0
    average_processing_time_ms: float = 0.0
    system_uptime_seconds: float = 0.0
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "total_processed": self.total_processed,
            "successful_schedules": self.successful_schedules,
            "failed_operations": self.failed_operations,
            "active_requests": self.active_requests,
            "parsed_intents": self.parsed_intents,
            "calendar_operations": self.calendar_operations,
            "storage_operations": self.storage_operations,
            "average_processing_time_ms": self.average_processing_time_ms,
            "system_uptime_seconds": self.system_uptime_seconds
        }


@dataclass
class ComponentStates:
    """Component states for monitoring TLA+ state consistency invariant"""
    intent_parser: SystemState = SystemState.IDLE
    orchestrator: SystemState = SystemState.READY
    vector_storage: SystemState = SystemState.AVAILABLE
    response_generator: SystemState = SystemState.IDLE
    last_updated: datetime = field(default_factory=datetime.now)
    
    def to_dict(self) -> Dict[str, str]:
        return {
            "intent_parser": self.intent_parser.value,
            "orchestrator": self.orchestrator.value,
            "vector_storage": self.vector_storage.value,
            "response_generator": self.response_generator.value,
            "last_updated": self.last_updated.isoformat()
        }
    
    def is_all_ready(self) -> bool:
        """Check if all components are in ready/available state"""
        return (
            self.intent_parser == SystemState.IDLE and
            self.orchestrator == SystemState.READY and
            self.vector_storage == SystemState.AVAILABLE and
            self.response_generator == SystemState.IDLE
        )


@dataclass
class ScheduleData:
    """Data structure for calendar schedule information"""
    schedule_id: str
    resource: str
    user: str
    start_time: datetime
    end_time: datetime
    description: str
    samples: List[str] = field(default_factory=list)
    protocol: Optional[str] = None
    priority: str = "NORMAL"
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "schedule_id": self.schedule_id,
            "resource": self.resource,
            "user": self.user,
            "start_time": self.start_time.isoformat(),
            "end_time": self.end_time.isoformat(),
            "description": self.description,
            "samples": self.samples,
            "protocol": self.protocol,
            "priority": self.priority,
            "metadata": self.metadata
        }
    
    def to_embedding_text(self) -> str:
        """Convert schedule to text for vector embedding"""
        return f"""
        Schedule: {self.description}
        Resource: {self.resource}
        User: {self.user}
        Time: {self.start_time} to {self.end_time}
        Samples: {', '.join(self.samples)}
        Protocol: {self.protocol or 'None'}
        Priority: {self.priority}
        """.strip()


@dataclass
class WorkflowConfiguration:
    """Configuration for Natural Language Calendar Workflow"""
    max_requests: int = 100
    max_parsed_intents: int = 100
    max_calendar_ops: int = 100
    max_storage_ops: int = 100
    users: List[str] = field(default_factory=list)
    resources: List[str] = field(default_factory=list)
    intent_types: List[str] = field(default_factory=lambda: ["SCHEDULE", "CANCEL", "QUERY"])
    vector_storage_config: Dict[str, Any] = field(default_factory=dict)
    intent_parser_config: Dict[str, Any] = field(default_factory=dict)
    calendar_config: Dict[str, Any] = field(default_factory=dict)
    response_templates: Dict[str, str] = field(default_factory=dict)
    
    def validate(self) -> bool:
        """Validate configuration according to TLA+ constraints"""
        if self.max_requests <= 0:
            raise ValueError("max_requests must be positive")
        if self.max_parsed_intents <= 0:
            raise ValueError("max_parsed_intents must be positive")
        if self.max_calendar_ops <= 0:
            raise ValueError("max_calendar_ops must be positive")
        if self.max_storage_ops <= 0:
            raise ValueError("max_storage_ops must be positive")
        if not self.users:
            raise ValueError("users list cannot be empty")
        if not self.resources:
            raise ValueError("resources list cannot be empty")
        if not self.intent_types:
            raise ValueError("intent_types list cannot be empty")
        
        return True
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "max_requests": self.max_requests,
            "max_parsed_intents": self.max_parsed_intents,
            "max_calendar_ops": self.max_calendar_ops,
            "max_storage_ops": self.max_storage_ops,
            "users": self.users,
            "resources": self.resources,
            "intent_types": self.intent_types,
            "vector_storage_config": self.vector_storage_config,
            "intent_parser_config": self.intent_parser_config,
            "calendar_config": self.calendar_config,
            "response_templates": self.response_templates
        }
