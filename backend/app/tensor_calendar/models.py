"""
Data models for Tensor Calendar Vector Storage System
Based on TLA+ validated specification
"""

from dataclasses import dataclass, field
from typing import Dict, Any, List, Optional, Union
from datetime import datetime
import json


@dataclass
class TensorCalendar:
    """
    Tensor calendar data structure
    
    Represents laboratory scheduling data that can be stored as tensor embeddings
    in the vector database for similarity search and retrieval.
    """
    tensor_id: str
    calendar_data: Dict[str, Any]
    embedding: Optional[List[float]] = None
    stored_at: Optional[datetime] = None
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for storage"""
        return {
            "tensor_id": self.tensor_id,
            "calendar_data": self.calendar_data,
            "embedding": self.embedding,
            "stored_at": self.stored_at.isoformat() if self.stored_at else None,
            "metadata": self.metadata
        }
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "TensorCalendar":
        """Create from dictionary"""
        stored_at = None
        if data.get("stored_at"):
            stored_at = datetime.fromisoformat(data["stored_at"])
        
        return cls(
            tensor_id=data["tensor_id"],
            calendar_data=data["calendar_data"],
            embedding=data.get("embedding"),
            stored_at=stored_at,
            metadata=data.get("metadata", {})
        )


@dataclass
class SystemMetrics:
    """
    Storage system metrics
    
    Tracks performance and utilization metrics as defined in TLA+ specification.
    Invariant: storage_utilization must always be between 0 and 100.
    """
    total_stored: int = 0
    cache_hits: int = 0
    cache_misses: int = 0
    avg_query_time: float = 0.0
    storage_utilization: int = 0  # Percentage 0-100
    
    def __post_init__(self):
        """Validate metrics constraints"""
        if not 0 <= self.storage_utilization <= 100:
            raise ValueError("Storage utilization must be between 0 and 100")
        if self.total_stored < 0:
            raise ValueError("Total stored cannot be negative")


@dataclass
class Sample:
    """Laboratory sample data structure"""
    sample_id: str
    sample_type: str
    properties: Dict[str, Any] = field(default_factory=dict)
    created_at: Optional[datetime] = None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "sample_id": self.sample_id,
            "sample_type": self.sample_type,
            "properties": self.properties,
            "created_at": self.created_at.isoformat() if self.created_at else None
        }


@dataclass
class Resource:
    """Laboratory resource data structure"""
    resource_id: str
    resource_type: str
    availability: Dict[str, Any] = field(default_factory=dict)
    capabilities: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "resource_id": self.resource_id,
            "resource_type": self.resource_type,
            "availability": self.availability,
            "capabilities": self.capabilities
        }


@dataclass
class Workflow:
    """Laboratory workflow data structure"""
    workflow_id: str
    workflow_type: str
    steps: List[Dict[str, Any]] = field(default_factory=list)
    dependencies: List[str] = field(default_factory=list)
    estimated_duration: Optional[int] = None  # minutes
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "workflow_id": self.workflow_id,
            "workflow_type": self.workflow_type,
            "steps": self.steps,
            "dependencies": self.dependencies,
            "estimated_duration": self.estimated_duration
        }


@dataclass
class Schedule:
    """Laboratory schedule data structure"""
    schedule_id: str
    start_time: datetime
    end_time: datetime
    resources: List[str] = field(default_factory=list)
    samples: List[str] = field(default_factory=list)
    workflow_id: Optional[str] = None
    status: str = "scheduled"  # scheduled, in_progress, completed, cancelled
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "schedule_id": self.schedule_id,
            "start_time": self.start_time.isoformat(),
            "end_time": self.end_time.isoformat(),
            "resources": self.resources,
            "samples": self.samples,
            "workflow_id": self.workflow_id,
            "status": self.status
        }
    
    @property
    def duration_minutes(self) -> int:
        """Calculate duration in minutes"""
        delta = self.end_time - self.start_time
        return int(delta.total_seconds() / 60)


@dataclass
class CalendarEvent:
    """Calendar event for tensor calendar system"""
    event_id: str
    event_type: str  # schedule, workflow, maintenance, etc.
    start_time: datetime
    end_time: datetime
    data: Dict[str, Any] = field(default_factory=dict)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "event_id": self.event_id,
            "event_type": self.event_type,
            "start_time": self.start_time.isoformat(),
            "end_time": self.end_time.isoformat(),
            "data": self.data,
            "metadata": self.metadata
        }
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "CalendarEvent":
        return cls(
            event_id=data["event_id"],
            event_type=data["event_type"],
            start_time=datetime.fromisoformat(data["start_time"]),
            end_time=datetime.fromisoformat(data["end_time"]),
            data=data.get("data", {}),
            metadata=data.get("metadata", {})
        )
