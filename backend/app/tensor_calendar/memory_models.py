"""
Enhanced Tensor Calendar with Unified Memory System
Revolutionary 4D Memory Architecture: Semantic + Temporal + Contextual + Modal

This system eliminates the distinction between short/long-term memory by creating
a unified temporal-semantic memory space where everything is searchable by both
content and time context.
"""

from enum import Enum
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Union, Tuple
from datetime import datetime, timedelta
import json
import numpy as np
from pydantic import BaseModel, Field


class MemoryType(Enum):
    """Types of memories stored in the tensor space"""
    CONVERSATION = "conversation"      # Chat interactions
    EVENT = "event"                   # Scheduled events, operations
    FACT = "fact"                     # Learned facts, knowledge
    DECISION = "decision"             # Decisions made by agent
    OBSERVATION = "observation"       # Environmental observations
    RELATIONSHIP = "relationship"     # Entity relationships
    WORKFLOW = "workflow"             # Process executions
    REFLECTION = "reflection"         # Meta-cognitive insights


class MemoryScope(Enum):
    """Scope/lifetime of memory"""
    SESSION = "session"               # Current session only
    PERSISTENT = "persistent"         # Permanent storage
    CONTEXTUAL = "contextual"         # Context-dependent retention
    EVOLVING = "evolving"             # Can be updated/refined


class ModalityType(Enum):
    """Data modalities in memory"""
    TEXT = "text"
    NUMERICAL = "numerical"
    TEMPORAL = "temporal"
    SPATIAL = "spatial"
    GRAPH = "graph"
    MEDIA = "media"


@dataclass
class TemporalContext:
    """Rich temporal context for memories"""
    timestamp: datetime
    duration: Optional[timedelta] = None
    timezone: str = "UTC"
    relative_time: Optional[str] = None  # "yesterday", "last week"
    temporal_precision: str = "exact"    # exact, approximate, fuzzy
    temporal_tags: List[str] = field(default_factory=list)


@dataclass
class SemanticContext:
    """Semantic context and relationships"""
    topics: List[str] = field(default_factory=list)
    entities: List[str] = field(default_factory=list)
    relationships: Dict[str, List[str]] = field(default_factory=dict)
    semantic_tags: List[str] = field(default_factory=list)
    confidence: float = 1.0


@dataclass
class ConversationalContext:
    """Context specific to conversations"""
    speaker: str
    conversation_id: str
    turn_number: int
    response_to: Optional[str] = None
    sentiment: Optional[str] = None
    intent: Optional[str] = None


@dataclass
class WorkflowContext:
    """Context for workflow/process memories"""
    workflow_id: str
    step_number: int
    operation_type: str
    success: bool
    error_message: Optional[str] = None
    performance_metrics: Dict[str, float] = field(default_factory=dict)


class UnifiedMemory(BaseModel):
    """
    Unified Memory Entry - the fundamental unit of the 4D memory tensor
    
    This single class handles all types of memories with rich temporal,
    semantic, and contextual information.
    """
    
    # Core Identity
    id: str = Field(..., description="Unique memory identifier")
    memory_type: MemoryType
    scope: MemoryScope
    
    # Content (Multi-modal)
    content: Dict[ModalityType, Any] = Field(default_factory=dict)
    primary_text: str = Field(..., description="Primary textual content")
    
    # 4D Contexts
    temporal_context: TemporalContext
    semantic_context: SemanticContext
    conversational_context: Optional[ConversationalContext] = None
    workflow_context: Optional[WorkflowContext] = None
    
    # Embedding Information
    embedding: List[float] = Field(default_factory=list)
    embedding_model: str = "default"
    embedding_dimension: int = 384
    
    # Memory Relationships
    parent_memories: List[str] = Field(default_factory=list)
    child_memories: List[str] = Field(default_factory=list)
    related_memories: List[str] = Field(default_factory=list)
    
    # Evolution Tracking
    version: int = 1
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)
    access_count: int = 0
    last_accessed: Optional[datetime] = None
    
    # Importance and Retention
    importance_score: float = 0.5
    decay_factor: float = 1.0
    retention_strength: float = 1.0
    
    # Metadata
    source: str = "system"
    confidence: float = 1.0
    tags: List[str] = Field(default_factory=list)
    metadata: Dict[str, Any] = Field(default_factory=dict)


@dataclass
class MemoryQuery:
    """
    Advanced query structure for the unified memory system
    Supports temporal, semantic, and contextual search
    """
    
    # Text/Semantic Query
    text_query: Optional[str] = None
    semantic_similarity_threshold: float = 0.7
    
    # Temporal Constraints
    time_range: Optional[Tuple[datetime, datetime]] = None
    relative_time: Optional[str] = None  # "last week", "yesterday"
    temporal_precision: str = "exact"
    
    # Type and Scope Filters
    memory_types: List[MemoryType] = field(default_factory=list)
    memory_scopes: List[MemoryScope] = field(default_factory=list)
    
    # Content Filters
    topics: List[str] = field(default_factory=list)
    entities: List[str] = field(default_factory=list)
    speakers: List[str] = field(default_factory=list)
    
    # Relationship Queries
    related_to_memory: Optional[str] = None
    conversation_id: Optional[str] = None
    workflow_id: Optional[str] = None
    
    # Result Configuration
    max_results: int = 10
    sort_by: str = "relevance"  # relevance, time, importance
    include_context: bool = True
    
    # Advanced Options
    fuzzy_temporal_search: bool = False
    cross_modal_search: bool = False
    include_related_memories: bool = False


@dataclass
class MemorySearchResult:
    """Rich search result with context and relationships"""
    memory: UnifiedMemory
    relevance_score: float
    temporal_distance: Optional[float] = None  # temporal relevance
    semantic_distance: Optional[float] = None  # semantic similarity
    context_matches: List[str] = field(default_factory=list)
    explanation: Optional[str] = None


@dataclass
class MemoryInsight:
    """Emergent insights from memory analysis"""
    insight_type: str
    description: str
    related_memories: List[str]
    confidence: float
    temporal_span: Optional[Tuple[datetime, datetime]] = None
    supporting_evidence: List[str] = field(default_factory=list)


class MemoryTensorConfiguration(BaseModel):
    """Configuration for the enhanced tensor calendar memory system"""
    
    # Vector Store Configuration
    collection_name: str = "unified_memory"
    embedding_dimension: int = 384
    distance_metric: str = "cosine"
    
    # Memory Management
    max_memories: int = 1000000
    retention_policy: str = "importance_based"
    decay_enabled: bool = True
    auto_consolidation: bool = True
    
    # Temporal Configuration
    temporal_resolution: str = "microsecond"
    timezone: str = "UTC"
    relative_time_window: timedelta = timedelta(days=30)
    
    # Search Configuration
    default_similarity_threshold: float = 0.7
    max_search_results: int = 100
    enable_fuzzy_search: bool = True
    
    # Insight Generation
    enable_insight_generation: bool = True
    insight_generation_interval: timedelta = timedelta(hours=1)
    min_insight_confidence: float = 0.6
    
    # Performance
    batch_size: int = 100
    cache_size: int = 10000
    async_processing: bool = True
