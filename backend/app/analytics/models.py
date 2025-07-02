#!/usr/bin/env python3
"""
Pydantic models for ALims clustering analysis
Provides type-safe data structures with validation
"""

from datetime import datetime
from typing import Dict, List, Optional, Any, Union
from enum import Enum

try:
    from pydantic import BaseModel, Field, validator, ConfigDict
    PYDANTIC_AVAILABLE = True
except ImportError:
    # Fallback for environments without Pydantic
    PYDANTIC_AVAILABLE = False
    
    class BaseModel:
        """Fallback BaseModel when Pydantic is not available"""
        def __init__(self, **kwargs):
            for key, value in kwargs.items():
                setattr(self, key, value)
        
        def dict(self):
            return {k: v for k, v in self.__dict__.items() if not k.startswith('_')}
        
        def json(self):
            import json
            return json.dumps(self.dict())


class ClusteringAlgorithm(str, Enum):
    """Supported clustering algorithms"""
    KMEANS = "kmeans"
    SPECTRAL = "spectral"
    GMM = "gmm"
    HDBSCAN = "hdbscan"


class EventType(str, Enum):
    """Event types in ALims"""
    FILE_OP = "file_op"
    APP_EVENT = "app_event"
    SYSTEM_EVENT = "system_event"
    USER_ACTION = "user_action"


class TimePattern(BaseModel):
    """Temporal pattern analysis for clusters"""
    peak_hour: Optional[int] = Field(None, ge=0, le=23, description="Peak activity hour (0-23)")
    peak_day: Optional[str] = Field(None, description="Peak activity day of week")
    activity_spread: Dict[str, int] = Field(default_factory=dict, description="Activity distribution metrics")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')


class ClusterAnalysis(BaseModel):
    """Analysis results for a single cluster"""
    size: int = Field(..., ge=0, description="Number of events in cluster")
    percentage: float = Field(..., ge=0, le=100, description="Percentage of total events")
    event_types: Dict[str, int] = Field(default_factory=dict, description="Event type distribution")
    top_sources: Dict[str, int] = Field(default_factory=dict, description="Most common event sources")
    time_pattern: TimePattern = Field(default_factory=TimePattern, description="Temporal patterns")
    dominant_pattern: str = Field(..., description="Identified dominant behavior pattern")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')


class AlgorithmParams(BaseModel):
    """Parameters for clustering algorithms"""
    n_clusters: Optional[int] = Field(None, ge=1, description="Number of clusters (for algorithms that require it)")
    min_cluster_size: Optional[int] = Field(None, ge=1, description="Minimum cluster size (for density-based algorithms)")
    min_samples: Optional[int] = Field(None, ge=1, description="Minimum samples parameter")
    random_state: Optional[int] = Field(42, description="Random state for reproducibility")
    affinity: Optional[str] = Field("rbf", description="Affinity parameter for spectral clustering")
    n_components: Optional[int] = Field(None, ge=1, description="Number of components (for GMM)")
    n_init: Optional[int] = Field(10, ge=1, description="Number of initializations (for K-means)")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='allow')  # Allow algorithm-specific parameters


class ClusteringResult(BaseModel):
    """Results from a single clustering algorithm"""
    algorithm: ClusteringAlgorithm = Field(..., description="Clustering algorithm used")
    n_clusters: int = Field(..., ge=0, description="Number of clusters found")
    silhouette_score: float = Field(..., ge=-1, le=1, description="Silhouette score (-1 to 1)")
    calinski_harabasz_score: float = Field(..., ge=0, description="Calinski-Harabasz score")
    algorithm_params: AlgorithmParams = Field(..., description="Parameters used for the algorithm")
    description: str = Field(..., description="Human-readable algorithm description")
    cluster_analysis: Dict[str, ClusterAnalysis] = Field(default_factory=dict, description="Per-cluster analysis")
    labels: List[int] = Field(default_factory=list, description="Cluster labels for each data point")
    error: Optional[str] = Field(None, description="Error message if clustering failed")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')
        
        @validator('silhouette_score')
        def validate_silhouette_score(cls, v):
            if not -1 <= v <= 1:
                raise ValueError('Silhouette score must be between -1 and 1')
            return v


class DataSummary(BaseModel):
    """Summary of input data for clustering"""
    total_events: int = Field(..., ge=0, description="Total number of events analyzed")
    event_types: Dict[str, int] = Field(default_factory=dict, description="Distribution of event types")
    time_range: Dict[str, str] = Field(default_factory=dict, description="Time range of data")
    data_quality_score: Optional[float] = Field(None, ge=0, le=1, description="Data quality assessment")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')


class ConsensusResults(BaseModel):
    """Consensus analysis across multiple clustering algorithms"""
    best_algorithm: Optional[ClusteringAlgorithm] = Field(None, description="Best performing algorithm")
    best_silhouette_score: float = Field(..., ge=-1, le=1, description="Best silhouette score achieved")
    average_clusters: float = Field(..., ge=0, description="Average number of clusters across algorithms")
    algorithm_agreement: bool = Field(..., description="Whether algorithms roughly agree on cluster count")
    consensus_clusters: int = Field(..., ge=0, description="Consensus number of clusters")
    confidence_score: Optional[float] = Field(None, ge=0, le=1, description="Confidence in consensus results")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')


class Recommendation(BaseModel):
    """A single recommendation from analysis"""
    priority: str = Field(..., description="Priority level (high, medium, low)")
    category: str = Field(..., description="Recommendation category")
    message: str = Field(..., description="Recommendation message")
    action_required: bool = Field(False, description="Whether user action is required")
    technical_details: Optional[str] = Field(None, description="Technical details for developers")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')


class AnalysisResults(BaseModel):
    """Complete clustering analysis results"""
    timestamp: datetime = Field(default_factory=datetime.now, description="When analysis was performed")
    analysis_id: str = Field(..., description="Unique identifier for this analysis")
    data_summary: DataSummary = Field(..., description="Summary of input data")
    clustering_results: Dict[ClusteringAlgorithm, ClusteringResult] = Field(
        default_factory=dict, 
        description="Results from each clustering algorithm"
    )
    consensus: ConsensusResults = Field(..., description="Consensus analysis across algorithms")
    recommendations: List[Recommendation] = Field(default_factory=list, description="Generated recommendations")
    analysis_duration_seconds: Optional[float] = Field(None, ge=0, description="Time taken for analysis")
    error: Optional[str] = Field(None, description="Global error message if analysis failed")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')
        
        @validator('clustering_results')
        def validate_clustering_results(cls, v):
            if not v:
                raise ValueError('At least one clustering result is required')
            return v


class AnalysisConfig(BaseModel):
    """Configuration for clustering analysis"""
    data_limit: int = Field(10000, ge=1, description="Maximum number of events to analyze")
    days_back: int = Field(7, ge=1, description="Number of days to look back for data")
    algorithms: List[ClusteringAlgorithm] = Field(
        default_factory=lambda: [ClusteringAlgorithm.KMEANS, ClusteringAlgorithm.SPECTRAL, ClusteringAlgorithm.GMM],
        description="Algorithms to run"
    )
    cache_duration_hours: int = Field(1, ge=0, description="How long to cache results (hours)")
    min_events_for_analysis: int = Field(10, ge=1, description="Minimum events required for analysis")
    feature_scaling: bool = Field(True, description="Whether to scale features before clustering")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')


class EventData(BaseModel):
    """Individual event data structure"""
    event_type: EventType = Field(..., description="Type of event")
    source: str = Field(..., description="Source of the event")
    timestamp: float = Field(..., gt=0, description="Unix timestamp")
    data_json: Optional[str] = Field(None, description="JSON data payload")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')


class FeatureVector(BaseModel):
    """Extracted feature vector for clustering"""
    event_id: Optional[str] = Field(None, description="Identifier for the source event")
    features: List[float] = Field(..., description="Numerical feature values")
    feature_names: List[str] = Field(default_factory=list, description="Names of features")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')
        
        @validator('features')
        def validate_features_not_empty(cls, v):
            if not v:
                raise ValueError('Feature vector cannot be empty')
            return v


class AnalysisMetrics(BaseModel):
    """Performance metrics for analysis"""
    events_processed: int = Field(..., ge=0, description="Number of events processed")
    features_extracted: int = Field(..., ge=0, description="Number of features extracted")
    algorithms_completed: int = Field(..., ge=0, description="Number of algorithms that completed successfully")
    total_algorithms: int = Field(..., ge=1, description="Total number of algorithms attempted")
    processing_time_seconds: float = Field(..., ge=0, description="Total processing time")
    memory_usage_mb: Optional[float] = Field(None, ge=0, description="Peak memory usage in MB")
    
    if PYDANTIC_AVAILABLE:
        model_config = ConfigDict(extra='forbid')
        
        @property
        def success_rate(self) -> float:
            """Calculate algorithm success rate"""
            return self.algorithms_completed / self.total_algorithms if self.total_algorithms > 0 else 0.0


# Factory functions for creating model instances with validation

def create_analysis_config(**kwargs) -> AnalysisConfig:
    """Create validated analysis configuration"""
    return AnalysisConfig(**kwargs)


def create_data_summary(total_events: int, event_types: Dict[str, int], time_range: Dict[str, str]) -> DataSummary:
    """Create validated data summary"""
    return DataSummary(
        total_events=total_events,
        event_types=event_types,
        time_range=time_range
    )


def create_clustering_result(
    algorithm: ClusteringAlgorithm,
    n_clusters: int,
    silhouette_score: float,
    calinski_harabasz_score: float,
    **kwargs
) -> ClusteringResult:
    """Create validated clustering result"""
    return ClusteringResult(
        algorithm=algorithm,
        n_clusters=n_clusters,
        silhouette_score=silhouette_score,
        calinski_harabasz_score=calinski_harabasz_score,
        **kwargs
    )


def create_consensus_results(
    best_algorithm: Optional[ClusteringAlgorithm],
    best_silhouette_score: float,
    average_clusters: float,
    algorithm_agreement: bool,
    consensus_clusters: int
) -> ConsensusResults:
    """Create validated consensus results"""
    return ConsensusResults(
        best_algorithm=best_algorithm,
        best_silhouette_score=best_silhouette_score,
        average_clusters=average_clusters,
        algorithm_agreement=algorithm_agreement,
        consensus_clusters=consensus_clusters
    )


def create_recommendation(priority: str, category: str, message: str, **kwargs) -> Recommendation:
    """Create validated recommendation"""
    return Recommendation(
        priority=priority,
        category=category,
        message=message,
        **kwargs
    )


# Type aliases for better readability
ClusteringResultsDict = Dict[ClusteringAlgorithm, ClusteringResult]
ClusterAnalysisDict = Dict[str, ClusterAnalysis]
RecommendationsList = List[Recommendation] 