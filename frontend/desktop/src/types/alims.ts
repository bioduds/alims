// TypeScript types matching our Pydantic models

export enum ClusteringAlgorithm {
  KMEANS = "kmeans",
  SPECTRAL = "spectral",
  GMM = "gmm",
  HDBSCAN = "hdbscan"
}

export enum EventType {
  FILE_OP = "file_op",
  APP_EVENT = "app_event",
  SYSTEM_EVENT = "system_event",
  USER_ACTION = "user_action"
}

export interface TimePattern {
  peak_hour: number;
  peak_day: string;
  activity_spread: {
    [key: string]: number;
  };
}

export interface ClusterAnalysis {
  size: number;
  percentage: number;
  event_types: {
    [key: string]: number;
  };
  top_sources: {
    [key: string]: number;
  };
  time_pattern: TimePattern;
  dominant_pattern?: string;
}

export interface AlgorithmParams {
  n_clusters?: number;
  min_cluster_size?: number;
  min_samples?: number;
  random_state?: number;
  affinity?: string;
  n_components?: number;
  n_init?: number;
}

export interface ClusteringResult {
  algorithm: ClusteringAlgorithm;
  n_clusters: number;
  silhouette_score: number;
  calinski_harabasz_score: number;
  algorithm_params: {
    [key: string]: any;
  };
  description: string;
  cluster_analysis: {
    [key: string]: ClusterAnalysis;
  };
}

export interface DataSummary {
  total_events: number;
  event_types: Record<string, number>;
  time_range: Record<string, string>;
  data_quality_score?: number;
}

export interface ConsensusResults {
  best_algorithm?: ClusteringAlgorithm;
  best_silhouette_score: number;
  average_clusters: number;
  algorithm_agreement: boolean;
  consensus_clusters: number;
  confidence_score?: number;
}

export interface Recommendation {
  priority: string;
  category: string;
  message: string;
  action_required: boolean;
  technical_details?: string;
}

export interface AnalysisResults {
  timestamp: string;
  analysis_id: string;
  data_summary: {
    total_events: number;
    event_types: {
      [key: string]: number;
    };
    time_range: {
      start: string;
      end: string;
    };
    data_quality_score: number;
  };
  clustering_results: {
    [key in ClusteringAlgorithm]?: ClusteringResult;
  };
}

export interface AnalysisConfig {
  data_limit: number;
  days_back: number;
  algorithms: ClusteringAlgorithm[];
  cache_duration_hours: number;
  min_events_for_analysis: number;
  feature_scaling: boolean;
}

// UI-specific types
export interface SystemMetrics {
  timestamp: string;
  cpu_usage: number;
  memory_usage: number;
  disk_usage: {
    total: number;
    used: number;
    free: number;
  };
  network: {
    bytes_sent: number;
    bytes_received: number;
    connections: number;
  };
  process_stats: {
    total_processes: number;
    active_agents: number;
    embryos: number;
  };
  events_per_second: number;
}

export interface ChartDataPoint {
  name: string;
  value: number;
  color?: string;
}

export interface PatternEvolutionPoint {
  timestamp: string;
  pattern_count: number;
  confidence: number;
  algorithm: ClusteringAlgorithm;
}

export interface DashboardProps {
  analysisData: AnalysisResults;
  systemMetrics: SystemMetrics;
}

export interface SystemOverviewProps {
  metrics: SystemMetrics;
}

export interface ClusteringResultsProps {
  results: {
    [key in ClusteringAlgorithm]?: ClusteringResult;
  };
}

export interface PatternEvolutionProps {
  analysisData: AnalysisResults | null;
}

export interface RecommendationsPanelProps {
  recommendations: Recommendation[];
  analysisId: string;
}

// Chat-related types
export interface Message {
  role: 'user' | 'assistant';
  content: string;
  timestamp: string;
  agent_name?: string;
  specialization?: string;
  confidence?: number;
  suggested_actions?: string[];
}

export interface ChatResponse {
  session_id: string;
  response: {
    content: string;
    agent_name: string;
    specialization: string;
    confidence: number;
    suggested_actions: string[];
  };
  error?: string;
}

export interface ChatProps {
  className?: string;
}

export interface ChatSession {
  session_id: string;
  start_time: number;
  duration: number;
  message_count: number;
  active_agents: string[];
  messages: Message[];
} 