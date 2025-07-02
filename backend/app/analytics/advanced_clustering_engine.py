#!/usr/bin/env python3
"""
Advanced Clustering Engine for ALims
Multi-algorithm clustering and pattern analysis for continuous learning pipeline
Enhanced with Pydantic models for type safety and validation
"""

import json
import sqlite3
import time
import uuid
from collections import Counter, defaultdict
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any

import numpy as np
import pandas as pd
from sklearn.cluster import KMeans, SpectralClustering
from sklearn.mixture import GaussianMixture
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import silhouette_score, calinski_harabasz_score
from sklearn.decomposition import PCA

try:
    import hdbscan
    HDBSCAN_AVAILABLE = True
except ImportError:
    HDBSCAN_AVAILABLE = False
    print("Warning: HDBSCAN not available. Install with: pip install hdbscan")

# Import our Pydantic models
from app.analytics.models import (
    AnalysisResults, AnalysisConfig, ClusteringResult, ClusteringAlgorithm,
    DataSummary, ConsensusResults, Recommendation, ClusterAnalysis,
    TimePattern, AlgorithmParams, AnalysisMetrics, EventData, FeatureVector,
    create_analysis_config, create_data_summary, create_clustering_result,
    create_consensus_results, create_recommendation
)


class AdvancedClusteringEngine:
    """Advanced clustering engine with multiple algorithms and Pydantic validation"""
    
    def __init__(self, db_path: str = "data/events.db", config: Optional[AnalysisConfig] = None):
        self.db_path = db_path
        self.config = config or create_analysis_config()
        self.last_analysis: Optional[AnalysisResults] = None
        self.analysis_cache: Dict[str, AnalysisResults] = {}
        self.feature_cache: Dict[str, FeatureVector] = {}
        
        # Clustering algorithms configuration with Pydantic models
        self.clusterers = {
            ClusteringAlgorithm.KMEANS: {
                'algorithm': KMeans,
                'params': AlgorithmParams(
                    n_clusters=8, 
                    random_state=42, 
                    n_init=10
                ),
                'description': 'K-Means clustering for spherical clusters'
            },
            ClusteringAlgorithm.SPECTRAL: {
                'algorithm': SpectralClustering,
                'params': AlgorithmParams(
                    n_clusters=8, 
                    random_state=42, 
                    affinity='rbf'
                ),
                'description': 'Spectral clustering for non-convex patterns'
            },
            ClusteringAlgorithm.GMM: {
                'algorithm': GaussianMixture,
                'params': AlgorithmParams(
                    n_components=8, 
                    random_state=42
                ),
                'description': 'Gaussian Mixture for probabilistic clustering'
            }
        }
        
        if HDBSCAN_AVAILABLE:
            self.clusterers[ClusteringAlgorithm.HDBSCAN] = {
                'algorithm': hdbscan.HDBSCAN,
                'params': AlgorithmParams(
                    min_cluster_size=50, 
                    min_samples=10
                ),
                'description': 'HDBSCAN for density-based clustering with noise detection'
            }
    
    def load_events_data(self, limit: Optional[int] = None, days_back: Optional[int] = None) -> pd.DataFrame:
        """Load recent events data for analysis using configuration"""
        # Use config defaults if not specified
        limit = limit or self.config.data_limit
        days_back = days_back or self.config.days_back
        
        try:
            conn = sqlite3.connect(self.db_path)
            
            # Get events from the last N days
            cutoff_date = datetime.now() - timedelta(days=days_back)
            cutoff_timestamp = cutoff_date.timestamp()
            
            query = """
                SELECT event_type, source, data_json, timestamp
                FROM events 
                WHERE timestamp > ? 
                ORDER BY timestamp DESC 
                LIMIT ?
            """
            
            df = pd.read_sql_query(query, conn, params=(cutoff_timestamp, limit))
            conn.close()
            
            print(f"✅ Loaded {len(df)} events from last {days_back} days (limit: {limit})")
            return df
            
        except Exception as e:
            print(f"❌ Error loading events: {e}")
            return pd.DataFrame()
    
    def extract_features(self, df: pd.DataFrame) -> np.ndarray:
        """Extract numerical features from events data"""
        if df.empty:
            return np.array([])
        
        features = []
        
        for _, row in df.iterrows():
            feature_vector = []
            
            # Basic features
            feature_vector.append(row['timestamp'])
            
            # Event type encoding (one-hot style)
            event_types = ['file_op', 'app_event', 'system_event', 'user_action']
            for et in event_types:
                feature_vector.append(1 if row['event_type'] == et else 0)
            
            # Source encoding (hash to keep it numerical)
            source_hash = hash(str(row['source'])) % 1000
            feature_vector.append(source_hash)
            
            # Data features from JSON
            try:
                if pd.notna(row['data_json']):
                    data = json.loads(row['data_json'])
                    
                    # File operation features
                    if 'action' in data:
                        actions = ['create', 'modify', 'delete', 'read', 'move']
                        for action in actions:
                            feature_vector.append(1 if data['action'] == action else 0)
                    else:
                        feature_vector.extend([0] * 5)  # Pad with zeros
                    
                    # File extension features
                    if 'ext' in data and data['ext']:
                        ext_hash = hash(data['ext']) % 100
                        feature_vector.append(ext_hash)
                    else:
                        feature_vector.append(0)
                    
                    # Path depth (simple measure of file organization)
                    if 'path' in data:
                        depth = str(data['path']).count('/')
                        feature_vector.append(min(depth, 20))  # Cap at 20
                    else:
                        feature_vector.append(0)
                else:
                    feature_vector.extend([0] * 7)  # Pad for missing data features
                    
            except:
                feature_vector.extend([0] * 7)  # Pad for invalid JSON
            
            # Time-based features
            dt = datetime.fromtimestamp(row['timestamp'])
            feature_vector.append(dt.hour)  # Hour of day
            feature_vector.append(dt.weekday())  # Day of week
            
            features.append(feature_vector)
        
        return np.array(features)
    
    def perform_clustering_analysis(self, force_new: bool = False) -> AnalysisResults:
        """Perform comprehensive clustering analysis with Pydantic validation"""
        start_time = time.time()
        analysis_id = str(uuid.uuid4())
        
        print(f"🔍 Starting clustering analysis (ID: {analysis_id[:8]}...)...")
        
        # Check cache if not forcing new analysis
        cache_key = f"analysis_{int(time.time() // self.config.cache_duration_hours // 3600)}"
        if not force_new and cache_key in self.analysis_cache:
            print("📋 Using cached analysis results")
            return self.analysis_cache[cache_key]
        
        try:
            # Load data
            df = self.load_events_data(
                limit=self.config.data_limit, 
                days_back=self.config.days_back
            )
            
            if df.empty:
                return AnalysisResults(
                    analysis_id=analysis_id,
                    data_summary=create_data_summary(0, {}, {}),
                    consensus=create_consensus_results(None, -1, 0, False, 0),
                    error="No data available for analysis"
                )
            
            if len(df) < self.config.min_events_for_analysis:
                return AnalysisResults(
                    analysis_id=analysis_id,
                    data_summary=create_data_summary(len(df), {}, {}),
                    consensus=create_consensus_results(None, -1, 0, False, 0),
                    error=f"Insufficient data for analysis (need {self.config.min_events_for_analysis}, got {len(df)})"
                )
            
            # Extract features
            features = self.extract_features(df)
            if features.size == 0:
                return AnalysisResults(
                    analysis_id=analysis_id,
                    data_summary=create_data_summary(len(df), {}, {}),
                    consensus=create_consensus_results(None, -1, 0, False, 0),
                    error="No features could be extracted"
                )
            
            # Normalize features if configured
            if self.config.feature_scaling and features.shape[0] > 1:
                scaler = StandardScaler()
                features_scaled = scaler.fit_transform(features)
            else:
                features_scaled = features
                
            if features_scaled.shape[0] < 2:
                return AnalysisResults(
                    analysis_id=analysis_id,
                    data_summary=create_data_summary(len(df), {}, {}),
                    consensus=create_consensus_results(None, -1, 0, False, 0),
                    error="Insufficient data for clustering (need at least 2 samples)"
                )
        
            # Create data summary with validation
            data_summary = create_data_summary(
                total_events=len(df),
                event_types=dict(df['event_type'].value_counts()),
                time_range={
                    'start': datetime.fromtimestamp(df['timestamp'].min()).isoformat(),
                    'end': datetime.fromtimestamp(df['timestamp'].max()).isoformat()
                }
            )
            
            # Store clustering results
            clustering_results: Dict[ClusteringAlgorithm, ClusteringResult] = {}
            algorithms_completed = 0
            
            # Run configured clustering algorithms
            for algorithm in self.config.algorithms:
                if algorithm not in self.clusterers:
                    print(f"  ⚠️ Algorithm {algorithm} not available, skipping")
                    continue
                    
                try:
                    print(f"  🔬 Running {algorithm.value.upper()} clustering...")
                    
                    config = self.clusterers[algorithm]
                    params_dict = config['params'].dict()
                    
                    # Create and fit clusterer with proper parameter mapping
                    if algorithm == ClusteringAlgorithm.GMM:
                        # GMM uses n_components instead of n_clusters
                        if 'n_clusters' in params_dict:
                            params_dict['n_components'] = params_dict.pop('n_clusters')
                        clusterer = config['algorithm'](**{k: v for k, v in params_dict.items() if v is not None})
                        labels = clusterer.fit_predict(features_scaled)
                    else:
                        clusterer = config['algorithm'](**{k: v for k, v in params_dict.items() if v is not None})
                        labels = clusterer.fit_predict(features_scaled)
                    
                    # Calculate metrics
                    n_clusters = len(set(labels)) - (1 if -1 in labels else 0)
                    
                    if n_clusters > 1 and len(set(labels)) > 1:
                        silhouette = silhouette_score(features_scaled, labels)
                        calinski = calinski_harabasz_score(features_scaled, labels)
                    else:
                        silhouette = -1.0
                        calinski = 0.0
                    
                    # Analyze clusters
                    cluster_analysis = self._analyze_clusters(df, labels)
                    
                    # Create validated clustering result
                    clustering_result = create_clustering_result(
                        algorithm=algorithm,
                        n_clusters=n_clusters,
                        silhouette_score=float(silhouette),
                        calinski_harabasz_score=float(calinski),
                        algorithm_params=config['params'],
                        description=config['description'],
                        cluster_analysis=cluster_analysis,
                        labels=labels.tolist()
                    )
                    
                    clustering_results[algorithm] = clustering_result
                    algorithms_completed += 1
                    
                except Exception as e:
                    print(f"  ❌ Error in {algorithm.value} clustering: {e}")
                    # Create error result
                    clustering_results[algorithm] = ClusteringResult(
                        algorithm=algorithm,
                        n_clusters=0,
                        silhouette_score=-1.0,
                        calinski_harabasz_score=0.0,
                        algorithm_params=AlgorithmParams(),
                        description=self.clusterers[algorithm]['description'],
                        error=str(e)
                    )
            
            # Generate consensus and recommendations
            consensus = self._generate_consensus_validated(clustering_results)
            recommendations = self._generate_recommendations_validated(data_summary, consensus, clustering_results)
            
            # Calculate analysis duration
            analysis_duration = time.time() - start_time
            
            # Create final validated results
            results = AnalysisResults(
                analysis_id=analysis_id,
                data_summary=data_summary,
                clustering_results=clustering_results,
                consensus=consensus,
                recommendations=recommendations,
                analysis_duration_seconds=analysis_duration
            )
            
            # Cache results
            self.analysis_cache[cache_key] = results
            self.last_analysis = results
            
            print(f"✅ Clustering analysis complete! ({analysis_duration:.2f}s)")
            return results
            
        except Exception as e:
            print(f"❌ Critical error during clustering analysis: {e}")
            return AnalysisResults(
                analysis_id=analysis_id,
                data_summary=create_data_summary(0, {}, {}),
                consensus=create_consensus_results(None, -1, 0, False, 0),
                error=f"Critical error: {str(e)}"
            )
    
    def _analyze_clusters(self, df: pd.DataFrame, labels: np.ndarray) -> Dict[str, ClusterAnalysis]:
        """Analyze the content of each cluster with Pydantic validation"""
        cluster_analysis = {}
        
        # Add cluster labels to dataframe
        df_with_labels = df.copy()
        df_with_labels['cluster'] = labels
        
        for cluster_id in set(labels):
            if cluster_id == -1:  # Noise cluster in HDBSCAN
                cluster_name = 'noise'
            else:
                cluster_name = f'cluster_{cluster_id}'
            
            cluster_data = df_with_labels[df_with_labels['cluster'] == cluster_id]
            
            # Create validated time pattern
            time_pattern = self._analyze_time_pattern_validated(cluster_data)
            
            # Create validated cluster analysis
            analysis = ClusterAnalysis(
                size=len(cluster_data),
                percentage=len(cluster_data) / len(df) * 100,
                event_types=dict(cluster_data['event_type'].value_counts()),
                top_sources=dict(cluster_data['source'].value_counts().head(5)),
                time_pattern=time_pattern,
                dominant_pattern=self._identify_dominant_pattern(cluster_data)
            )
            
            cluster_analysis[cluster_name] = analysis
        
        return cluster_analysis
    
    def _analyze_time_pattern_validated(self, cluster_data: pd.DataFrame) -> TimePattern:
        """Analyze temporal patterns in cluster with Pydantic validation"""
        if cluster_data.empty:
            return TimePattern()
        
        # Convert timestamps to datetime
        times = pd.to_datetime(cluster_data['timestamp'], unit='s')
        
        return TimePattern(
            peak_hour=int(times.dt.hour.mode().iloc[0]) if not times.empty else None,
            peak_day=str(times.dt.day_name().mode().iloc[0]) if not times.empty else None,
            activity_spread={
                'hours': int(times.dt.hour.nunique()),
                'days': int(times.dt.date.nunique())
            }
        )
    
    def _analyze_time_pattern(self, cluster_data: pd.DataFrame) -> Dict[str, Any]:
        """Legacy method for backward compatibility"""
        pattern = self._analyze_time_pattern_validated(cluster_data)
        return pattern.dict()
    
    def _identify_dominant_pattern(self, cluster_data: pd.DataFrame) -> str:
        """Identify the dominant pattern in a cluster"""
        if cluster_data.empty:
            return "empty_cluster"
        
        # Most common event type
        top_event_type = cluster_data['event_type'].mode().iloc[0] if not cluster_data.empty else "unknown"
        
        # Most common source
        top_source = cluster_data['source'].mode().iloc[0] if not cluster_data.empty else "unknown"
        
        # Simple pattern classification
        if "file" in top_event_type.lower():
            return f"file_operations_{top_source}"
        elif "app" in top_event_type.lower():
            return f"application_usage_{top_source}"
        else:
            return f"general_activity_{top_event_type}"
    
    def _generate_consensus(self, clustering_results: Dict[str, Any]) -> Dict[str, Any]:
        """Generate consensus from multiple clustering results"""
        if not clustering_results:
            return {}
        
        # Find best performing algorithm
        best_algorithm = None
        best_score = -1
        
        for name, result in clustering_results.items():
            if 'error' not in result and result.get('silhouette_score', -1) > best_score:
                best_score = result['silhouette_score']
                best_algorithm = name
        
        # Calculate average number of clusters
        cluster_counts = [result.get('n_clusters', 0) for result in clustering_results.values() 
                         if 'error' not in result]
        avg_clusters = np.mean(cluster_counts) if cluster_counts else 0
        
        return {
            'best_algorithm': best_algorithm,
            'best_silhouette_score': best_score,
            'average_clusters': avg_clusters,
            'algorithm_agreement': len(set(cluster_counts)) <= 2,  # Algorithms roughly agree
            'consensus_clusters': int(np.median(cluster_counts)) if cluster_counts else 0
        }
    
    def _generate_consensus_validated(self, clustering_results: Dict[ClusteringAlgorithm, ClusteringResult]) -> ConsensusResults:
        """Generate consensus analysis across algorithms with Pydantic validation"""
        valid_results = {k: v for k, v in clustering_results.items() if v.error is None}
        
        if not valid_results:
            return create_consensus_results(None, -1.0, 0.0, False, 0)
        
        # Find best algorithm by silhouette score
        best_algorithm = max(valid_results.keys(), 
                           key=lambda x: valid_results[x].silhouette_score)
        best_score = valid_results[best_algorithm].silhouette_score
        
        # Calculate average number of clusters
        avg_clusters = sum(v.n_clusters for v in valid_results.values()) / len(valid_results)
        
        # Check if algorithms agree (within reasonable range)
        clusters_list = [v.n_clusters for v in valid_results.values()]
        cluster_range = max(clusters_list) - min(clusters_list) if clusters_list else 0
        agreement = cluster_range <= 2  # Algorithms agree if within 2 clusters
        
        return create_consensus_results(
            best_algorithm=best_algorithm,
            best_silhouette_score=best_score,
            average_clusters=avg_clusters,
            algorithm_agreement=agreement,
            consensus_clusters=int(avg_clusters)
        )
    
    def _generate_recommendations_validated(self, data_summary: DataSummary, consensus: ConsensusResults, 
                                          clustering_results: Dict[ClusteringAlgorithm, ClusteringResult]) -> List[Recommendation]:
        """Generate recommendations with Pydantic validation"""
        recommendations = []
        
        # Data quality recommendations
        if data_summary.total_events < 1000:
            recommendations.append(create_recommendation(
                priority="medium",
                category="data_quality",
                message="Consider collecting more data for better clustering results",
                action_required=False,
                technical_details=f"Current data: {data_summary.total_events} events, recommended: 1000+"
            ))
        
        # Algorithm performance recommendations
        if consensus.best_silhouette_score < 0.3:
            recommendations.append(create_recommendation(
                priority="high",
                category="performance",
                message="Poor clustering quality detected - consider parameter tuning",
                action_required=True,
                technical_details=f"Best silhouette score: {consensus.best_silhouette_score:.3f}"
            ))
        
        # Consensus recommendations
        if not consensus.algorithm_agreement:
            recommendations.append(create_recommendation(
                priority="medium",
                category="consensus",
                message="Algorithms disagree on cluster count - results may be unstable",
                action_required=False,
                technical_details=f"Cluster count range varies significantly across algorithms"
            ))
        
        # Success case
        if consensus.best_silhouette_score > 0.5 and consensus.algorithm_agreement:
            recommendations.append(create_recommendation(
                priority="low",
                category="success",
                message="Excellent clustering results - patterns are clear and consistent",
                action_required=False,
                technical_details=f"High silhouette score: {consensus.best_silhouette_score:.3f}"
            ))
        
        return recommendations
    
    def _generate_recommendations(self, results: Dict[str, Any]) -> List[str]:
        """Generate recommendations based on analysis"""
        recommendations = []
        
        consensus = results.get('consensus', {})
        best_algo = consensus.get('best_algorithm')
        
        if best_algo:
            recommendations.append(f"✅ Best clustering: {best_algo.upper()} with silhouette score {consensus.get('best_silhouette_score', 0):.3f}")
        
        # Check for specialization opportunities
        if consensus.get('consensus_clusters', 0) >= 3:
            recommendations.append(f"🤖 {consensus.get('consensus_clusters')} distinct patterns found - good for micro-agent specialization")
        
        # Data quality recommendations
        total_events = results.get('data_summary', {}).get('total_events', 0)
        if total_events < 1000:
            recommendations.append("⚠️ More data needed for robust clustering (current: {total_events})")
        elif total_events > 5000:
            recommendations.append("✅ Sufficient data for reliable pattern detection")
        
        return recommendations
    
    def get_summary_for_tray(self) -> str:
        """Get a brief summary suitable for tray display"""
        if not self.last_analysis:
            return "No analysis available"
        
        consensus = self.last_analysis.consensus
        n_clusters = consensus.consensus_clusters
        best_algo = consensus.best_algorithm.value if consensus.best_algorithm else 'unknown'
        
        return f"{n_clusters} patterns found ({best_algo.upper()})"
    
    def get_detailed_summary(self) -> str:
        """Get detailed summary for display windows"""
        if not self.last_analysis:
            return "No analysis results available. Run clustering analysis first."
        
        summary = []
        summary.append("🔍 CLUSTERING ANALYSIS RESULTS")
        summary.append("=" * 40)
        
        # Data summary
        data_sum = self.last_analysis.data_summary
        summary.append(f"📊 Data: {data_sum.total_events} events analyzed")
        
        # Best algorithm
        consensus = self.last_analysis.consensus
        best_algo = consensus.best_algorithm.value if consensus.best_algorithm else 'none'
        best_score = consensus.best_silhouette_score
        
        summary.append(f"🏆 Best: {best_algo.upper()} (score: {best_score:.3f})")
        summary.append(f"🧬 Patterns: {consensus.consensus_clusters} distinct clusters")
        
        # Recommendations
        recommendations = self.last_analysis.recommendations
        if recommendations:
            summary.append("\n💡 RECOMMENDATIONS:")
            for rec in recommendations:
                summary.append(f"  [{rec.priority.upper()}] {rec.message}")
        
        return "\n".join(summary)
    
    def get_analysis_results(self) -> Optional[AnalysisResults]:
        """Get the last analysis results as a Pydantic model"""
        return self.last_analysis
    
    def export_results_json(self, filepath: str) -> bool:
        """Export analysis results to JSON file"""
        if not self.last_analysis:
            return False
        
        try:
            with open(filepath, 'w') as f:
                f.write(self.last_analysis.json(indent=2))
            return True
        except Exception as e:
            print(f"Error exporting results: {e}")
            return False 