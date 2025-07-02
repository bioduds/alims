import React from 'react';
import { ClusteringResult, ClusteringAlgorithm } from "../types/alims";

interface ClusteringResultsProps {
  results: {
    [key in ClusteringAlgorithm]?: ClusteringResult;
  };
}

const ClusteringResults: React.FC<ClusteringResultsProps> = ({ results }) => {
  // Find the best result based on silhouette score
  const bestResult = Object.values(results).reduce((best, current) => {
    if (!best) return current;
    if (!current) return best;
    return current.silhouette_score > best.silhouette_score ? current : best;
  }, undefined as ClusteringResult | undefined);

  if (!bestResult) {
    return (
      <div className="bg-white dark:bg-gray-800 rounded-lg shadow-lg p-6">
        <h2 className="text-2xl font-semibold text-gray-800 dark:text-white mb-6">
          Clustering Results
        </h2>
        <div className="text-gray-500 dark:text-gray-400">
          No clustering results available
        </div>
      </div>
    );
  }

  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg shadow-lg p-6">
      <h2 className="text-2xl font-semibold text-gray-800 dark:text-white mb-6">
        Clustering Results
      </h2>

    <div className="space-y-6">
        {/* Algorithm Info */}
        <div>
          <h3 className="text-lg font-medium text-gray-700 dark:text-gray-300 mb-4">
            Algorithm Details
        </h3>
          <div className="grid grid-cols-2 gap-4">
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Algorithm
            </div>
              <div className="mt-2">
                <span className="text-xl font-semibold text-gray-800 dark:text-white">
                  {bestResult.algorithm}
                </span>
          </div>
            </div>
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Number of Clusters
          </div>
              <div className="mt-2">
                <span className="text-xl font-semibold text-gray-800 dark:text-white">
                  {bestResult.n_clusters}
                </span>
          </div>
          </div>
        </div>
      </div>

        {/* Metrics */}
        <div>
          <h3 className="text-lg font-medium text-gray-700 dark:text-gray-300 mb-4">
            Quality Metrics
        </h3>
          <div className="grid grid-cols-2 gap-4">
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Silhouette Score
        </div>
              <div className="mt-2">
                <span className="text-xl font-semibold text-gray-800 dark:text-white">
                  {bestResult.silhouette_score.toFixed(3)}
                </span>
              </div>
                </div>
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Calinski-Harabasz Score
                </div>
              <div className="mt-2">
                <span className="text-xl font-semibold text-gray-800 dark:text-white">
                  {bestResult.calinski_harabasz_score.toFixed(1)}
                </span>
              </div>
            </div>
        </div>
      </div>

        {/* Clusters */}
        <div>
          <h3 className="text-lg font-medium text-gray-700 dark:text-gray-300 mb-4">
            Cluster Analysis
          </h3>
          <div className="space-y-4">
            {Object.entries(bestResult.cluster_analysis).map(([id, cluster]) => (
              <div key={id} className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
                <div className="flex justify-between items-center mb-4">
                  <div className="text-lg font-medium text-gray-800 dark:text-white">
                    Cluster {parseInt(id) + 1}
                  </div>
                  <div className="text-sm text-gray-500 dark:text-gray-400">
                    {cluster.percentage.toFixed(1)}% of data
              </div>
            </div>

                {/* Event Types */}
                <div className="mb-4">
                  <div className="text-sm text-gray-500 dark:text-gray-400 mb-2">
                    Event Types
                  </div>
                  <div className="grid grid-cols-2 gap-2">
                    {Object.entries(cluster.event_types).map(([type, count]) => (
                      <div key={type} className="flex justify-between">
                        <span className="text-gray-700 dark:text-gray-300">
                          {type}
                      </span>
                        <span className="text-gray-600 dark:text-gray-400">
                          {count.toLocaleString()}
                        </span>
                      </div>
                    ))}
                  </div>
                </div>

                {/* Time Pattern */}
                <div>
                  <div className="text-sm text-gray-500 dark:text-gray-400 mb-2">
                    Time Pattern
                  </div>
                  <div className="grid grid-cols-2 gap-2">
                    <div className="flex justify-between">
                      <span className="text-gray-700 dark:text-gray-300">
                        Peak Hour
                      </span>
                      <span className="text-gray-600 dark:text-gray-400">
                        {cluster.time_pattern.peak_hour}:00
                      </span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-gray-700 dark:text-gray-300">
                        Peak Day
                      </span>
                      <span className="text-gray-600 dark:text-gray-400">
                        {cluster.time_pattern.peak_day}
                          </span>
                    </div>
                  </div>
                </div>
              </div>
            ))}
          </div>
        </div>

        {/* Description */}
        <div className="text-gray-700 dark:text-gray-300">
          {bestResult.description}
        </div>
      </div>
    </div>
  );
};

export default ClusteringResults; 