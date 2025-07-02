import React from 'react';
import { DashboardProps } from '../types/alims';
import SystemOverview from './SystemOverview';
import ClusteringResults from './ClusteringResults';
import PatternEvolution from './PatternEvolution';
import RecommendationsPanel from './RecommendationsPanel';

const Dashboard: React.FC<DashboardProps> = ({ analysisData, systemMetrics }) => {
  return (
    <div className="grid grid-cols-12 gap-6">
      {/* System Overview */}
      <div className="col-span-12 lg:col-span-4">
        <SystemOverview metrics={systemMetrics} />
      </div>
          
      {/* Clustering Results */}
      <div className="col-span-12 lg:col-span-8">
        <ClusteringResults results={analysisData.clustering_results} />
      </div>

      {/* Pattern Evolution */}
      <div className="col-span-12 lg:col-span-8">
        <PatternEvolution analysisData={analysisData} />
      </div>
          
      {/* Recommendations */}
      <div className="col-span-12 lg:col-span-4">
        <RecommendationsPanel 
          recommendations={[
            {
              priority: 'HIGH',
              category: 'Performance',
              message: 'System optimization recommended',
              action_required: true,
              technical_details: 'Consider upgrading memory allocation for better performance'
            },
            {
              priority: 'MEDIUM',
              category: 'Security',
              message: 'Update security protocols',
              action_required: false
            }
          ]} 
          analysisId={analysisData.analysis_id}
        />
      </div>
    </div>
  );
};

export default Dashboard; 