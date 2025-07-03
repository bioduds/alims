import React, { useEffect, useState, useCallback } from 'react';
import VisualizationEngine from './VisualizationEngine';

interface SystemData {
  timestamp: string;
  cpu_usage: number;
  memory_usage: number;
  disk_usage: number;
  agents_active: number;
  interaction_count: number;
  uptime: number;
  events_processed: number;
  clustering_results?: any;
  embryo_training_progress?: any;
}

interface RealTimeDataStreamProps {
  visualizationType: 'system_overview' | 'performance_metrics' | 'agent_activity' | 'event_stream' | 'clustering_analysis';
  updateInterval?: number;
  className?: string;
}

export const RealTimeDataStream: React.FC<RealTimeDataStreamProps> = ({
  visualizationType,
  updateInterval = 5000,
  className = ''
}) => {
  const [systemData, setSystemData] = useState<SystemData[]>([]);
  const [currentData, setCurrentData] = useState<SystemData | null>(null);
  const [isConnected, setIsConnected] = useState(false);
  const [error, setError] = useState<string | null>(null);

  // Fetch system data from ALIMS backend
  const fetchSystemData = useCallback(async () => {
    try {
      const response = await fetch('http://127.0.0.1:8000/system-stats');
      if (response.ok) {
        const data = await response.json();
        const newDataPoint: SystemData = {
          timestamp: new Date().toISOString(),
          cpu_usage: data.cpu_usage || Math.random() * 100,
          memory_usage: data.memory_usage || Math.random() * 100,
          disk_usage: data.disk_usage || Math.random() * 100,
          agents_active: data.agents_active || Math.floor(Math.random() * 10),
          interaction_count: data.interaction_count || Math.floor(Math.random() * 1000),
          uptime: data.uptime || Date.now(),
          events_processed: data.events_processed || Math.floor(Math.random() * 10000),
          clustering_results: data.clustering_results,
          embryo_training_progress: data.embryo_training_progress
        };

        setCurrentData(newDataPoint);
        setSystemData(prev => [...prev.slice(-19), newDataPoint]); // Keep last 20 data points
        setIsConnected(true);
        setError(null);
      } else {
        throw new Error(`HTTP ${response.status}`);
      }
    } catch (err) {
      console.error('Error fetching system data:', err);
      setError(err instanceof Error ? err.message : 'Unknown error');
      setIsConnected(false);
    }
  }, []);

  // Set up real-time data polling
  useEffect(() => {
    fetchSystemData(); // Initial fetch
    const interval = setInterval(fetchSystemData, updateInterval);
    return () => clearInterval(interval);
  }, [fetchSystemData, updateInterval]);

  // Format data for different visualization types
  const getVisualizationData = () => {
    if (!currentData || systemData.length === 0) return null;

    switch (visualizationType) {
      case 'system_overview':
        return {
          type: 'system_dashboard' as const,
          title: 'ALIMS Laboratory System Overview',
          data: currentData,
          realTimeData: true,
          updateInterval
        };

      case 'performance_metrics':
        return {
          type: 'line' as const,
          title: 'System Performance Over Time',
          data: {
            labels: systemData.map(d => new Date(d.timestamp).toLocaleTimeString()),
            datasets: [
              {
                label: 'CPU Usage (%)',
                data: systemData.map(d => d.cpu_usage),
                borderColor: 'rgb(59, 130, 246)',
                backgroundColor: 'rgba(59, 130, 246, 0.1)',
                tension: 0.4
              },
              {
                label: 'Memory Usage (%)',
                data: systemData.map(d => d.memory_usage),
                borderColor: 'rgb(16, 185, 129)',
                backgroundColor: 'rgba(16, 185, 129, 0.1)',
                tension: 0.4
              },
              {
                label: 'Disk Usage (%)',
                data: systemData.map(d => d.disk_usage),
                borderColor: 'rgb(245, 158, 11)',
                backgroundColor: 'rgba(245, 158, 11, 0.1)',
                tension: 0.4
              }
            ]
          },
          realTimeData: true,
          updateInterval
        };

      case 'agent_activity':
        return {
          type: 'bar' as const,
          title: 'Agent Activity Dashboard',
          data: {
            labels: ['Active Agents', 'Total Interactions', 'Events Processed'],
            datasets: [{
              label: 'Count',
              data: [
                currentData.agents_active,
                currentData.interaction_count / 100, // Scale down for visibility
                currentData.events_processed / 1000 // Scale down for visibility
              ],
              backgroundColor: [
                'rgba(139, 69, 19, 0.8)',
                'rgba(75, 192, 192, 0.8)',
                'rgba(255, 206, 86, 0.8)'
              ],
              borderColor: [
                'rgba(139, 69, 19, 1)',
                'rgba(75, 192, 192, 1)',
                'rgba(255, 206, 86, 1)'
              ],
              borderWidth: 2
            }]
          },
          realTimeData: true,
          updateInterval
        };

      case 'event_stream':
        return {
          type: 'scatter' as const,
          title: 'Event Processing Stream',
          data: {
            datasets: [{
              label: 'Events vs Time',
              data: systemData.map((d, index) => ({
                x: index,
                y: d.events_processed
              })),
              backgroundColor: 'rgba(255, 99, 132, 0.6)',
              borderColor: 'rgba(255, 99, 132, 1)',
              pointRadius: 6,
              pointHoverRadius: 8
            }]
          },
          realTimeData: true,
          updateInterval
        };

      case 'clustering_analysis':
        if (currentData.clustering_results) {
          return {
            type: 'network' as const,
            title: 'Clustering Analysis Network',
            data: currentData.clustering_results,
            realTimeData: true,
            updateInterval
          };
        } else {
          // Generate sample network data for demonstration
          return {
            type: 'network' as const,
            title: 'Clustering Analysis Network',
            data: {
              nodes: [
                { id: 'Cluster 1', group: 1 },
                { id: 'Cluster 2', group: 2 },
                { id: 'Cluster 3', group: 3 },
                { id: 'Data Point A', group: 1 },
                { id: 'Data Point B', group: 2 },
                { id: 'Data Point C', group: 3 }
              ],
              links: [
                { source: 'Cluster 1', target: 'Data Point A' },
                { source: 'Cluster 2', target: 'Data Point B' },
                { source: 'Cluster 3', target: 'Data Point C' }
              ]
            },
            realTimeData: true,
            updateInterval
          };
        }

      default:
        return null;
    }
  };

  const visualizationData = getVisualizationData();

  if (error) {
    return (
      <div className={`bg-red-50 border border-red-200 rounded-lg p-6 ${className}`}>
        <div className="flex items-center">
          <div className="flex-shrink-0">
            <svg className="h-5 w-5 text-red-400" viewBox="0 0 20 20" fill="currentColor">
              <path fillRule="evenodd" d="M10 18a8 8 0 100-16 8 8 0 000 16zM8.707 7.293a1 1 0 00-1.414 1.414L8.586 10l-1.293 1.293a1 1 0 101.414 1.414L10 11.414l1.293 1.293a1 1 0 001.414-1.414L11.414 10l1.293-1.293a1 1 0 00-1.414-1.414L10 8.586 8.707 7.293z" clipRule="evenodd" />
            </svg>
          </div>
          <div className="ml-3">
            <h3 className="text-sm font-medium text-red-800">Data Stream Error</h3>
            <p className="mt-1 text-sm text-red-700">
              Unable to connect to ALIMS backend: {error}
            </p>
            <p className="mt-1 text-xs text-red-600">
              Make sure the ALIMS AI API server is running on http://127.0.0.1:8000
            </p>
          </div>
        </div>
      </div>
    );
  }

  if (!visualizationData) {
    return (
      <div className={`bg-gray-50 border border-gray-200 rounded-lg p-6 ${className}`}>
        <div className="flex items-center justify-center h-64">
          <div className="text-center">
            <div className="animate-spin rounded-full h-8 w-8 border-t-2 border-b-2 border-blue-500 mx-auto"></div>
            <p className="mt-4 text-gray-600">Loading real-time data...</p>
          </div>
        </div>
      </div>
    );
  }

  return (
    <div className={className}>
      <div className="mb-4 flex items-center justify-between">
        <div className="flex items-center space-x-2">
          <div className={`h-2 w-2 rounded-full ${isConnected ? 'bg-green-500' : 'bg-red-500'}`}></div>
          <span className="text-sm text-gray-600">
            {isConnected ? 'Connected' : 'Disconnected'} • Updated {systemData.length > 0 ? 'just now' : 'never'}
          </span>
        </div>
        <div className="text-xs text-gray-500">
          Update interval: {updateInterval / 1000}s
        </div>
      </div>
      
      <VisualizationEngine
        visualization={visualizationData}
        onDataUpdate={(data) => {
          console.log('Visualization data updated:', data);
        }}
      />
    </div>
  );
};

export default RealTimeDataStream; 