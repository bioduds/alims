import React, { useState, useEffect } from 'react';
import {
  Chart as ChartJS,
  CategoryScale,
  LinearScale,
  PointElement,
  LineElement,
  Title,
  Tooltip,
  Legend,
  ArcElement,
  BarElement,
} from 'chart.js';
import { Line, Doughnut, Bar } from 'react-chartjs-2';

ChartJS.register(
  CategoryScale,
  LinearScale,
  PointElement,
  LineElement,
  Title,
  Tooltip,
  Legend,
  ArcElement,
  BarElement
);

interface SystemMetrics {
  cpu_usage: number;
  memory_usage: number;
  memory_total: number;
  memory_used: number;
  disk_usage: number;
  disk_total: number;
  disk_used: number;
}

interface AIMetrics {
  uptime_seconds: number;
  uptime_formatted: string;
  active_agents: number;
  total_agents: number;
  interaction_count: number;
  avg_response_time: number;
  model_name: string;
  ollama_status: string;
}

interface SystemStatsData {
  timestamp: string;
  system_metrics: SystemMetrics;
  ai_metrics: AIMetrics;
  agents_status: Record<string, string>;
  performance_history: {
    response_times: number[];
    timestamps: string[];
  };
}

const SystemStatsDashboard: React.FC = () => {
  const [stats, setStats] = useState<SystemStatsData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const fetchSystemStats = async () => {
    try {
      const response = await fetch('http://127.0.0.1:8000/system-stats');
      if (response.ok) {
        const data: SystemStatsData = await response.json();
        setStats(data);
        setError(null);
      } else {
        setError('Failed to fetch system statistics');
      }
    } catch (err) {
      setError('Error connecting to ALIMS API');
      console.error('System stats fetch error:', err);
    } finally {
      setLoading(false);
    }
  };

  useEffect(() => {
    fetchSystemStats();
    const interval = setInterval(fetchSystemStats, 5000); // Update every 5 seconds
    return () => clearInterval(interval);
  }, []);

  if (loading) {
    return (
      <div className="h-full flex items-center justify-center">
        <div className="text-center">
          <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-400 mx-auto mb-4"></div>
          <p className="text-gray-400">Loading system statistics...</p>
        </div>
      </div>
    );
  }

  if (error || !stats) {
    return (
      <div className="h-full flex items-center justify-center">
        <div className="text-center text-red-400">
          <div className="text-4xl mb-4">⚠️</div>
          <p>{error || 'No system data available'}</p>
          <button 
            onClick={fetchSystemStats}
            className="mt-4 bg-blue-600 hover:bg-blue-700 px-4 py-2 rounded text-white"
          >
            Retry
          </button>
        </div>
      </div>
    );
  }

  // System resource usage chart data
  const systemUsageData = {
    labels: ['CPU', 'Memory', 'Disk'],
    datasets: [
      {
        label: 'Usage %',
        data: [stats.system_metrics.cpu_usage, stats.system_metrics.memory_usage, stats.system_metrics.disk_usage],
        backgroundColor: ['#EF4444', '#F59E0B', '#10B981'],
        borderColor: ['#DC2626', '#D97706', '#059669'],
        borderWidth: 2,
      },
    ],
  };

  // Agent status pie chart
  const agentStatusData = {
    labels: ['Active Agents', 'Inactive Agents'],
    datasets: [
      {
        data: [stats.ai_metrics.active_agents, stats.ai_metrics.total_agents - stats.ai_metrics.active_agents],
        backgroundColor: ['#10B981', '#6B7280'],
        borderColor: ['#059669', '#4B5563'],
        borderWidth: 2,
      },
    ],
  };

  // Response time history chart
  const responseTimeData = {
    labels: stats.performance_history.timestamps.map(ts => 
      new Date(ts).toLocaleTimeString()
    ),
    datasets: [
      {
        label: 'Response Time (s)',
        data: stats.performance_history.response_times,
        borderColor: '#3B82F6',
        backgroundColor: 'rgba(59, 130, 246, 0.1)',
        tension: 0.4,
        fill: true,
      },
    ],
  };

  const chartOptions = {
    responsive: true,
    maintainAspectRatio: false,
    plugins: {
      legend: {
        labels: {
          color: '#D1D5DB',
        },
      },
    },
    scales: {
      y: {
        ticks: {
          color: '#9CA3AF',
        },
        grid: {
          color: '#374151',
        },
      },
      x: {
        ticks: {
          color: '#9CA3AF',
        },
        grid: {
          color: '#374151',
        },
      },
    },
  };

  return (
    <div className="h-full p-6 bg-gradient-to-br from-gray-800 to-gray-900 overflow-auto">
      <div className="mb-6">
        <h2 className="text-2xl font-bold text-white mb-2">🖥️ System Statistics Dashboard</h2>
        <p className="text-gray-400">Real-time ALIMS laboratory system monitoring • Updated {new Date(stats.timestamp).toLocaleTimeString()}</p>
      </div>

      {/* Key Metrics Row */}
      <div className="grid grid-cols-4 gap-4 mb-6">
        <div className="bg-gray-800/50 rounded-lg p-4 border border-gray-600">
          <div className="text-2xl font-bold text-blue-400">{stats.system_metrics.cpu_usage}%</div>
          <div className="text-sm text-gray-400">CPU Usage</div>
        </div>
        <div className="bg-gray-800/50 rounded-lg p-4 border border-gray-600">
          <div className="text-2xl font-bold text-green-400">{stats.ai_metrics.active_agents}/{stats.ai_metrics.total_agents}</div>
          <div className="text-sm text-gray-400">Active Agents</div>
        </div>
        <div className="bg-gray-800/50 rounded-lg p-4 border border-gray-600">
          <div className="text-2xl font-bold text-purple-400">{stats.ai_metrics.avg_response_time}s</div>
          <div className="text-sm text-gray-400">Avg Response</div>
        </div>
        <div className="bg-gray-800/50 rounded-lg p-4 border border-gray-600">
          <div className="text-2xl font-bold text-yellow-400">{stats.ai_metrics.uptime_formatted}</div>
          <div className="text-sm text-gray-400">Uptime</div>
        </div>
      </div>

      {/* Charts Grid */}
      <div className="grid grid-cols-2 gap-6 mb-6">
        {/* System Resource Usage */}
        <div className="bg-gray-800/50 rounded-lg p-6 border border-gray-600">
          <h3 className="text-lg font-semibold text-white mb-4">System Resources</h3>
          <div className="h-48">
            <Bar data={systemUsageData} options={chartOptions} />
          </div>
        </div>

        {/* Agent Status */}
        <div className="bg-gray-800/50 rounded-lg p-6 border border-gray-600">
          <h3 className="text-lg font-semibold text-white mb-4">Agent Status</h3>
          <div className="h-48">
            <Doughnut 
              data={agentStatusData} 
              options={{
                ...chartOptions,
                plugins: {
                  ...chartOptions.plugins,
                  legend: {
                    ...chartOptions.plugins.legend,
                    position: 'bottom' as const,
                  },
                },
              }} 
            />
          </div>
        </div>
      </div>

      {/* Response Time History */}
      <div className="bg-gray-800/50 rounded-lg p-6 border border-gray-600 mb-6">
        <h3 className="text-lg font-semibold text-white mb-4">Response Time History</h3>
        <div className="h-48">
          <Line data={responseTimeData} options={chartOptions} />
        </div>
      </div>

      {/* Detailed Metrics */}
      <div className="grid grid-cols-2 gap-6">
        {/* System Details */}
        <div className="bg-gray-800/50 rounded-lg p-6 border border-gray-600">
          <h3 className="text-lg font-semibold text-white mb-4">System Details</h3>
          <div className="space-y-3 text-sm">
            <div className="flex justify-between">
              <span className="text-gray-400">Memory:</span>
              <span className="text-white">{stats.system_metrics.memory_used}GB / {stats.system_metrics.memory_total}GB</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-400">Disk:</span>
              <span className="text-white">{stats.system_metrics.disk_used}GB / {stats.system_metrics.disk_total}GB</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-400">Model:</span>
              <span className="text-cyan-400">{stats.ai_metrics.model_name}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-400">Ollama:</span>
              <span className={stats.ai_metrics.ollama_status === 'healthy' ? 'text-green-400' : 'text-red-400'}>
                {stats.ai_metrics.ollama_status}
              </span>
            </div>
          </div>
        </div>

        {/* Agent Details */}
        <div className="bg-gray-800/50 rounded-lg p-6 border border-gray-600">
          <h3 className="text-lg font-semibold text-white mb-4">Agent Status</h3>
          <div className="space-y-3 text-sm">
            {Object.entries(stats.agents_status).map(([agent, status]) => (
              <div key={agent} className="flex justify-between">
                <span className="text-gray-400 capitalize">{agent.replace('_', ' ')}:</span>
                <span className={status === 'active' ? 'text-green-400' : 'text-red-400'}>
                  {status}
                </span>
              </div>
            ))}
            <div className="flex justify-between pt-2 border-t border-gray-600">
              <span className="text-gray-400">Interactions:</span>
              <span className="text-white">{stats.ai_metrics.interaction_count}</span>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
};

export default SystemStatsDashboard; 