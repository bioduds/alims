import React from 'react';
import { SystemOverviewProps } from '../types/alims';
import { cn } from '../utils/cn';

const SystemOverview: React.FC<SystemOverviewProps> = ({ metrics }) => {
  const formatBytes = (bytes: number) => {
    const units = ['B', 'KB', 'MB', 'GB', 'TB'];
    let value = bytes;
    let unitIndex = 0;
    
    while (value >= 1024 && unitIndex < units.length - 1) {
      value /= 1024;
      unitIndex++;
    }
    
    return `${value.toFixed(1)} ${units[unitIndex]}`;
  };

  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg shadow-lg p-6">
      <h2 className="text-2xl font-semibold text-gray-800 dark:text-white mb-6">
        System Overview
      </h2>

    <div className="space-y-6">
        {/* Resource Usage */}
        <div>
          <h3 className="text-lg font-medium text-gray-700 dark:text-gray-300 mb-4">
            Resource Usage
          </h3>
          <div className="grid grid-cols-2 gap-4">
            {/* CPU Usage */}
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                CPU Usage
              </div>
              <div className="mt-2 flex items-end">
                <span className="text-2xl font-semibold text-gray-800 dark:text-white">
                  {metrics.cpu_usage.toFixed(1)}%
                </span>
              </div>
              <div className="mt-2 h-2 bg-gray-200 dark:bg-gray-600 rounded-full">
                <div 
                  className={cn(
                    "h-full rounded-full",
                    metrics.cpu_usage > 80 ? "bg-red-500" :
                    metrics.cpu_usage > 60 ? "bg-yellow-500" :
                    "bg-green-500"
                  )}
                  style={{ width: `${metrics.cpu_usage}%` }}
                />
              </div>
          </div>

            {/* Memory Usage */}
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Memory Usage
                </div>
              <div className="mt-2">
                <span className="text-2xl font-semibold text-gray-800 dark:text-white">
                  {formatBytes(metrics.memory_usage)}
                </span>
              </div>
            </div>
          </div>
        </div>

        {/* Network Stats */}
        <div>
          <h3 className="text-lg font-medium text-gray-700 dark:text-gray-300 mb-4">
            Network Activity
          </h3>
          <div className="grid grid-cols-2 gap-4">
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Data Sent
              </div>
              <div className="mt-2">
                <span className="text-2xl font-semibold text-gray-800 dark:text-white">
                  {formatBytes(metrics.network.bytes_sent)}
                </span>
          </div>
                </div>
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Data Received
                </div>
              <div className="mt-2">
                <span className="text-2xl font-semibold text-gray-800 dark:text-white">
                  {formatBytes(metrics.network.bytes_received)}
                </span>
              </div>
            </div>
          </div>
        </div>

        {/* Process Stats */}
        <div>
          <h3 className="text-lg font-medium text-gray-700 dark:text-gray-300 mb-4">
            AI System Status
          </h3>
          <div className="grid grid-cols-3 gap-4">
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Active Agents
      </div>
              <div className="mt-2">
                <span className="text-2xl font-semibold text-gray-800 dark:text-white">
                  {metrics.process_stats.active_agents}
                </span>
              </div>
            </div>
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Embryos
              </div>
              <div className="mt-2">
                <span className="text-2xl font-semibold text-gray-800 dark:text-white">
                  {metrics.process_stats.embryos}
                </span>
              </div>
            </div>
            <div className="bg-gray-50 dark:bg-gray-700 rounded-lg p-4">
              <div className="text-sm text-gray-500 dark:text-gray-400">
                Events/s
              </div>
              <div className="mt-2">
                <span className="text-2xl font-semibold text-gray-800 dark:text-white">
                  {metrics.events_per_second.toFixed(1)}
                </span>
              </div>
            </div>
          </div>
        </div>

        {/* Last Update */}
        <div className="text-sm text-gray-500 dark:text-gray-400">
          Last Update: {new Date(metrics.timestamp).toLocaleString()}
      </div>
      </div>
    </div>
  );
};

export default SystemOverview; 