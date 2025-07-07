import { cn } from '../utils/cn';

interface StageData {
  current_stage: string;
  stage_info: {
    title: string;
    description: string;
    icon: string;
    color: string;
  };
  progress: number;
  sample_status: Array<{
    id: string;
    status: string;
    priority: string;
    location: string;
    progress?: number;
  }>;
  available_actions: Array<{
    id: string;
    label: string;
    description: string;
    enabled: boolean;
    priority?: string;
  }>;
  next_steps: string[];
  tla_validation: Record<string, {
    status: string;
    message: string;
    confidence: number;
  }>;
  visual_elements: any;
  alerts: Array<{
    type: string;
    title: string;
    message: string;
  }>;
  context_summary?: string;
}

interface StageVisualizationProps {
  stageData: StageData | null;
  onActionClick?: (actionId: string) => void;
  className?: string;
}

export default function StageVisualization({ 
  stageData, 
  onActionClick, 
  className = '' 
}: StageVisualizationProps) {
  if (!stageData) {
    return (
      <div className={cn("p-4 bg-gray-50 dark:bg-gray-800 rounded-lg", className)}>
        <div className="text-center text-gray-500 dark:text-gray-400">
          <div className="text-2xl mb-2">🔬</div>
          <p>No stage data available</p>
        </div>
      </div>
    );
  }

  const { stage_info, progress, sample_status, available_actions, next_steps, tla_validation, alerts } = stageData;

  // Determine progress color
  const getProgressColor = (progress: number) => {
    if (progress < 30) return 'bg-red-500';
    if (progress < 70) return 'bg-yellow-500';
    return 'bg-green-500';
  };

  // Get status badge color
  const getStatusColor = (status: string) => {
    switch (status) {
      case 'PASS': return 'bg-green-100 text-green-800 dark:bg-green-900/20 dark:text-green-400';
      case 'WARNING': return 'bg-yellow-100 text-yellow-800 dark:bg-yellow-900/20 dark:text-yellow-400';
      case 'FAIL': return 'bg-red-100 text-red-800 dark:bg-red-900/20 dark:text-red-400';
      default: return 'bg-gray-100 text-gray-800 dark:bg-gray-900/20 dark:text-gray-400';
    }
  };

  // Get alert color
  const getAlertColor = (type: string) => {
    switch (type) {
      case 'error': return 'bg-red-50 border-red-200 text-red-800 dark:bg-red-900/20 dark:border-red-800 dark:text-red-400';
      case 'warning': return 'bg-yellow-50 border-yellow-200 text-yellow-800 dark:bg-yellow-900/20 dark:border-yellow-800 dark:text-yellow-400';
      case 'info': return 'bg-blue-50 border-blue-200 text-blue-800 dark:bg-blue-900/20 dark:border-blue-800 dark:text-blue-400';
      default: return 'bg-gray-50 border-gray-200 text-gray-800 dark:bg-gray-900/20 dark:border-gray-800 dark:text-gray-400';
    }
  };

  return (
    <div className={cn("space-y-4", className)}>
      {/* Stage Header */}
      <div className="bg-white dark:bg-gray-900 p-4 rounded-lg border border-gray-200 dark:border-gray-700">
        <div className="flex items-center justify-between mb-3">
          <div className="flex items-center space-x-3">
            <div 
              className="text-2xl p-2 rounded-lg"
              style={{ backgroundColor: `${stage_info.color}20` }}
            >
              {stage_info.icon}
            </div>
            <div>
              <h3 className="font-semibold text-gray-900 dark:text-gray-100">
                {stage_info.title}
              </h3>
              <p className="text-sm text-gray-600 dark:text-gray-400">
                {stage_info.description}
              </p>
            </div>
          </div>
          <div className="text-right">
            <div className="text-2xl font-bold text-gray-900 dark:text-gray-100">
              {Math.round(progress)}%
            </div>
            <div className="text-xs text-gray-500 dark:text-gray-400">
              Complete
            </div>
          </div>
        </div>
        
        {/* Progress Bar */}
        <div className="w-full bg-gray-200 dark:bg-gray-700 rounded-full h-2">
          <div 
            className={cn("h-2 rounded-full transition-all duration-300", getProgressColor(progress))}
            style={{ width: `${progress}%` }}
          />
        </div>
      </div>

      {/* Alerts */}
      {alerts && alerts.length > 0 && (
        <div className="space-y-2">
          {alerts.map((alert, index) => (
            <div 
              key={index}
              className={cn("p-3 rounded-lg border text-sm", getAlertColor(alert.type))}
            >
              <div className="font-medium">{alert.title}</div>
              <div className="mt-1">{alert.message}</div>
            </div>
          ))}
        </div>
      )}

      <div className="grid grid-cols-1 lg:grid-cols-2 gap-4">
        {/* Sample Status */}
        <div className="bg-white dark:bg-gray-900 p-4 rounded-lg border border-gray-200 dark:border-gray-700">
          <h4 className="font-medium text-gray-900 dark:text-gray-100 mb-3 flex items-center">
            <span className="mr-2">🧪</span>
            Sample Status
          </h4>
          {sample_status && sample_status.length > 0 ? (
            <div className="space-y-2">
              {sample_status.map((sample, index) => (
                <div key={index} className="flex items-center justify-between p-2 bg-gray-50 dark:bg-gray-800 rounded">
                  <div className="flex items-center space-x-2">
                    <div className={cn(
                      "w-2 h-2 rounded-full",
                      sample.status === 'active' ? 'bg-green-500' : 'bg-gray-400'
                    )} />
                    <span className="text-sm font-mono">{sample.id}</span>
                    {sample.priority === 'STAT' && (
                      <span className="px-2 py-1 bg-red-100 text-red-800 text-xs rounded">
                        STAT
                      </span>
                    )}
                  </div>
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {sample.location}
                  </div>
                </div>
              ))}
            </div>
          ) : (
            <p className="text-sm text-gray-500 dark:text-gray-400">No samples currently tracked</p>
          )}
        </div>

        {/* TLA+ Validation */}
        <div className="bg-white dark:bg-gray-900 p-4 rounded-lg border border-gray-200 dark:border-gray-700">
          <h4 className="font-medium text-gray-900 dark:text-gray-100 mb-3 flex items-center">
            <span className="mr-2">🔒</span>
            TLA+ Validation
          </h4>
          {tla_validation && Object.keys(tla_validation).length > 0 ? (
            <div className="space-y-2">
              {Object.entries(tla_validation).map(([property, result]) => (
                <div key={property} className="flex items-center justify-between">
                  <span className="text-sm text-gray-700 dark:text-gray-300">
                    {property}
                  </span>
                  <span className={cn(
                    "px-2 py-1 text-xs rounded font-medium",
                    getStatusColor(result.status)
                  )}>
                    {result.status}
                  </span>
                </div>
              ))}
            </div>
          ) : (
            <p className="text-sm text-gray-500 dark:text-gray-400">No validations to display</p>
          )}
        </div>
      </div>

      {/* Available Actions */}
      {available_actions && available_actions.length > 0 && (
        <div className="bg-white dark:bg-gray-900 p-4 rounded-lg border border-gray-200 dark:border-gray-700">
          <h4 className="font-medium text-gray-900 dark:text-gray-100 mb-3 flex items-center">
            <span className="mr-2">⚡</span>
            Available Actions
          </h4>
          <div className="grid grid-cols-1 sm:grid-cols-2 gap-2">
            {available_actions.map((action) => (
              <button
                key={action.id}
                onClick={() => onActionClick?.(action.id)}
                disabled={!action.enabled}
                className={cn(
                  "p-3 rounded-lg border text-left transition-colors",
                  action.enabled
                    ? "bg-blue-50 border-blue-200 text-blue-800 hover:bg-blue-100 dark:bg-blue-900/20 dark:border-blue-800 dark:text-blue-400 dark:hover:bg-blue-900/30"
                    : "bg-gray-50 border-gray-200 text-gray-400 cursor-not-allowed dark:bg-gray-800 dark:border-gray-700",
                  action.priority === 'high' && "ring-2 ring-red-500 ring-opacity-50"
                )}
              >
                <div className="font-medium text-sm">{action.label}</div>
                <div className="text-xs mt-1 opacity-75">{action.description}</div>
              </button>
            ))}
          </div>
        </div>
      )}

      {/* Next Steps */}
      {next_steps && next_steps.length > 0 && (
        <div className="bg-white dark:bg-gray-900 p-4 rounded-lg border border-gray-200 dark:border-gray-700">
          <h4 className="font-medium text-gray-900 dark:text-gray-100 mb-3 flex items-center">
            <span className="mr-2">🚀</span>
            Next Steps
          </h4>
          <ul className="space-y-2">
            {next_steps.map((step, index) => (
              <li key={index} className="flex items-center space-x-2 text-sm text-gray-700 dark:text-gray-300">
                <span className="text-blue-500 dark:text-blue-400">→</span>
                <span>{step}</span>
              </li>
            ))}
          </ul>
        </div>
      )}

      {/* Context Summary */}
      {stageData.context_summary && (
        <div className="bg-gray-50 dark:bg-gray-800 p-3 rounded-lg">
          <div className="text-sm text-gray-600 dark:text-gray-400 text-center">
            <span className="font-medium">Context:</span> {stageData.context_summary}
          </div>
        </div>
      )}
    </div>
  );
}
