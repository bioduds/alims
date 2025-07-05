import React from 'react';
import { StageComponent, ConversationContext, ActionItem } from '../../types/stage';

interface DefaultStageComponentProps {
  component: StageComponent;
  conversationContext: ConversationContext;
  onAction: (action: ActionItem) => void;
  userPermissions: string[];
}

export const DefaultStageComponent: React.FC<DefaultStageComponentProps> = ({
  component,
  conversationContext,
  onAction,
  userPermissions
}) => {
  const getComponentIcon = (type: string) => {
    const icons: Record<string, string> = {
      'SampleTracker': '🧪',
      'TestCatalog': '⚗️',
      'InstrumentStatus': '🔬',
      'QualityControl': '✅',
      'WorkflowDesigner': '🔄',
      'DataVisualization': '📊',
      'KnowledgeExplorer': '📚',
      'ComplianceDashboard': '📋',
      'SafetyMonitor': '⚠️',
      'InventoryManager': '📦',
      'ReportGenerator': '📄',
      'ProtocolLibrary': '📖',
      'CalibrationScheduler': '📅',
      'AuditTrailViewer': '🔍',
      'TrendingAnalysis': '📈',
      'StatisticalTools': '📐',
      'MolecularViewer': '🧬',
      'ChromatogramDisplay': '📉',
      'SpectralAnalysis': '🌈',
      'BatchProcessor': '⚙️'
    };
    return icons[type] || '🔧';
  };

  const getComponentDescription = (type: string) => {
    const descriptions: Record<string, string> = {
      'SampleTracker': 'Track and manage laboratory samples',
      'TestCatalog': 'Browse available tests and methods',
      'InstrumentStatus': 'Monitor instrument status and performance',
      'QualityControl': 'Quality control monitoring and management',
      'WorkflowDesigner': 'Design and manage laboratory workflows',
      'DataVisualization': 'Create and view data visualizations',
      'KnowledgeExplorer': 'Explore scientific knowledge and resources',
      'ComplianceDashboard': 'Monitor regulatory compliance',
      'SafetyMonitor': 'Laboratory safety monitoring and alerts',
      'InventoryManager': 'Manage laboratory inventory and supplies',
      'ReportGenerator': 'Generate and manage reports',
      'ProtocolLibrary': 'Access laboratory protocols and procedures',
      'CalibrationScheduler': 'Schedule and track calibrations',
      'AuditTrailViewer': 'View audit trails and logs',
      'TrendingAnalysis': 'Analyze trends and patterns',
      'StatisticalTools': 'Statistical analysis tools',
      'MolecularViewer': 'View molecular structures and data',
      'ChromatogramDisplay': 'Display chromatographic data',
      'SpectralAnalysis': 'Analyze spectral data',
      'BatchProcessor': 'Process samples in batches'
    };
    return descriptions[type] || 'Laboratory tool and information panel';
  };

  const defaultAction: ActionItem = {
    id: `open-${component.type.toLowerCase()}`,
    type: component.type.toLowerCase(),
    label: `Open ${component.type}`,
    description: `Open the ${component.type} interface`,
    icon: getComponentIcon(component.type),
    priority: 'medium',
    onExecute: () => {
      onAction({
        id: `open-${component.type.toLowerCase()}`,
        type: component.type.toLowerCase(),
        label: `Open ${component.type}`,
        description: `Open the ${component.type} interface`,
        icon: getComponentIcon(component.type),
        priority: 'medium',
        onExecute: () => console.log(`Opening ${component.type}`)
      });
    }
  };

  if (component.state === 'Loading') {
    return (
      <div className="stage-component bg-white rounded-lg shadow-sm border border-gray-200 p-4">
        <div className="flex items-center space-x-2 mb-4">
          <div className="w-4 h-4 bg-gray-500 rounded animate-pulse"></div>
          <h3 className="font-medium text-gray-900">{component.type}</h3>
        </div>
        <div className="animate-pulse space-y-3">
          <div className="h-4 bg-gray-200 rounded w-3/4"></div>
          <div className="h-4 bg-gray-200 rounded w-1/2"></div>
          <div className="h-4 bg-gray-200 rounded w-5/6"></div>
        </div>
      </div>
    );
  }

  if (component.state === 'Error') {
    return (
      <div className="stage-component bg-white rounded-lg shadow-sm border border-red-200 p-4">
        <div className="flex items-center space-x-2 mb-4">
          <span className="text-red-500 text-lg">❌</span>
          <h3 className="font-medium text-red-900">{component.type}</h3>
          <span className="bg-red-100 text-red-800 text-xs px-2 py-1 rounded-full">Error</span>
        </div>
        <div className="text-red-600 text-sm">
          Failed to load {component.type} component. Please try again.
        </div>
        <button 
          onClick={() => window.location.reload()}
          className="mt-2 px-3 py-1 bg-red-100 text-red-700 text-sm rounded hover:bg-red-200"
        >
          Retry
        </button>
      </div>
    );
  }

  return (
    <div className="stage-component bg-white rounded-lg shadow-sm border border-gray-200">
      {/* Header */}
      <div className="border-b border-gray-200 p-4">
        <div className="flex items-center justify-between">
          <div className="flex items-center space-x-2">
            <span className="text-gray-500 text-lg">{getComponentIcon(component.type)}</span>
            <h3 className="font-medium text-gray-900">{component.type}</h3>
            <span className="bg-gray-100 text-gray-800 text-xs px-2 py-1 rounded-full">
              Available
            </span>
          </div>
        </div>
        <p className="text-sm text-gray-600 mt-2">
          {getComponentDescription(component.type)}
        </p>
      </div>

      {/* Content */}
      <div className="p-4">
        {/* Component-specific content placeholder */}
        <div className="text-center py-8">
          <div className="text-6xl mb-4 text-gray-300">
            {getComponentIcon(component.type)}
          </div>
          <h4 className="text-lg font-medium text-gray-900 mb-2">
            {component.type}
          </h4>
          <p className="text-gray-600 mb-4">
            {getComponentDescription(component.type)}
          </p>
          
          {/* Contextual information */}
          {conversationContext.keywords.length > 0 && (
            <div className="mb-4">
              <p className="text-sm text-gray-500 mb-2">Related to your conversation:</p>
              <div className="flex flex-wrap justify-center gap-1">
                {conversationContext.keywords.slice(0, 5).map((keyword, index) => (
                  <span 
                    key={index}
                    className="px-2 py-1 bg-blue-100 text-blue-800 text-xs rounded"
                  >
                    {keyword}
                  </span>
                ))}
              </div>
            </div>
          )}

          {/* Action button */}
          <button
            onClick={defaultAction.onExecute}
            className="px-4 py-2 bg-blue-600 text-white rounded-md hover:bg-blue-700 transition-colors"
          >
            {defaultAction.label}
          </button>
        </div>

        {/* Coming soon notice */}
        <div className="mt-4 p-3 bg-yellow-50 border border-yellow-200 rounded-md">
          <div className="flex items-center space-x-2">
            <span className="text-yellow-600">🚧</span>
            <span className="text-sm text-yellow-800">
              Full {component.type} interface coming soon! 
              This is a placeholder showing component availability.
            </span>
          </div>
        </div>
      </div>
    </div>
  );
};

export default DefaultStageComponent;
