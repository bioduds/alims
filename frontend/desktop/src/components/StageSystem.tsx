import React, { useState, useEffect, useCallback } from 'react';
import { 
  StageComponent, 
  ConversationContext, 
  ActionItem,
  Sample,
  Test,
  Instrument,
  Workflow,
  VisualizationData,
  Alert,
  ChatMessage,
  ExtractedEntity,
  KnowledgeItem,
  ComponentData,
  ComponentState,
  StageComponentType,
  KnowledgeDomain
} from '../types/stage';

// Component imports
import { SampleTrackerComponent } from './stage/SampleTrackerComponent';
import { TestCatalogComponent } from './stage/TestCatalogComponent';
import { DefaultStageComponent } from './stage/DefaultStageComponent';

// ============================================================================
// CONTEXT ANALYSIS ENGINE
// ============================================================================

class ContextAnalyzer {
  private static readonly KEYWORD_MAPPINGS: Record<string, StageComponentType[]> = {
    // Sample-related keywords
    'sample|specimen|batch|aliquot|vial': ['SampleTracker'],
    'register|track|custody|storage|disposal': ['SampleTracker'],
    
    // Test-related keywords  
    'test|analysis|assay|method|analytical': ['TestCatalog'],
    'procedure|protocol|validation|verification': ['TestCatalog', 'ProtocolLibrary'],
    
    // Instrument-related keywords
    'instrument|equipment|HPLC|GC|MS|spectro': ['InstrumentStatus'],
    'calibration|maintenance|service|repair': ['InstrumentStatus', 'CalibrationScheduler'],
    
    // QC-related keywords
    'QC|quality|control|precision|accuracy|bias': ['QualityControl'],
    'trending|westgard|levey|jennings|outlier': ['QualityControl', 'TrendingAnalysis'],
    
    // Data-related keywords
    'data|results|chart|graph|trend|statistics': ['DataVisualization', 'StatisticalTools'],
    'plot|histogram|regression|correlation': ['DataVisualization', 'StatisticalTools'],
    
    // Workflow-related keywords
    'workflow|process|automation|sequence|batch': ['WorkflowDesigner', 'BatchProcessor'],
    
    // Knowledge-related keywords
    'explain|what|how|why|theory|principle': ['KnowledgeExplorer'],
    'calculate|formula|equation|units': ['KnowledgeExplorer', 'StatisticalTools'],
    
    // Compliance-related keywords
    'audit|compliance|regulation|GLP|ISO|FDA': ['ComplianceDashboard', 'AuditTrailViewer'],
    'document|signature|approval|review': ['ComplianceDashboard'],
    
    // Safety-related keywords
    'safety|hazard|risk|emergency|incident': ['SafetyMonitor'],
    'chemical|exposure|PPE|waste|spill': ['SafetyMonitor'],
    
    // Inventory-related keywords
    'inventory|stock|reagent|consumable|order': ['InventoryManager'],
    'expiration|lot|supplier|catalog': ['InventoryManager']
  };

  static analyzeContext(
    conversationContext: ConversationContext,
    newMessage?: ChatMessage
  ): {
    relevantComponents: StageComponentType[];
    priorities: Record<StageComponentType, number>;
    suggestedActions: ActionItem[];
    knowledgeQueries: string[];
  } {
    const allText = [
      ...conversationContext.messages.map(m => m.content),
      newMessage?.content || ''
    ].join(' ').toLowerCase();

    const relevantComponents = new Set<StageComponentType>();
    const priorities: Record<string, number> = {};

    // Keyword-based matching
    Object.entries(this.KEYWORD_MAPPINGS).forEach(([pattern, components]) => {
      const regex = new RegExp(pattern, 'gi');
      const matches = allText.match(regex) || [];
      
      if (matches.length > 0) {
        components.forEach(comp => {
          relevantComponents.add(comp);
          priorities[comp] = (priorities[comp] || 0) + matches.length;
        });
      }
    });

    // Entity-based enhancement
    conversationContext.entities.forEach(entity => {
      switch (entity.type) {
        case 'Sample':
          relevantComponents.add('SampleTracker');
          priorities['SampleTracker'] = (priorities['SampleTracker'] || 0) + entity.confidence;
          break;
        case 'Test':
          relevantComponents.add('TestCatalog');
          priorities['TestCatalog'] = (priorities['TestCatalog'] || 0) + entity.confidence;
          break;
        case 'Instrument':
          relevantComponents.add('InstrumentStatus');
          priorities['InstrumentStatus'] = (priorities['InstrumentStatus'] || 0) + entity.confidence;
          break;
        case 'QC':
          relevantComponents.add('QualityControl');
          priorities['QualityControl'] = (priorities['QualityControl'] || 0) + entity.confidence;
          break;
      }
    });

    // Intent-based recommendations
    const suggestedActions = this.deriveActions(
      Array.from(relevantComponents),
      conversationContext.intent
    );

    // Knowledge queries
    const knowledgeQueries = this.generateKnowledgeQueries(
      conversationContext.keywords,
      conversationContext.intent
    );

    // Default components if nothing specific
    if (relevantComponents.size === 0) {
      relevantComponents.add('KnowledgeExplorer');
      relevantComponents.add('TestCatalog');
      priorities['KnowledgeExplorer'] = 1;
      priorities['TestCatalog'] = 1;
    }

    return {
      relevantComponents: Array.from(relevantComponents),
      priorities: priorities as Record<StageComponentType, number>,
      suggestedActions,
      knowledgeQueries
    };
  }

  private static deriveActions(
    components: StageComponentType[],
    intent: string
  ): ActionItem[] {
    const actions: ActionItem[] = [];

    components.forEach(component => {
      switch (component) {
        case 'SampleTracker':
          actions.push(
            {
              id: 'register-sample',
              type: 'sample',
              label: 'Register New Sample',
              description: 'Add a new sample to the system',
              icon: 'vial',
              priority: 'medium',
              onExecute: () => console.log('Register sample')
            },
            {
              id: 'track-sample',
              type: 'sample',
              label: 'Track Sample Status',
              description: 'View sample location and status',
              icon: 'map-pin',
              priority: 'medium',
              onExecute: () => console.log('Track sample')
            }
          );
          break;

        case 'TestCatalog':
          actions.push(
            {
              id: 'search-tests',
              type: 'test',
              label: 'Search Tests',
              description: 'Find available tests and methods',
              icon: 'search',
              priority: 'high',
              onExecute: () => console.log('Search tests')
            },
            {
              id: 'compare-methods',
              type: 'test',
              label: 'Compare Methods',
              description: 'Compare analytical methods',
              icon: 'compare',
              priority: 'medium',
              onExecute: () => console.log('Compare methods')
            }
          );
          break;

        case 'InstrumentStatus':
          actions.push(
            {
              id: 'check-status',
              type: 'instrument',
              label: 'Check Status',
              description: 'View instrument status and availability',
              icon: 'activity',
              priority: 'high',
              onExecute: () => console.log('Check instrument status')
            },
            {
              id: 'schedule-maintenance',
              type: 'instrument',
              label: 'Schedule Maintenance',
              description: 'Plan instrument maintenance',
              icon: 'calendar',
              priority: 'medium',
              onExecute: () => console.log('Schedule maintenance')
            }
          );
          break;

        case 'DataVisualization':
          actions.push(
            {
              id: 'create-chart',
              type: 'visualization',
              label: 'Create Chart',
              description: 'Generate data visualization',
              icon: 'bar-chart',
              priority: 'high',
              onExecute: () => console.log('Create chart')
            },
            {
              id: 'export-data',
              type: 'visualization',
              label: 'Export Data',
              description: 'Export data in various formats',
              icon: 'download',
              priority: 'medium',
              onExecute: () => console.log('Export data')
            }
          );
          break;
      }
    });

    return actions;
  }

  private static generateKnowledgeQueries(
    keywords: string[],
    intent: string
  ): string[] {
    const queries: string[] = [];

    // Generate queries based on keywords
    keywords.forEach(keyword => {
      if (intent.includes('explain') || intent.includes('what')) {
        queries.push(`What is ${keyword}?`);
        queries.push(`How does ${keyword} work?`);
      }
      if (intent.includes('procedure') || intent.includes('how')) {
        queries.push(`${keyword} procedure`);
        queries.push(`${keyword} protocol`);
      }
    });

    return queries.slice(0, 5); // Limit to top 5 queries
  }
}

// ============================================================================
// MAIN STAGE COMPONENT
// ============================================================================

interface StageSystemProps {
  conversationContext: ConversationContext;
  onVisualizationChange: (type: string, data: any) => void;
  onUserAction: (action: ActionItem) => void;
  userPermissions: string[];
  className?: string;
}

export const StageSystem: React.FC<StageSystemProps> = ({
  conversationContext,
  onVisualizationChange,
  onUserAction,
  userPermissions,
  className = ''
}) => {
  const [activeComponents, setActiveComponents] = useState<StageComponent[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  // Analyze context and update stage components
  const updateStageComponents = useCallback(async () => {
    if (!conversationContext.conversationId) return;

    setLoading(true);
    setError(null);

    try {
      const analysis = ContextAnalyzer.analyzeContext(conversationContext);
      
      // Create new components based on analysis
      const newComponents: StageComponent[] = analysis.relevantComponents
        .sort((a, b) => (analysis.priorities[b] || 0) - (analysis.priorities[a] || 0))
        .slice(0, 3) // Show top 3 most relevant components
        .map((type, index) => ({
          id: `${type}-${Date.now()}`,
          type,
          state: 'Loading' as ComponentState,
          priority: analysis.priorities[type] || 0,
          data: {}
        }));

      setActiveComponents(newComponents);

      // Load data for each component
      for (const component of newComponents) {
        await loadComponentData(component);
      }

    } catch (err) {
      setError(`Failed to update stage: ${err}`);
    } finally {
      setLoading(false);
    }
  }, [conversationContext]);

  // Load data for a specific component
  const loadComponentData = useCallback(async (component: StageComponent) => {
    try {
      // Simulate data loading based on component type
      const data = await fetchComponentData(component.type, conversationContext);
      
      setActiveComponents(prev => 
        prev.map(c => 
          c.id === component.id 
            ? { ...c, state: 'Active' as ComponentState, data }
            : c
        )
      );
    } catch (err) {
      setActiveComponents(prev => 
        prev.map(c => 
          c.id === component.id 
            ? { ...c, state: 'Error' as ComponentState }
            : c
        )
      );
    }
  }, [conversationContext]);

  // Update stage when conversation context changes
  useEffect(() => {
    updateStageComponents();
  }, [conversationContext.lastUpdate, updateStageComponents]);

  // Render individual stage component
  const renderComponent = useCallback((component: StageComponent) => {
    const commonProps = {
      key: component.id,
      component,
      conversationContext,
      onAction: onUserAction,
      userPermissions
    };

    switch (component.type) {
      case 'SampleTracker':
        return <SampleTrackerComponent {...commonProps} />;
      case 'TestCatalog':
        return <TestCatalogComponent {...commonProps} />;
      case 'InstrumentStatus':
        return <DefaultStageComponent {...commonProps} />;
      case 'QualityControl':
        return <DefaultStageComponent {...commonProps} />;
      case 'DataVisualization':
        return <DefaultStageComponent {...commonProps} />;
      case 'KnowledgeExplorer':
        return <DefaultStageComponent {...commonProps} />;
      case 'WorkflowDesigner':
        return <DefaultStageComponent {...commonProps} />;
      case 'ComplianceDashboard':
        return <DefaultStageComponent {...commonProps} />;
      default:
        return <DefaultStageComponent {...commonProps} />;
    }
  }, [onUserAction, userPermissions, conversationContext]);

  return (
    <div className={`stage-system ${className}`}>
      {/* Stage Header */}
      <div className="stage-header">
        <h2 className="text-lg font-semibold text-gray-800">
          Laboratory Analysis Stage
        </h2>
        <p className="text-sm text-gray-600">
          Context-aware tools and information for your laboratory workflow
        </p>
      </div>

      {/* Loading State */}
      {loading && (
        <div className="stage-loading">
          <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-500"></div>
          <span className="ml-2 text-gray-600">Updating stage content...</span>
        </div>
      )}

      {/* Error State */}
      {error && (
        <div className="stage-error bg-red-50 border border-red-200 rounded p-4">
          <p className="text-red-700">{error}</p>
          <button 
            onClick={updateStageComponents}
            className="mt-2 px-3 py-1 bg-red-100 text-red-700 rounded text-sm hover:bg-red-200"
          >
            Retry
          </button>
        </div>
      )}

      {/* Active Components */}
      <div className="stage-components space-y-4">
        {activeComponents.map(component => (
          <div
            key={component.id}
            className="stage-component-wrapper opacity-100 transform translate-y-0 transition-all duration-300"
          >
            {renderComponent(component)}
          </div>
        ))}
      </div>

      {/* Default State */}
      {!loading && !error && activeComponents.length === 0 && (
        <div className="stage-empty text-center py-8">
          <div className="text-gray-400 mb-4">
            <svg className="w-16 h-16 mx-auto" fill="currentColor" viewBox="0 0 20 20">
              <path fillRule="evenodd" d="M3 4a1 1 0 011-1h12a1 1 0 011 1v12a1 1 0 01-1 1H4a1 1 0 01-1-1V4zm2 3a1 1 0 000 2h10a1 1 0 100-2H5zm0 4a1 1 0 100 2h6a1 1 0 100-2H5z" clipRule="evenodd" />
            </svg>
          </div>
          <p className="text-gray-600">
            Start a conversation to see relevant laboratory tools and information
          </p>
        </div>
      )}
    </div>
  );
};

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

async function fetchComponentData(
  componentType: StageComponentType,
  context: ConversationContext
): Promise<ComponentData> {
  // Simulate API calls to fetch component-specific data
  switch (componentType) {
    case 'SampleTracker':
      return {
        samples: [
          { id: 'S001', status: 'In Progress', location: 'Lab A', tests: ['CBC', 'Chemistry'] },
          { id: 'S002', status: 'Completed', location: 'Archive', tests: ['Microbiology'] }
        ]
      };
    
    case 'TestCatalog':
      return {
        tests: [
          { name: 'Complete Blood Count', method: 'Flow Cytometry', turnaround: '2 hours' },
          { name: 'Chemistry Panel', method: 'Photometry', turnaround: '1 hour' },
          { name: 'HPLC Analysis', method: 'Chromatography', turnaround: '4 hours' }
        ]
      };
    
    case 'InstrumentStatus':
      return {
        instruments: [
          { id: 'HPLC-001', name: 'Agilent 1200', status: 'Online', queue: 3 },
          { id: 'GC-MS-001', name: 'Shimadzu QP2020', status: 'Maintenance', queue: 0 }
        ]
      };
    
    default:
      return {};
  }
}

export default StageSystem;
