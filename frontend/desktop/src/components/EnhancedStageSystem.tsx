import React, { useState, useEffect, useCallback } from 'react';
import { 
  StageComponentType, 
  ConversationContext, 
  ActionItem,
  ComponentData,
  ComponentState,
  ChatMessage,
  UserIntent,
  StageComponent
} from '../types/comprehensive-stage';

// Import all stage components
import { SampleTrackerComponent } from './stage/SampleTrackerComponent';
import { TestCatalogComponent } from './stage/TestCatalogComponent';
import { InstrumentStatusComponent } from './stage/InstrumentStatusComponent';
import { QualityControlComponent } from './stage/QualityControlComponent';
import { DataVisualizationComponent } from './stage/DataVisualizationComponent';
import { StatisticalToolsComponent } from './stage/StatisticalToolsComponent';
import { MolecularViewerComponent } from './stage/MolecularViewerComponent';
import { SpectralAnalysisComponent } from './stage/SpectralAnalysisComponent';
import { KnowledgeExplorerComponent } from './stage/KnowledgeExplorerComponent';
import { WorkflowDesignerComponent } from './stage/WorkflowDesignerComponent';
import { ComplianceDashboardComponent } from './stage/ComplianceDashboardComponent';
import { SafetyMonitorComponent } from './stage/SafetyMonitorComponent';
import { InventoryManagerComponent } from './stage/InventoryManagerComponent';
import { ChromatogramDisplayComponent } from './stage/ChromatogramDisplayComponent';
import { CalculationWizardComponent } from './stage/CalculationWizardComponent';
import { DefaultStageComponent } from './stage/DefaultStageComponent';

// ============================================================================
// ENHANCED CONTEXT ANALYSIS ENGINE
// ============================================================================

class EnhancedContextAnalyzer {
  private static readonly COMPREHENSIVE_KEYWORD_MAPPINGS: Record<string, StageComponentType[]> = {
    // LIMS Components
    'sample|specimen|batch|aliquot|vial|tube|container': ['SampleTracker', 'ChainOfCustody'],
    'register|track|custody|storage|disposal|transfer': ['SampleTracker', 'ChainOfCustody'],
    'test|analysis|assay|method|analytical|procedure': ['TestCatalog', 'ProtocolLibrary'],
    'validation|verification|protocol|sop': ['TestCatalog', 'ProtocolLibrary', 'ComplianceDashboard'],
    'instrument|equipment|HPLC|GC|MS|spectro|analyzer': ['InstrumentStatus', 'CalibrationScheduler'],
    'calibration|maintenance|service|repair|diagnostic': ['InstrumentStatus', 'CalibrationScheduler'],
    'QC|quality|control|precision|accuracy|bias|westgard': ['QualityControl', 'TrendingAnalysis'],
    'trending|levey|jennings|outlier|cusum|control chart': ['QualityControl', 'TrendingAnalysis'],
    'workflow|process|automation|sequence|pipeline': ['WorkflowDesigner', 'BatchProcessor'],
    'batch|automation|scheduling|resource|throughput': ['WorkflowDesigner', 'BatchProcessor'],
    'audit|compliance|regulation|GLP|ISO|FDA|validation': ['ComplianceDashboard', 'AuditTrailViewer'],
    'document|signature|approval|review|21CFR11': ['ComplianceDashboard', 'AuditTrailViewer'],
    'safety|hazard|risk|emergency|incident|exposure': ['SafetyMonitor'],
    'chemical|ppe|waste|spill|ventilation|fume hood': ['SafetyMonitor', 'SafetyDataSheets'],
    'inventory|stock|reagent|consumable|order|supplier': ['InventoryManager'],
    'expiration|lot|catalog|reorder|cost|procurement': ['InventoryManager'],
    'report|certificate|summary|dashboard|metrics': ['ReportGenerator'],
    
    // Science Components
    'data|results|chart|graph|plot|visualization': ['DataVisualization', 'StatisticalTools'],
    'statistics|correlation|regression|anova|t-test': ['StatisticalTools', 'TrendingAnalysis'],
    'histogram|scatter|box plot|violin|heatmap': ['DataVisualization', 'StatisticalTools'],
    'molecule|structure|compound|protein|dna|sequence': ['MolecularViewer', 'SequenceAnalyzer'],
    '3d|molecular|pdb|smiles|inchi|chemical structure': ['MolecularViewer', 'StructurePredictor'],
    'spectrum|chromatogram|peak|mass spec|nmr|ir': ['SpectralAnalysis', 'ChromatogramDisplay'],
    'chromatography|retention|resolution|selectivity': ['ChromatogramDisplay', 'SpectralAnalysis'],
    'mass spectrometry|ms/ms|fragmentation|isotope': ['MassSpecViewer', 'SpectralAnalysis'],
    'pathway|metabolism|enzyme|kinetics|biochemical': ['PathwayMapper', 'KineticsModeler'],
    'dose response|pharmacology|toxicology|ec50|ic50': ['DoseResponseAnalyzer', 'KineticsModeler'],
    'thermodynamics|enthalpy|entropy|gibbs|equilibrium': ['ThermodynamicsCalc', 'FormulaCalculator'],
    'chemical properties|logp|solubility|melting point': ['ChemicalProperties', 'FormulaCalculator'],
    
    // Knowledge Components
    'explain|what|how|why|theory|principle|concept': ['KnowledgeExplorer', 'TrainingModules'],
    'learn|understand|tutorial|guide|education': ['KnowledgeExplorer', 'TrainingModules'],
    'calculate|compute|formula|equation|units|convert': ['CalculationWizard', 'ConversionTools'],
    'reference|standard|literature|paper|citation': ['ReferenceLibrary', 'LiteratureSearch'],
    'method|technique|bibliography|doi|pubmed': ['LiteratureSearch', 'MethodDatabase'],
    'regulation|guidance|fda|ich|usp|pharmacopeia': ['RegulatoryGuidance', 'ComplianceDashboard'],
    'safety data|msds|sds|hazard|toxicity|exposure': ['SafetyDataSheets', 'SafetyMonitor'],
    'troubleshoot|problem|error|issue|diagnostic': ['TroubleshootingGuide', 'TechnicalSupport'],
    'best practice|recommendation|optimization|improvement': ['BestPractices', 'ExpertSystem'],
    'news|update|latest|development|innovation': ['NewsAndUpdates', 'LiteratureSearch'],
    'note|notebook|personal|bookmark|favorite': ['PersonalNotebook', 'KnowledgeExplorer']
  };

  private static readonly ENTITY_MAPPINGS: Record<string, StageComponentType[]> = {
    'sample_id': ['SampleTracker', 'ChainOfCustody'],
    'batch_number': ['SampleTracker', 'BatchProcessor'],
    'test_name': ['TestCatalog', 'ProtocolLibrary'],
    'instrument_id': ['InstrumentStatus', 'CalibrationScheduler'],
    'method_code': ['TestCatalog', 'MethodDatabase'],
    'qc_material': ['QualityControl', 'TrendingAnalysis'],
    'chemical_name': ['MolecularViewer', 'SafetyDataSheets'],
    'cas_number': ['ChemicalProperties', 'SafetyDataSheets'],
    'compound_id': ['MolecularViewer', 'SpectralAnalysis'],
    'spectrum_file': ['SpectralAnalysis', 'ChromatogramDisplay'],
    'workflow_id': ['WorkflowDesigner', 'BatchProcessor'],
    'user_id': ['AuditTrailViewer', 'ComplianceDashboard']
  };

  private static readonly CONTEXT_MAPPINGS: Record<string, StageComponentType[]> = {
    'analysis_request': ['TestCatalog', 'SampleTracker', 'WorkflowDesigner'],
    'quality_investigation': ['QualityControl', 'AuditTrailViewer', 'StatisticalTools'],
    'method_development': ['TestCatalog', 'ProtocolLibrary', 'StatisticalTools'],
    'research_inquiry': ['KnowledgeExplorer', 'LiteratureSearch', 'MethodDatabase'],
    'troubleshooting': ['TroubleshootingGuide', 'TechnicalSupport', 'InstrumentStatus'],
    'compliance_audit': ['ComplianceDashboard', 'AuditTrailViewer', 'QualityControl'],
    'safety_concern': ['SafetyMonitor', 'SafetyDataSheets', 'InventoryManager'],
    'data_analysis': ['DataVisualization', 'StatisticalTools', 'TrendingAnalysis'],
    'molecular_analysis': ['MolecularViewer', 'SpectralAnalysis', 'SequenceAnalyzer'],
    'inventory_management': ['InventoryManager', 'ReportGenerator'],
    'instrument_maintenance': ['InstrumentStatus', 'CalibrationScheduler', 'ComplianceDashboard']
  };

  static analyzeConversation(
    conversationContext: ConversationContext,
    newMessage?: ChatMessage
  ): {
    relevantComponents: StageComponentType[];
    priorityScores: Record<StageComponentType, number>;
    suggestedActions: ActionItem[];
    knowledgeQueries: string[];
    userIntent: UserIntent;
    contextualRecommendations: ContextualRecommendation[];
  } {
    const allText = [
      ...conversationContext.messages.map(m => m.content),
      newMessage?.content || ''
    ].join(' ').toLowerCase();

    const componentScores: Record<string, number> = {};
    const relevantComponents = new Set<StageComponentType>();

    // Keyword-based scoring
    Object.entries(this.COMPREHENSIVE_KEYWORD_MAPPINGS).forEach(([pattern, components]) => {
      const regex = new RegExp(pattern, 'gi');
      const matches = allText.match(regex) || [];
      
      if (matches.length > 0) {
        components.forEach(comp => {
          componentScores[comp] = (componentScores[comp] || 0) + matches.length * 2;
          relevantComponents.add(comp);
        });
      }
    });

    // Entity-based scoring
    Object.entries(this.ENTITY_MAPPINGS).forEach(([entity, components]) => {
      if (allText.includes(entity.replace('_', ' '))) {
        components.forEach(comp => {
          componentScores[comp] = (componentScores[comp] || 0) + 3;
          relevantComponents.add(comp);
        });
      }
    });

    // Context-based scoring
    Object.entries(this.CONTEXT_MAPPINGS).forEach(([context, components]) => {
      if (this.detectContext(allText, context)) {
        components.forEach(comp => {
          componentScores[comp] = (componentScores[comp] || 0) + 4;
          relevantComponents.add(comp);
        });
      }
    });

    // Analyze user intent
    const userIntent = this.analyzeUserIntent(allText, newMessage);

    // Generate suggested actions
    const suggestedActions = this.generateSuggestedActions(
      Array.from(relevantComponents), 
      userIntent, 
      componentScores
    );

    // Generate knowledge queries
    const knowledgeQueries = this.generateKnowledgeQueries(allText, userIntent);

    // Generate contextual recommendations
    const contextualRecommendations = this.generateContextualRecommendations(
      Array.from(relevantComponents),
      userIntent,
      allText
    );

    return {
      relevantComponents: Array.from(relevantComponents),
      priorityScores: componentScores as Record<StageComponentType, number>,
      suggestedActions,
      knowledgeQueries,
      userIntent,
      contextualRecommendations
    };
  }

  private static detectContext(text: string, context: string): boolean {
    const contextPatterns: Record<string, string[]> = {
      'analysis_request': ['analyze', 'test', 'measure', 'determine', 'quantify'],
      'quality_investigation': ['investigate', 'qc issue', 'out of control', 'failed', 'error'],
      'method_development': ['develop', 'optimize', 'validate', 'new method', 'improve'],
      'research_inquiry': ['research', 'study', 'investigate', 'literature', 'publication'],
      'troubleshooting': ['problem', 'issue', 'error', 'malfunction', 'not working'],
      'compliance_audit': ['audit', 'inspection', 'compliance', 'regulation', 'standard'],
      'safety_concern': ['safety', 'hazard', 'danger', 'risk', 'exposure'],
      'data_analysis': ['analyze data', 'statistics', 'correlation', 'trend', 'pattern'],
      'molecular_analysis': ['structure', 'molecule', 'compound', 'protein', 'sequence'],
      'inventory_management': ['inventory', 'stock', 'order', 'supply', 'reagent'],
      'instrument_maintenance': ['maintenance', 'calibration', 'service', 'repair', 'pm']
    };

    const patterns = contextPatterns[context] || [];
    return patterns.some(pattern => text.includes(pattern));
  }

  private static analyzeUserIntent(text: string, message?: ChatMessage): UserIntent {
    const intentPatterns = {
      'information_seeking': ['what', 'how', 'why', 'explain', 'show me', 'tell me'],
      'task_execution': ['run', 'execute', 'start', 'begin', 'perform', 'do'],
      'problem_solving': ['help', 'solve', 'fix', 'resolve', 'troubleshoot'],
      'learning': ['learn', 'understand', 'teach', 'tutorial', 'guide'],
      'monitoring': ['status', 'check', 'monitor', 'track', 'watch']
    };

    let maxScore = 0;
    let primaryIntent: IntentType = 'information_seeking';
    const secondaryIntents: IntentType[] = [];

    Object.entries(intentPatterns).forEach(([intent, patterns]) => {
      const score = patterns.reduce((acc, pattern) => 
        acc + (text.includes(pattern) ? 1 : 0), 0);
      
      if (score > maxScore) {
        if (maxScore > 0) secondaryIntents.unshift(primaryIntent);
        maxScore = score;
        primaryIntent = intent as IntentType;
      } else if (score > 0) {
        secondaryIntents.push(intent as IntentType);
      }
    });

    return {
      primary_intent: primaryIntent,
      secondary_intents: secondaryIntents.slice(0, 2),
      confidence: Math.min(maxScore / 3, 1),
      required_actions: []
    };
  }

  private static generateSuggestedActions(
    components: StageComponentType[],
    intent: UserIntent,
    scores: Record<string, number>
  ): ActionItem[] {
    const actions: ActionItem[] = [];
    
    components.forEach(component => {
      const score = scores[component] || 0;
      if (score > 2) {
        actions.push({
          action_id: `${component}_${intent.primary_intent}`,
          action_type: this.mapIntentToActionType(intent.primary_intent),
          description: `${intent.primary_intent.replace('_', ' ')} ${component}`,
          priority: score > 5 ? 'high' : score > 3 ? 'medium' : 'low',
          required_permissions: [],
          estimated_duration: 300,
          dependencies: []
        });
      }
    });

    return actions.sort((a, b) => {
      const priorityOrder = { 'high': 3, 'medium': 2, 'low': 1, 'urgent': 4 };
      return priorityOrder[b.priority] - priorityOrder[a.priority];
    });
  }

  private static mapIntentToActionType(intent: IntentType): ActionType {
    const mapping: Record<IntentType, ActionType> = {
      'information_seeking': 'view',
      'task_execution': 'execute',
      'problem_solving': 'analyze',
      'learning': 'view',
      'monitoring': 'view'
    };
    return mapping[intent] || 'view';
  }

  private static generateKnowledgeQueries(text: string, intent: UserIntent): string[] {
    const queries: string[] = [];
    
    if (intent.primary_intent === 'learning' || intent.primary_intent === 'information_seeking') {
      if (text.includes('method')) queries.push('analytical methods');
      if (text.includes('qc') || text.includes('quality')) queries.push('quality control');
      if (text.includes('instrument')) queries.push('instrumentation');
      if (text.includes('safety')) queries.push('laboratory safety');
      if (text.includes('regulation')) queries.push('regulatory guidance');
    }

    return queries;
  }

  private static generateContextualRecommendations(
    components: StageComponentType[],
    intent: UserIntent,
    text: string
  ): ContextualRecommendation[] {
    const recommendations: ContextualRecommendation[] = [];
    
    // Cross-component recommendations
    if (components.includes('SampleTracker') && components.includes('TestCatalog')) {
      recommendations.push({
        type: 'workflow_optimization',
        title: 'Optimize Sample-to-Test Workflow',
        description: 'Consider automating sample registration and test assignment',
        confidence: 0.8,
        related_components: ['SampleTracker', 'TestCatalog', 'WorkflowDesigner']
      });
    }

    if (components.includes('QualityControl') && components.includes('StatisticalTools')) {
      recommendations.push({
        type: 'quality_enhancement',
        title: 'Enhanced QC Analysis',
        description: 'Implement advanced statistical analysis for QC trending',
        confidence: 0.9,
        related_components: ['QualityControl', 'StatisticalTools', 'TrendingAnalysis']
      });
    }

    return recommendations;
  }
}

// Supporting interfaces
interface ContextualRecommendation {
  type: string;
  title: string;
  description: string;
  confidence: number;
  related_components: StageComponentType[];
}

type IntentType = 'information_seeking' | 'task_execution' | 'problem_solving' | 'learning' | 'monitoring';
type ActionType = 'view' | 'create' | 'update' | 'delete' | 'execute' | 'analyze' | 'report';

// ============================================================================
// ENHANCED STAGE SYSTEM COMPONENT
// ============================================================================

interface EnhancedStageSystemProps {
  conversationContext: ConversationContext;
  onActionExecuted?: (action: ActionItem) => void;
  onComponentChange?: (components: StageComponentType[]) => void;
  className?: string;
}

export const EnhancedStageSystem: React.FC<EnhancedStageSystemProps> = ({
  conversationContext,
  onActionExecuted,
  onComponentChange,
  className = ''
}) => {
  const [activeComponents, setActiveComponents] = useState<StageComponentType[]>(['DefaultStage']);
  const [componentStates, setComponentStates] = useState<Record<string, ComponentState>>({});
  const [layoutMode, setLayoutMode] = useState<'single' | 'dual' | 'grid' | 'tabbed'>('single');
  const [contextAnalysis, setContextAnalysis] = useState<any>(null);

  // Analyze conversation context and update stage
  const analyzeAndUpdateStage = useCallback((newMessage?: ChatMessage) => {
    const analysis = EnhancedContextAnalyzer.analyzeConversation(
      conversationContext,
      newMessage
    );

    setContextAnalysis(analysis);

    // Select primary component with highest score
    const sortedComponents = analysis.relevantComponents.sort(
      (a, b) => (analysis.priorityScores[b] || 0) - (analysis.priorityScores[a] || 0)
    );

    const newActiveComponents = sortedComponents.length > 0 
      ? sortedComponents.slice(0, 4) // Maximum 4 components
      : ['DefaultStage'];

    // Determine layout based on number of components
    const newLayout = newActiveComponents.length === 1 ? 'single' :
                     newActiveComponents.length === 2 ? 'dual' :
                     newActiveComponents.length <= 4 ? 'grid' : 'tabbed';

    setActiveComponents(newActiveComponents);
    setLayoutMode(newLayout);

    // Initialize component states
    const newStates: Record<string, ComponentState> = {};
    newActiveComponents.forEach(comp => {
      newStates[comp] = {
        loading: false,
        error: null,
        warnings: [],
        user_interactions: [],
        component_health: 'healthy'
      };
    });
    setComponentStates(newStates);

    // Notify parent of component changes
    onComponentChange?.(newActiveComponents);
  }, [conversationContext, onComponentChange]);

  // Update stage when conversation context changes
  useEffect(() => {
    analyzeAndUpdateStage();
  }, [analyzeAndUpdateStage]);

  // Execute user actions
  const handleActionExecution = useCallback((action: ActionItem) => {
    // Update component state to reflect action execution
    setComponentStates(prev => ({
      ...prev,
      [action.action_id]: {
        ...prev[action.action_id],
        user_interactions: [
          ...(prev[action.action_id]?.user_interactions || []),
          {
            interaction_id: `${Date.now()}`,
            interaction_type: action.action_type,
            timestamp: new Date(),
            user_id: 'current_user',
            parameters: {}
          }
        ]
      }
    }));

    onActionExecuted?.(action);
  }, [onActionExecuted]);

  // Render individual stage component
  const renderComponent = (componentType: StageComponentType, index: number) => {
    const componentState = componentStates[componentType];
    const analysisData = contextAnalysis?.priorityScores[componentType] || 0;

    const commonProps = {
      key: `${componentType}-${index}`,
      data: {} as ComponentData,
      state: componentState || {
        loading: false,
        error: null,
        warnings: [],
        user_interactions: [],
        component_health: 'healthy' as const
      },
      onActionExecute: handleActionExecution,
      contextAnalysis: contextAnalysis,
      priority: analysisData
    };

    switch (componentType) {
      case 'SampleTracker':
        return <SampleTrackerComponent {...commonProps} />;
      case 'TestCatalog':
        return <TestCatalogComponent {...commonProps} />;
      case 'InstrumentStatus':
        return <InstrumentStatusComponent {...commonProps} />;
      case 'QualityControl':
        return <QualityControlComponent {...commonProps} />;
      case 'DataVisualization':
        return <DataVisualizationComponent {...commonProps} />;
      case 'StatisticalTools':
        return <StatisticalToolsComponent {...commonProps} />;
      case 'MolecularViewer':
        return <MolecularViewerComponent {...commonProps} />;
      case 'SpectralAnalysis':
        return <SpectralAnalysisComponent {...commonProps} />;
      case 'KnowledgeExplorer':
        return <KnowledgeExplorerComponent {...commonProps} />;
      case 'WorkflowDesigner':
        return <WorkflowDesignerComponent {...commonProps} />;
      case 'ComplianceDashboard':
        return <ComplianceDashboardComponent {...commonProps} />;
      case 'SafetyMonitor':
        return <SafetyMonitorComponent {...commonProps} />;
      case 'InventoryManager':
        return <InventoryManagerComponent {...commonProps} />;
      case 'ChromatogramDisplay':
        return <ChromatogramDisplayComponent {...commonProps} />;
      case 'CalculationWizard':
        return <CalculationWizardComponent {...commonProps} />;
      default:
        return <DefaultStageComponent {...commonProps} />;
    }
  };

  // Render layout based on mode
  const renderLayout = () => {
    switch (layoutMode) {
      case 'single':
        return (
          <div className="stage-single-layout">
            {renderComponent(activeComponents[0], 0)}
          </div>
        );

      case 'dual':
        return (
          <div className="stage-dual-layout grid grid-cols-2 gap-4">
            {activeComponents.slice(0, 2).map((comp, idx) => renderComponent(comp, idx))}
          </div>
        );

      case 'grid':
        return (
          <div className="stage-grid-layout grid grid-cols-2 grid-rows-2 gap-4">
            {activeComponents.slice(0, 4).map((comp, idx) => renderComponent(comp, idx))}
          </div>
        );

      case 'tabbed':
        return (
          <div className="stage-tabbed-layout">
            <div className="tab-headers flex border-b">
              {activeComponents.map((comp, idx) => (
                <button
                  key={comp}
                  className={`px-4 py-2 border-b-2 ${idx === 0 ? 'border-blue-500' : 'border-transparent'}`}
                  onClick={() => {/* Handle tab switching */}}
                >
                  {comp.replace(/([A-Z])/g, ' $1').trim()}
                </button>
              ))}
            </div>
            <div className="tab-content p-4">
              {renderComponent(activeComponents[0], 0)}
            </div>
          </div>
        );

      default:
        return renderComponent('DefaultStage', 0);
    }
  };

  return (
    <div className={`enhanced-stage-system ${className}`}>
      {/* Context Analysis Display */}
      {contextAnalysis && (
        <div className="context-analysis-header bg-gray-100 p-2 mb-4 rounded">
          <div className="flex justify-between items-center">
            <span className="text-sm font-medium">
              Intent: {contextAnalysis.userIntent.primary_intent.replace('_', ' ')}
            </span>
            <span className="text-xs text-gray-600">
              {activeComponents.length} component{activeComponents.length !== 1 ? 's' : ''} active
            </span>
          </div>
          {contextAnalysis.suggestedActions.length > 0 && (
            <div className="mt-2">
              <span className="text-xs font-medium">Suggested Actions:</span>
              <div className="flex flex-wrap gap-1 mt-1">
                {contextAnalysis.suggestedActions.slice(0, 3).map((action: ActionItem) => (
                  <button
                    key={action.action_id}
                    className="text-xs bg-blue-100 text-blue-800 px-2 py-1 rounded"
                    onClick={() => handleActionExecution(action)}
                  >
                    {action.description}
                  </button>
                ))}
              </div>
            </div>
          )}
        </div>
      )}

      {/* Main Stage Content */}
      <div className="stage-content">
        {renderLayout()}
      </div>

      {/* Contextual Recommendations */}
      {contextAnalysis?.contextualRecommendations?.length > 0 && (
        <div className="contextual-recommendations mt-4 p-3 bg-yellow-50 border border-yellow-200 rounded">
          <h4 className="text-sm font-medium text-yellow-800 mb-2">Recommendations:</h4>
          {contextAnalysis.contextualRecommendations.map((rec: ContextualRecommendation, idx: number) => (
            <div key={idx} className="text-sm text-yellow-700 mb-1">
              <strong>{rec.title}:</strong> {rec.description}
            </div>
          ))}
        </div>
      )}
    </div>
  );
};

export default EnhancedStageSystem;
