// ============================================================================
// SHARED TYPE DEFINITIONS FOR STAGE SYSTEM
// ============================================================================

export interface Sample {
  id: string;
  status: 'received' | 'in_progress' | 'completed' | 'archived' | 'rejected';
  location: string;
  tests: string[];
  registrationDate: Date;
  completionDate?: Date;
  priority: 'routine' | 'urgent' | 'stat';
  patientId?: string;
  sampleType: string;
  volume?: number;
  chainOfCustody: CustodyRecord[];
}

export interface CustodyRecord {
  timestamp: Date;
  userId: string;
  action: string;
  location: string;
  notes?: string;
}

export interface Test {
  id: string;
  name: string;
  method: string;
  analytes: string[];
  sampleTypes: string[];
  turnaroundTime: string;
  cost: number;
  accreditationStatus: 'accredited' | 'non_accredited' | 'pending';
  methodology: string;
  referenceRanges: ReferenceRange[];
  qcRequirements: string[];
}

export interface ReferenceRange {
  analyte: string;
  population: string;
  units: string;
  lowerLimit: number;
  upperLimit: number;
  criticalLow?: number;
  criticalHigh?: number;
}

export interface Instrument {
  id: string;
  name: string;
  model: string;
  manufacturer: string;
  status: 'online' | 'offline' | 'maintenance' | 'error' | 'calibration';
  currentAnalysis?: string;
  queueLength: number;
  lastCalibration: Date;
  nextMaintenance: Date;
  location: string;
  capabilities: string[];
  performanceMetrics: {
    uptime: number;
    accuracy: number;
    precision: number;
    throughput: number;
  };
}

export interface Workflow {
  id: string;
  name: string;
  description: string;
  steps: WorkflowStep[];
  status: 'draft' | 'active' | 'paused' | 'completed' | 'error';
  progress: number;
  startTime?: Date;
  endTime?: Date;
  assignedTo?: string;
  priority: 'low' | 'medium' | 'high' | 'critical';
}

export interface WorkflowStep {
  id: string;
  name: string;
  type: 'manual' | 'automated' | 'approval' | 'notification';
  status: 'pending' | 'in_progress' | 'completed' | 'skipped' | 'error';
  estimatedDuration: number;
  actualDuration?: number;
  assignedTo?: string;
  dependencies: string[];
  instructions?: string;
}

export interface VisualizationData {
  id: string;
  type: 'line' | 'bar' | 'scatter' | 'histogram' | 'control_chart' | 'chromatogram' | 'spectrum';
  title: string;
  data: any[];
  xAxis: AxisConfig;
  yAxis: AxisConfig;
  metadata: {
    created: Date;
    source: string;
    parameters: Record<string, any>;
  };
}

export interface AxisConfig {
  label: string;
  units?: string;
  scale: 'linear' | 'logarithmic' | 'time';
  range?: [number, number];
}

export interface Alert {
  id: string;
  type: 'info' | 'warning' | 'error' | 'critical';
  title: string;
  message: string;
  timestamp: Date;
  source: string;
  acknowledged: boolean;
  actions?: AlertAction[];
}

export interface AlertAction {
  label: string;
  action: () => void;
  type: 'primary' | 'secondary' | 'danger';
}

export interface ChatMessage {
  id: string;
  role: 'user' | 'agent';
  content: string;
  timestamp: Date;
  agent_source?: string;
  metadata?: {
    confidence?: number;
    entities?: ExtractedEntity[];
    intent?: string;
  };
}

export interface ExtractedEntity {
  type: 'Sample' | 'Test' | 'Instrument' | 'Method' | 'QC' | 'Reagent' | 'Protocol';
  value: string;
  confidence: number;
  context: string;
  startIndex?: number;
  endIndex?: number;
}

// ============================================================================
// QUALITY CONTROL SPECIFIC TYPES
// ============================================================================

export interface QCMaterial {
  id: string;
  name: string;
  level: 'low' | 'normal' | 'high';
  lotNumber: string;
  expirationDate: Date;
  analytes: QCAnalyte[];
  manufacturer: string;
  storageConditions: string;
}

export interface QCAnalyte {
  name: string;
  targetValue: number;
  standardDeviation: number;
  units: string;
  acceptableLimits: {
    low: number;
    high: number;
  };
}

export interface QCResult {
  id: string;
  materialId: string;
  analyte: string;
  value: number;
  timestamp: Date;
  runId: string;
  instrument: string;
  operator: string;
  inControl: boolean;
  violatedRules: string[];
}

export interface ControlChart {
  analyte: string;
  material: string;
  data: QCResult[];
  statistics: {
    mean: number;
    standardDeviation: number;
    coefficientOfVariation: number;
    bias: number;
  };
  controlLimits: {
    mean: number;
    plus1SD: number;
    minus1SD: number;
    plus2SD: number;
    minus2SD: number;
    plus3SD: number;
    minus3SD: number;
  };
}

// ============================================================================
// KNOWLEDGE BASE TYPES
// ============================================================================

export interface KnowledgeItem {
  id: string;
  domain: KnowledgeDomain;
  type: 'principle' | 'procedure' | 'troubleshooting' | 'reference' | 'calculation';
  title: string;
  content: string;
  summary: string;
  tags: string[];
  difficulty: 'beginner' | 'intermediate' | 'advanced' | 'expert';
  relevanceScore: number;
  lastAccessed: Date;
  source: string;
  references: string[];
  relatedTopics: string[];
  interactiveElements?: InteractiveElement[];
}

export interface InteractiveElement {
  type: 'calculator' | 'simulator' | 'visualizer' | 'quiz';
  title: string;
  description: string;
  component: string; // Component name to render
  parameters: Record<string, any>;
}

export type KnowledgeDomain = 
  | 'AnalyticalChemistry'
  | 'MolecularBiology'
  | 'ClinicalChemistry'
  | 'Microbiology'
  | 'Toxicology'
  | 'Pharmacology'
  | 'QualityAssurance'
  | 'Instrumentation'
  | 'DataAnalysis'
  | 'RegulatoryCompliance';

// ============================================================================
// COMPLIANCE AND AUDIT TYPES
// ============================================================================

export interface ComplianceFramework {
  id: string;
  name: string;
  version: string;
  requirements: ComplianceRequirement[];
  lastAssessment: Date;
  nextAssessment: Date;
  overallScore: number;
  status: 'compliant' | 'non_compliant' | 'under_review' | 'pending';
}

export interface ComplianceRequirement {
  id: string;
  section: string;
  title: string;
  description: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
  status: 'met' | 'not_met' | 'partial' | 'not_applicable';
  evidence: string[];
  lastReview: Date;
  assignedTo: string;
  dueDate: Date;
}

export interface AuditRecord {
  id: string;
  timestamp: Date;
  userId: string;
  action: string;
  entity: string;
  entityId: string;
  oldValue?: any;
  newValue?: any;
  sessionId: string;
  ipAddress: string;
  userAgent: string;
  result: 'success' | 'failure' | 'warning';
  details?: string;
}

// ============================================================================
// STATISTICAL ANALYSIS TYPES
// ============================================================================

export interface StatisticalAnalysis {
  id: string;
  type: 'descriptive' | 'regression' | 'anova' | 'correlation' | 'outlier_detection';
  name: string;
  description: string;
  inputData: any[];
  results: StatisticalResults;
  parameters: Record<string, any>;
  timestamp: Date;
  createdBy: string;
}

export interface StatisticalResults {
  summary: {
    n: number;
    mean?: number;
    median?: number;
    standardDeviation?: number;
    variance?: number;
    minimum?: number;
    maximum?: number;
    range?: number;
    quartiles?: [number, number, number];
  };
  hypothesis?: {
    nullHypothesis: string;
    alternativeHypothesis: string;
    pValue: number;
    testStatistic: number;
    criticalValue: number;
    conclusion: string;
  };
  correlation?: {
    coefficient: number;
    pValue: number;
    significance: 'significant' | 'not_significant';
  };
  regression?: {
    equation: string;
    rSquared: number;
    slope: number;
    intercept: number;
    standardError: number;
  };
  outliers?: {
    method: string;
    values: any[];
    indices: number[];
  };
}

// ============================================================================
// STAGE SYSTEM CORE TYPES
// ============================================================================

export interface StageComponent {
  id: string;
  type: StageComponentType;
  state: ComponentState;
  priority: number;
  data: ComponentData;
  metadata?: {
    lastUpdated: Date;
    relevanceScore: number;
    userInteractions: number;
  };
}

export type StageComponentType = 
  | 'SampleTracker'
  | 'TestCatalog'
  | 'InstrumentStatus'
  | 'QualityControl'
  | 'WorkflowDesigner'
  | 'DataVisualization'
  | 'KnowledgeExplorer'
  | 'ComplianceDashboard'
  | 'SafetyMonitor'
  | 'InventoryManager'
  | 'ReportGenerator'
  | 'ProtocolLibrary'
  | 'CalibrationScheduler'
  | 'AuditTrailViewer'
  | 'TrendingAnalysis'
  | 'StatisticalTools'
  | 'MolecularViewer'
  | 'ChromatogramDisplay'
  | 'SpectralAnalysis'
  | 'BatchProcessor';

export type ComponentState = 'Inactive' | 'Loading' | 'Active' | 'Updating' | 'Error' | 'Cached';

export interface ComponentData {
  samples?: Sample[];
  tests?: Test[];
  instruments?: Instrument[];
  workflows?: Workflow[];
  knowledge?: KnowledgeItem[];
  visualizations?: VisualizationData[];
  actions?: ActionItem[];
  alerts?: Alert[];
}

export interface ConversationContext {
  conversationId: string;
  messages: ChatMessage[];
  entities: ExtractedEntity[];
  intent: string;
  keywords: string[];
  lastUpdate: Date;
  confidence: number;
}

export interface ActionItem {
  id: string;
  type: string;
  label: string;
  description: string;
  icon: string;
  priority: 'low' | 'medium' | 'high' | 'critical';
  onExecute: () => void;
  permissions?: string[];
}

// ============================================================================
// TLA+ VALIDATED LIMS STAGE SYSTEM TYPES
// ============================================================================

// TLA+ validated system states from LimsStageSystem.tla
export type SystemState = 
  | 'INITIALIZING'
  | 'READY' 
  | 'PROCESSING_CHAT'
  | 'UPDATING_STAGE'
  | 'ERROR'
  | 'MAINTENANCE';

// TLA+ validated chat message types (subset focused on core LIMS functionality)
export type ChatMessageType = 
  | 'SAMPLE_INQUIRY'
  | 'TEST_REQUEST'
  | 'KNOWLEDGE_QUERY'
  | 'GENERAL_QUERY';

// TLA+ validated component types for LIMS focus
export type LimsComponentType = 
  | 'SAMPLE_TRACKER'
  | 'TEST_CATALOG'
  | 'KNOWLEDGE_BASE';

// Enhanced ChatMessage with TLA+ validated message types
export interface LimsChatMessage extends ChatMessage {
  type: ChatMessageType;
  limsType?: ChatMessageType;
  triggeredComponents: string[];
}

// TLA+ Stage Context matching specification
export interface LimsStageContext {
  currentFocus: ChatMessageType | 'GENERAL';
  activeWorkflow: LimsComponentType | 'NONE';
  knowledgeBase: Set<string>;
  userPreferences: 'DEFAULT' | string;
}

// ============================================================================
// EXISTING TYPES CONTINUE BELOW
// ============================================================================
