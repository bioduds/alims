// ============================================================================
// COMPREHENSIVE STAGE TYPE DEFINITIONS - ALL COMPONENTS
// ============================================================================

// Base interfaces for all stage components
export interface BaseStageComponent {
  id: string;
  type: StageComponentType;
  title: string;
  status: ComponentStatus;
  lastUpdated: Date;
  refreshInterval?: number;
  permissions: ComponentPermissions;
  dependencies: string[];
}

export interface ComponentPermissions {
  view: boolean;
  edit: boolean;
  execute: boolean;
  admin: boolean;
  requiredRole: UserRole;
}

export type ComponentStatus = 'loading' | 'active' | 'error' | 'offline' | 'maintenance';
export type UserRole = 'admin' | 'scientist' | 'technician' | 'observer' | 'guest';

// Extended stage component types covering all LIMS, Science, and Knowledge domains
export type StageComponentType = 
  // LIMS Components
  | 'SampleTracker' | 'TestCatalog' | 'InstrumentStatus' | 'QualityControl'
  | 'WorkflowDesigner' | 'ComplianceDashboard' | 'SafetyMonitor' | 'InventoryManager'
  | 'AuditTrailViewer' | 'CalibrationScheduler' | 'BatchProcessor' | 'ReportGenerator'
  | 'ProtocolLibrary' | 'ChainOfCustody' | 'ResourceScheduler'
  // Science Components  
  | 'DataVisualization' | 'StatisticalTools' | 'TrendingAnalysis' | 'MolecularViewer'
  | 'ChromatogramDisplay' | 'SpectralAnalysis' | 'MassSpecViewer' | 'SequenceAnalyzer'
  | 'StructurePredictor' | 'PathwayMapper' | 'DoseResponseAnalyzer' | 'KineticsModeler'
  | 'ThermodynamicsCalc' | 'ChemicalProperties' | 'FormulaCalculator'
  // Knowledge Components
  | 'KnowledgeExplorer' | 'LiteratureSearch' | 'MethodDatabase' | 'RegulatoryGuidance'
  | 'SafetyDataSheets' | 'TechnicalSupport' | 'TrainingModules' | 'ExpertSystem'
  | 'CalculationWizard' | 'ConversionTools' | 'ReferenceLibrary' | 'TroubleshootingGuide'
  | 'BestPractices' | 'NewsAndUpdates' | 'PersonalNotebook'
  // Default
  | 'DefaultStage';

// ============================================================================
// LIMS COMPONENT INTERFACES
// ============================================================================

export interface SampleTrackerData {
  current_samples: Sample[];
  location_tracking: LocationTracking[];
  quick_actions: SampleAction[];
  visualizations: SampleVisualization[];
  alerts: SampleAlert[];
  batch_operations: BatchOperation[];
}

export interface Sample {
  id: string;
  barcode: string;
  status: SampleStatus;
  sample_type: string;
  volume: number;
  units: string;
  location: string;
  tests_assigned: string[];
  priority: SamplePriority;
  collection_date: Date;
  received_date: Date;
  expected_completion: Date;
  patient_info: PatientInfo;
  chain_of_custody: CustodyRecord[];
  storage_conditions: StorageConditions;
  expiration_date?: Date;
}

export type SampleStatus = 'received' | 'in_progress' | 'completed' | 'archived' | 'rejected' | 'expired';
export type SamplePriority = 'routine' | 'urgent' | 'stat' | 'critical';

export interface TestCatalogData {
  available_tests: TestDefinition[];
  method_details: MethodDetail[];
  test_combinations: TestCombination[];
  ordering_interface: OrderingInterface;
  test_performance: TestPerformance[];
}

export interface TestDefinition {
  test_code: string;
  test_name: string;
  category: string;
  method_code: string;
  analytes: AnalyteInfo[];
  sample_types: string[];
  sample_volume_required: number;
  container_type: string;
  turnaround_time: TurnaroundTime;
  cost: TestCost;
  accreditation_status: AccreditationStatus;
  clinical_significance: string;
  interpretation_guidelines: string;
  reference_ranges: ReferenceRange[];
  critical_values: CriticalValue[];
  interfering_substances: string[];
  storage_requirements: string;
  stability_data: StabilityInfo[];
}

export interface InstrumentStatusData {
  instruments: InstrumentInfo[];
  system_controls: InstrumentControl[];
  diagnostic_tools: DiagnosticTool[];
  maintenance_tracking: MaintenanceInfo[];
  performance_monitoring: PerformanceMetrics[];
}

export interface InstrumentInfo {
  instrument_id: string;
  name: string;
  model: string;
  manufacturer: string;
  serial_number: string;
  location: string;
  status: InstrumentStatus;
  current_run: CurrentRun;
  queue_management: QueueManagement;
  performance_metrics: InstrumentPerformance;
  calibration_status: CalibrationStatus;
  maintenance_tracking: MaintenanceTracking;
  consumables: ConsumableStatus[];
}

export type InstrumentStatus = 'online' | 'offline' | 'maintenance' | 'error' | 'calibration' | 'standby';

export interface QualityControlData {
  qc_materials: QCMaterial[];
  trending_analysis: TrendingAnalysis;
  outlier_detection: OutlierDetection;
  corrective_actions: CorrectiveAction[];
  statistical_analysis: StatisticalQCAnalysis;
}

export interface QCMaterial {
  material_id: string;
  material_name: string;
  level: QCLevel;
  lot_number: string;
  expiration_date: Date;
  target_values: TargetValue[];
  current_statistics: QCStatistics;
  control_limits: ControlLimits;
  westgard_rules: WestgardRules;
}

export type QCLevel = 'low' | 'normal' | 'high' | 'critical';

// ============================================================================
// SCIENCE COMPONENT INTERFACES
// ============================================================================

export interface DataVisualizationData {
  chart_types: ChartTypeConfig[];
  data_sources: DataSource[];
  interactive_features: InteractiveFeature[];
  statistical_overlays: StatisticalOverlay[];
  customization_options: CustomizationOption[];
  export_options: ExportOption[];
}

export interface ChartTypeConfig {
  type: ChartType;
  config: ChartConfiguration;
  data_requirements: DataRequirement[];
  supported_interactions: InteractionType[];
}

export type ChartType = 'line' | 'scatter' | 'bar' | 'histogram' | 'box_plot' | 'control_chart' 
                      | 'heatmap' | '3d_surface' | 'violin_plot' | 'density_plot';

export interface StatisticalToolsData {
  descriptive_statistics: DescriptiveStats;
  hypothesis_testing: HypothesisTest[];
  regression_analysis: RegressionAnalysis[];
  time_series_analysis: TimeSeriesAnalysis;
  method_validation: MethodValidation[];
  power_analysis: PowerAnalysis;
}

export interface DescriptiveStats {
  summary_statistics: SummaryStatistics;
  distribution_analysis: DistributionAnalysis;
  normality_tests: NormalityTest[];
  outlier_detection_methods: OutlierMethod[];
}

export interface MolecularViewerData {
  molecular_structures: MolecularStructure[];
  analysis_tools: MolecularAnalysisTool[];
  property_calculations: PropertyCalculation[];
  interaction_analysis: InteractionAnalysis[];
  visualization_settings: VisualizationSettings;
}

export interface MolecularStructure {
  structure_id: string;
  name: string;
  formula: string;
  molecular_weight: number;
  structure_format: StructureFormat;
  structure_data: string;
  visualization_style: VisualizationStyle;
  color_scheme: ColorScheme;
}

export type StructureFormat = 'PDB' | 'MOL' | 'SDF' | 'SMILES' | 'InChI';
export type VisualizationStyle = 'ball_stick' | 'space_fill' | 'wireframe' | 'cartoon' | 'surface';

export interface SpectralAnalysisData {
  spectra: SpectrumData[];
  analysis_tools: SpectralAnalysisTool[];
  peak_detection: PeakDetection;
  library_search: LibrarySearch;
  identification_results: IdentificationResult[];
}

export interface SpectrumData {
  spectrum_id: string;
  spectrum_type: SpectrumType;
  measurement_conditions: MeasurementConditions;
  data_points: DataPoint[];
  metadata: SpectrumMetadata;
}

export type SpectrumType = 'UV_VIS' | 'IR' | 'NMR' | 'MS' | 'Raman' | 'XRD';

// ============================================================================
// KNOWLEDGE COMPONENT INTERFACES
// ============================================================================

export interface KnowledgeExplorerData {
  knowledge_domains: KnowledgeDomain[];
  content_types: ContentType[];
  interactive_features: KnowledgeInteractiveFeature[];
  learning_pathways: LearningPathway[];
  personalized_content: PersonalizedContent[];
}

export interface KnowledgeDomain {
  domain_id: string;
  domain_name: string;
  description: string;
  concepts: Concept[];
  relationships: ConceptRelationship[];
  expertise_level: ExpertiseLevel;
}

export type ExpertiseLevel = 'beginner' | 'intermediate' | 'advanced' | 'expert';

export interface LiteratureSearchData {
  search_engines: SearchEngine[];
  search_results: SearchResult[];
  citation_tools: CitationTool[];
  full_text_access: FullTextAccess[];
  research_trends: ResearchTrend[];
}

export interface SearchResult {
  title: string;
  authors: string[];
  journal: string;
  publication_date: Date;
  doi: string;
  abstract: string;
  relevance_score: number;
  citation_count: number;
  access_type: AccessType;
}

export type AccessType = 'open_access' | 'subscription' | 'pay_per_view' | 'institutional';

export interface CalculationWizardData {
  calculation_categories: CalculationCategory[];
  formula_library: FormulaDefinition[];
  step_by_step_guides: CalculationGuide[];
  unit_conversion: UnitConversion[];
  validation_rules: ValidationRule[];
}

export interface FormulaDefinition {
  formula_id: string;
  name: string;
  description: string;
  formula: string;
  parameters: Parameter[];
  units: UnitDefinition[];
  examples: CalculationExample[];
  references: Reference[];
}

// ============================================================================
// ADVANCED VISUALIZATION INTERFACES
// ============================================================================

export interface ChromatogramDisplayData {
  chromatograms: ChromatogramData[];
  peak_detection: PeakDetectionSettings;
  integration_methods: IntegrationMethod[];
  baseline_correction: BaselineCorrection[];
  comparison_tools: ComparisonTool[];
}

export interface ChromatogramData {
  chromatogram_id: string;
  sample_id: string;
  method_name: string;
  acquisition_date: Date;
  time_points: number[];
  intensity_values: number[];
  peaks: Peak[];
  integration_results: IntegrationResult[];
}

export interface Peak {
  peak_id: string;
  retention_time: number;
  height: number;
  area: number;
  width: number;
  tailing_factor: number;
  theoretical_plates: number;
  compound_id?: string;
}

export interface PathwayMapperData {
  biological_pathways: BiologicalPathway[];
  pathway_visualization: PathwayVisualization;
  interaction_networks: InteractionNetwork[];
  enrichment_analysis: EnrichmentAnalysis[];
}

export interface BiologicalPathway {
  pathway_id: string;
  name: string;
  organism: string;
  category: PathwayCategory;
  components: PathwayComponent[];
  interactions: PathwayInteraction[];
  references: Reference[];
}

export type PathwayCategory = 'metabolic' | 'signaling' | 'genetic' | 'regulatory' | 'disease';

// ============================================================================
// WORKFLOW AND AUTOMATION INTERFACES
// ============================================================================

export interface WorkflowDesignerData {
  workflow_templates: WorkflowTemplate[];
  custom_workflows: CustomWorkflow[];
  automation_rules: AutomationRule[];
  execution_history: ExecutionHistory[];
  performance_metrics: WorkflowMetrics[];
}

export interface WorkflowTemplate {
  template_id: string;
  name: string;
  description: string;
  category: WorkflowCategory;
  steps: WorkflowStep[];
  parameters: WorkflowParameter[];
  validation_rules: WorkflowValidation[];
}

export type WorkflowCategory = 'sample_processing' | 'analysis' | 'quality_control' | 'reporting' | 'maintenance';

export interface BatchProcessorData {
  batch_definitions: BatchDefinition[];
  active_batches: ActiveBatch[];
  batch_history: BatchHistory[];
  optimization_suggestions: OptimizationSuggestion[];
}

export interface BatchDefinition {
  batch_id: string;
  name: string;
  description: string;
  sample_criteria: SampleCriteria[];
  processing_steps: ProcessingStep[];
  quality_gates: QualityGate[];
  resource_requirements: ResourceRequirement[];
}

// ============================================================================
// COMPLIANCE AND SAFETY INTERFACES
// ============================================================================

export interface ComplianceDashboardData {
  regulatory_frameworks: RegulatoryFramework[];
  compliance_status: ComplianceStatus[];
  audit_schedules: AuditSchedule[];
  documentation_tracking: DocumentationTracking[];
  training_compliance: TrainingCompliance[];
}

export interface RegulatoryFramework {
  framework_id: string;
  name: string;
  jurisdiction: string;
  requirements: ComplianceRequirement[];
  deadlines: ComplianceDeadline[];
  status: ComplianceFrameworkStatus;
}

export type ComplianceFrameworkStatus = 'compliant' | 'non_compliant' | 'pending' | 'under_review';

export interface SafetyMonitorData {
  safety_protocols: SafetyProtocol[];
  active_alerts: SafetyAlert[];
  incident_reports: IncidentReport[];
  hazard_assessments: HazardAssessment[];
  emergency_procedures: EmergencyProcedure[];
}

export interface SafetyAlert {
  alert_id: string;
  type: SafetyAlertType;
  severity: AlertSeverity;
  location: string;
  description: string;
  timestamp: Date;
  status: AlertStatus;
  assigned_to: string;
  response_required: boolean;
}

export type SafetyAlertType = 'chemical_exposure' | 'equipment_malfunction' | 'environmental' | 'procedural';
export type AlertSeverity = 'low' | 'medium' | 'high' | 'critical';
export type AlertStatus = 'active' | 'acknowledged' | 'investigating' | 'resolved';

// ============================================================================
// INVENTORY AND RESOURCE MANAGEMENT
// ============================================================================

export interface InventoryManagerData {
  inventory_items: InventoryItem[];
  stock_levels: StockLevel[];
  ordering_system: OrderingSystem;
  supplier_management: SupplierManagement[];
  cost_tracking: CostTracking[];
}

export interface InventoryItem {
  item_id: string;
  name: string;
  category: InventoryCategory;
  supplier: string;
  catalog_number: string;
  description: string;
  storage_requirements: StorageRequirements;
  safety_information: SafetyInformation;
  cost_per_unit: number;
  current_stock: number;
  reorder_point: number;
  maximum_stock: number;
  expiration_tracking: boolean;
}

export type InventoryCategory = 'reagents' | 'consumables' | 'standards' | 'equipment' | 'safety';

// ============================================================================
// REPORTING AND DOCUMENTATION
// ============================================================================

export interface ReportGeneratorData {
  report_templates: ReportTemplate[];
  active_reports: ActiveReport[];
  report_history: ReportHistory[];
  distribution_lists: DistributionList[];
  automation_schedules: ReportSchedule[];
}

export interface ReportTemplate {
  template_id: string;
  name: string;
  description: string;
  report_type: ReportType;
  data_sources: ReportDataSource[];
  layout: ReportLayout;
  parameters: ReportParameter[];
  output_formats: OutputFormat[];
}

export type ReportType = 'analytical' | 'quality_control' | 'compliance' | 'inventory' | 'performance';
export type OutputFormat = 'PDF' | 'Excel' | 'CSV' | 'HTML' | 'XML';

// ============================================================================
// EXPERT SYSTEM AND AI INTERFACES
// ============================================================================

export interface ExpertSystemData {
  knowledge_base: ExpertKnowledgeBase;
  inference_engine: InferenceEngine;
  consultation_history: ConsultationHistory[];
  decision_trees: DecisionTree[];
  confidence_scores: ConfidenceScore[];
}

export interface ExpertKnowledgeBase {
  rules: ExpertRule[];
  facts: ExpertFact[];
  heuristics: ExpertHeuristic[];
  case_studies: CaseStudy[];
}

export interface TechnicalSupportData {
  support_categories: SupportCategory[];
  troubleshooting_guides: TroubleshootingGuide[];
  faq_database: FAQ[];
  ticket_system: SupportTicket[];
  knowledge_articles: KnowledgeArticle[];
}

// ============================================================================
// CONTEXT ANALYSIS AND STAGE ORCHESTRATION
// ============================================================================

export interface ConversationContext {
  messages: ChatMessage[];
  entities: ExtractedEntity[];
  keywords: string[];
  domain_context: KnowledgeDomain[];
  confidence_scores: Record<StageComponentType, number>;
  user_intent: UserIntent;
  conversation_flow: ConversationFlow;
}

export interface ChatMessage {
  id: string;
  content: string;
  timestamp: Date;
  sender: 'user' | 'assistant';
  message_type: MessageType;
  context_analysis: MessageContext;
}

export type MessageType = 'question' | 'request' | 'command' | 'information' | 'clarification';

export interface ExtractedEntity {
  entity_type: EntityType;
  entity_value: string;
  confidence: number;
  start_position: number;
  end_position: number;
}

export type EntityType = 'sample_id' | 'test_name' | 'instrument_id' | 'chemical_name' | 'person_name' | 'date' | 'number';

export interface UserIntent {
  primary_intent: IntentType;
  secondary_intents: IntentType[];
  confidence: number;
  required_actions: ActionItem[];
}

export type IntentType = 'information_seeking' | 'task_execution' | 'problem_solving' | 'learning' | 'monitoring';

export interface ActionItem {
  action_id: string;
  action_type: ActionType;
  description: string;
  priority: ActionPriority;
  required_permissions: string[];
  estimated_duration: number;
  dependencies: string[];
}

export type ActionType = 'view' | 'create' | 'update' | 'delete' | 'execute' | 'analyze' | 'report';
export type ActionPriority = 'low' | 'medium' | 'high' | 'urgent';

// ============================================================================
// STAGE COMPONENT CONFIGURATIONS
// ============================================================================

export interface StageComponent {
  component_type: StageComponentType;
  configuration: ComponentConfiguration;
  data: ComponentData;
  state: ComponentState;
  interactions: ComponentInteraction[];
}

export interface ComponentConfiguration {
  display_mode: DisplayMode;
  refresh_interval: number;
  data_filters: DataFilter[];
  visualization_settings: VisualizationSettings;
  user_preferences: UserPreferences;
}

export type DisplayMode = 'full' | 'compact' | 'summary' | 'detailed';

export interface ComponentData {
  primary_data: any;
  secondary_data: any;
  metadata: DataMetadata;
  last_updated: Date;
  data_quality: DataQuality;
}

export interface ComponentState {
  loading: boolean;
  error: string | null;
  warnings: string[];
  user_interactions: UserInteraction[];
  component_health: ComponentHealth;
}

export type ComponentHealth = 'healthy' | 'degraded' | 'critical' | 'offline';

// ============================================================================
// STAGE SYSTEM ORCHESTRATION
// ============================================================================

export interface StageSystem {
  active_components: StageComponent[];
  layout_configuration: LayoutConfiguration;
  context_analyzer: ContextAnalyzer;
  component_registry: ComponentRegistry;
  data_coordinator: DataCoordinator;
  user_session: UserSession;
}

export interface LayoutConfiguration {
  layout_type: LayoutType;
  grid_configuration: GridConfiguration;
  responsive_breakpoints: ResponsiveBreakpoint[];
  theme_settings: ThemeSettings;
}

export type LayoutType = 'single' | 'dual' | 'grid' | 'tabbed' | 'accordion' | 'dashboard';

export interface ComponentRegistry {
  available_components: Record<StageComponentType, ComponentDefinition>;
  component_dependencies: Record<StageComponentType, string[]>;
  component_priorities: Record<StageComponentType, number>;
  loading_strategies: Record<StageComponentType, LoadingStrategy>;
}

export interface DataCoordinator {
  data_sources: DataSource[];
  update_strategies: UpdateStrategy[];
  cache_policies: CachePolicy[];
  synchronization_rules: SynchronizationRule[];
}

// This comprehensive type system ensures complete coverage of all possible
// LIMS, Science, and Knowledge-based components in the ALIMS Stage System
