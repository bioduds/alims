// ============================================================================
// SUPPORTING TYPE DEFINITIONS FOR COMPREHENSIVE STAGE SYSTEM
// ============================================================================

// Common utility types
export interface TimestampedEntity {
  created_at: Date;
  updated_at: Date;
  created_by: string;
  updated_by: string;
}

export interface AuditableEntity extends TimestampedEntity {
  version: number;
  audit_trail: AuditRecord[];
}

export interface AuditRecord {
  timestamp: Date;
  user_id: string;
  action: string;
  old_value?: any;
  new_value?: any;
  reason?: string;
}

// ============================================================================
// SAMPLE MANAGEMENT TYPES
// ============================================================================

export interface LocationTracking {
  location_id: string;
  location_name: string;
  location_type: LocationType;
  rack_id?: string;
  position?: string;
  temperature: number;
  humidity: number;
  environmental_conditions: EnvironmentalCondition[];
  last_moved: Date;
  moved_by: string;
  coordinates?: Coordinates;
}

export type LocationType = 'freezer' | 'refrigerator' | 'room_temp' | 'incubator' | 'storage_room' | 'workbench';

export interface EnvironmentalCondition {
  parameter: string;
  value: number;
  units: string;
  timestamp: Date;
  within_limits: boolean;
}

export interface Coordinates {
  x: number;
  y: number;
  z?: number;
}

export interface SampleAction {
  action_id: string;
  action_name: string;
  action_type: SampleActionType;
  description: string;
  required_permissions: string[];
  estimated_duration: number;
  parameters: ActionParameter[];
}

export type SampleActionType = 'register' | 'update_status' | 'assign_tests' | 'transfer' | 'dispose' | 'print_labels';

export interface ActionParameter {
  parameter_name: string;
  parameter_type: string;
  required: boolean;
  default_value?: any;
  validation_rules: ValidationRule[];
}

export interface ValidationRule {
  rule_type: string;
  rule_value: any;
  error_message: string;
}

export interface SampleVisualization {
  visualization_id: string;
  visualization_type: SampleVisualizationType;
  title: string;
  description: string;
  data_source: string;
  configuration: VisualizationConfiguration;
}

export type SampleVisualizationType = 'flow_diagram' | 'status_timeline' | 'location_heatmap' | 'turnaround_metrics';

export interface VisualizationConfiguration {
  chart_type: string;
  color_scheme: string;
  dimensions: ChartDimensions;
  interactive_features: string[];
  export_formats: string[];
}

export interface ChartDimensions {
  width: number;
  height: number;
  margin: Margin;
}

export interface Margin {
  top: number;
  right: number;
  bottom: number;
  left: number;
}

export interface SampleAlert {
  alert_id: string;
  alert_type: SampleAlertType;
  severity: 'low' | 'medium' | 'high' | 'critical';
  message: string;
  sample_id: string;
  timestamp: Date;
  acknowledged: boolean;
  resolved: boolean;
  assigned_to?: string;
}

export type SampleAlertType = 'expiring' | 'temperature_excursion' | 'missing' | 'overdue' | 'contamination';

export interface BatchOperation {
  operation_id: string;
  operation_type: BatchOperationType;
  sample_ids: string[];
  parameters: OperationParameter[];
  status: OperationStatus;
  scheduled_time?: Date;
  execution_time?: Date;
  completion_time?: Date;
  operator: string;
}

export type BatchOperationType = 'status_update' | 'test_assignment' | 'location_transfer' | 'disposal' | 'archival';
export type OperationStatus = 'scheduled' | 'in_progress' | 'completed' | 'failed' | 'cancelled';

export interface OperationParameter {
  parameter_name: string;
  parameter_value: any;
  parameter_type: string;
}

export interface PatientInfo {
  patient_id?: string;
  age?: number;
  gender?: string;
  clinical_notes?: string;
  diagnosis_codes?: string[];
  physician?: string;
  collection_site?: string;
  privacy_level: PrivacyLevel;
}

export type PrivacyLevel = 'public' | 'restricted' | 'confidential' | 'anonymized';

export interface CustodyRecord {
  timestamp: Date;
  user_id: string;
  action: CustodyAction;
  location_from?: string;
  location_to?: string;
  notes?: string;
  signature?: string;
  witness?: string;
}

export type CustodyAction = 'received' | 'transferred' | 'analyzed' | 'stored' | 'disposed' | 'shipped';

export interface StorageConditions {
  temperature_range: TemperatureRange;
  humidity_range: HumidityRange;
  light_conditions: LightConditions;
  atmosphere: AtmosphereConditions;
  special_requirements: string[];
}

export interface TemperatureRange {
  min_temp: number;
  max_temp: number;
  units: string;
  tolerance: number;
}

export interface HumidityRange {
  min_humidity: number;
  max_humidity: number;
  tolerance: number;
}

export interface LightConditions {
  light_exposure: 'dark' | 'ambient' | 'protected' | 'direct';
  uv_protection: boolean;
}

export interface AtmosphereConditions {
  atmosphere_type: 'air' | 'nitrogen' | 'argon' | 'vacuum';
  oxygen_level?: number;
  co2_level?: number;
}

// ============================================================================
// TEST AND METHOD TYPES
// ============================================================================

export interface MethodDetail {
  method_id: string;
  principle: string;
  instrumentation: string[];
  reagents: ReagentInfo[];
  calibration_procedure: string;
  qc_requirements: QCRequirement[];
  precision_data: PrecisionData;
  accuracy_data: AccuracyData;
  linearity_range: LinearityData;
  detection_limit: number;
  quantitation_limit: number;
  reportable_range: RangeInfo;
  matrix_effects: MatrixEffect[];
}

export interface ReagentInfo {
  reagent_id: string;
  name: string;
  manufacturer: string;
  catalog_number: string;
  lot_number: string;
  expiration_date: Date;
  concentration: string;
  volume_required: number;
  storage_conditions: StorageConditions;
}

export interface QCRequirement {
  qc_type: QCType;
  frequency: string;
  acceptance_criteria: AcceptanceCriteria;
  corrective_actions: string[];
}

export type QCType = 'calibration_verification' | 'control_material' | 'duplicate_analysis' | 'spike_recovery';

export interface AcceptanceCriteria {
  parameter: string;
  target_value?: number;
  tolerance: number;
  units: string;
  statistical_method: string;
}

export interface PrecisionData {
  within_run_cv: number;
  between_run_cv: number;
  between_day_cv: number;
  total_cv: number;
  n_replicates: number;
  concentration_levels: ConcentrationLevel[];
}

export interface ConcentrationLevel {
  level_name: string;
  nominal_value: number;
  measured_values: number[];
  statistics: StatisticalSummary;
}

export interface StatisticalSummary {
  mean: number;
  median: number;
  std_dev: number;
  variance: number;
  cv_percent: number;
  min_value: number;
  max_value: number;
  n_count: number;
}

export interface AccuracyData {
  bias_percent: number;
  recovery_percent: number;
  reference_method: string;
  comparison_data: ComparisonData[];
}

export interface ComparisonData {
  sample_id: string;
  reference_value: number;
  test_value: number;
  difference: number;
  percent_difference: number;
}

export interface LinearityData {
  correlation_coefficient: number;
  slope: number;
  intercept: number;
  std_error_slope: number;
  std_error_intercept: number;
  concentration_range: RangeInfo;
  data_points: LinearityPoint[];
}

export interface LinearityPoint {
  expected_value: number;
  observed_value: number;
  residual: number;
  percent_recovery: number;
}

export interface RangeInfo {
  lower_limit: number;
  upper_limit: number;
  units: string;
  confidence_level: number;
}

export interface MatrixEffect {
  matrix_type: string;
  interference_type: string;
  magnitude: number;
  mitigation_strategy: string;
}

export interface TestCombination {
  combination_id: string;
  combination_type: TestCombinationType;
  tests: string[];
  logic_rule: string;
  clinical_rationale: string;
}

export type TestCombinationType = 'recommended_panel' | 'reflexive_testing' | 'add_on_test' | 'cascade_testing';

export interface OrderingInterface {
  quick_order_enabled: boolean;
  batch_order_enabled: boolean;
  standing_orders_enabled: boolean;
  order_sets_enabled: boolean;
  approval_workflow: ApprovalWorkflow;
}

export interface ApprovalWorkflow {
  approval_required: boolean;
  approval_criteria: ApprovalCriteria[];
  escalation_rules: EscalationRule[];
}

export interface ApprovalCriteria {
  criterion_type: string;
  threshold_value: any;
  approver_role: string;
}

export interface EscalationRule {
  condition: string;
  escalation_time: number;
  escalation_target: string;
}

export interface TestPerformance {
  test_id: string;
  performance_period: DateRange;
  volume_statistics: VolumeStatistics;
  turnaround_statistics: TurnaroundStatistics;
  quality_metrics: TestQualityMetrics;
}

export interface DateRange {
  start_date: Date;
  end_date: Date;
}

export interface VolumeStatistics {
  total_tests: number;
  average_daily: number;
  peak_daily: number;
  trend: TrendDirection;
}

export type TrendDirection = 'increasing' | 'decreasing' | 'stable' | 'variable';

export interface TurnaroundStatistics {
  average_tat: number;
  median_tat: number;
  percentile_90: number;
  percentile_95: number;
  on_time_delivery: number;
}

export interface TestQualityMetrics {
  error_rate: number;
  repeat_rate: number;
  critical_value_rate: number;
  customer_satisfaction: number;
}

export interface AnalyteInfo {
  analyte_id: string;
  name: string;
  abbreviation: string;
  units: string;
  reference_ranges: ReferenceRange[];
  critical_values: CriticalValue[];
  clinical_significance: string;
}

export interface ReferenceRange {
  population: string;
  age_range?: AgeRange;
  gender?: 'male' | 'female' | 'all';
  lower_limit: number;
  upper_limit: number;
  units: string;
  reference_method: string;
}

export interface AgeRange {
  min_age: number;
  max_age: number;
  age_units: 'days' | 'months' | 'years';
}

export interface CriticalValue {
  analyte_id: string;
  critical_low?: number;
  critical_high?: number;
  units: string;
  notification_protocol: NotificationProtocol;
}

export interface NotificationProtocol {
  notification_time: number;
  escalation_time: number;
  contact_list: ContactInfo[];
  verification_required: boolean;
}

export interface ContactInfo {
  name: string;
  role: string;
  phone: string;
  email: string;
  priority: number;
}

export interface TurnaroundTime {
  routine_hours: number;
  urgent_hours: number;
  stat_hours: number;
  critical_hours: number;
  factors_affecting_tat: string[];
}

export interface TestCost {
  internal_cost: number;
  external_cost: number;
  send_out_cost?: number;
  currency: string;
  cost_factors: CostFactor[];
}

export interface CostFactor {
  factor_name: string;
  factor_type: 'fixed' | 'variable' | 'overhead';
  amount: number;
  percentage?: number;
}

export type AccreditationStatus = 'CAP' | 'CLIA' | 'ISO15189' | 'non_accredited' | 'pending';

export interface StabilityInfo {
  storage_condition: string;
  stability_period: number;
  stability_units: 'hours' | 'days' | 'weeks' | 'months';
  degradation_rate?: number;
  validation_study: string;
}

// ============================================================================
// INSTRUMENT AND EQUIPMENT TYPES
// ============================================================================

export interface InstrumentControl {
  control_id: string;
  control_name: string;
  control_type: InstrumentControlType;
  description: string;
  required_permissions: string[];
  safety_interlocks: SafetyInterlock[];
}

export type InstrumentControlType = 'start_run' | 'pause_run' | 'stop_run' | 'emergency_stop' | 'initiate_shutdown' | 'run_diagnostics';

export interface SafetyInterlock {
  interlock_type: string;
  condition: string;
  action: string;
  override_allowed: boolean;
  override_authorization: string;
}

export interface DiagnosticTool {
  tool_id: string;
  tool_name: string;
  tool_type: DiagnosticToolType;
  description: string;
  output_format: string;
  execution_time: number;
}

export type DiagnosticToolType = 'system_logs' | 'error_history' | 'performance_trends' | 'calibration_history' | 'component_status';

export interface MaintenanceInfo {
  maintenance_id: string;
  maintenance_type: MaintenanceType;
  scheduled_date: Date;
  estimated_duration: number;
  required_parts: MaintenancePart[];
  required_personnel: string[];
  documentation: MaintenanceDocument[];
}

export type MaintenanceType = 'preventive' | 'corrective' | 'calibration' | 'validation' | 'upgrade';

export interface MaintenancePart {
  part_number: string;
  part_name: string;
  quantity: number;
  supplier: string;
  cost: number;
}

export interface MaintenanceDocument {
  document_type: string;
  document_name: string;
  version: string;
  location: string;
}

export interface PerformanceMetrics {
  metric_name: string;
  metric_value: number;
  metric_units: string;
  measurement_date: Date;
  target_value?: number;
  tolerance?: number;
  trend: TrendDirection;
}

export interface CurrentRun {
  run_id: string;
  sample_count: number;
  progress_percent: number;
  estimated_completion: Date;
  operator: string;
  run_parameters: RunParameter[];
}

export interface RunParameter {
  parameter_name: string;
  parameter_value: any;
  parameter_units?: string;
}

export interface QueueManagement {
  pending_samples: number;
  estimated_wait_time: string;
  priority_samples: number;
  queue_optimization: QueueOptimization;
}

export interface QueueOptimization {
  optimization_algorithm: string;
  efficiency_score: number;
  recommended_actions: string[];
}

export interface InstrumentPerformance {
  uptime_percent: number;
  daily_throughput: number;
  error_rate: number;
  calibration_stability: number;
  maintenance_compliance: number;
  efficiency_metrics: EfficiencyMetric[];
}

export interface EfficiencyMetric {
  metric_name: string;
  current_value: number;
  target_value: number;
  units: string;
  improvement_potential: number;
}

export interface CalibrationStatus {
  last_calibration: Date;
  next_due: Date;
  calibration_type: CalibrationType;
  results: CalibrationResult[];
  stability_trend: StabilityTrend;
  compliance_status: ComplianceStatus;
}

export type CalibrationType = 'single_point' | 'multi_point' | 'blank' | 'slope_intercept' | 'non_linear';

export interface CalibrationResult {
  calibrator_level: string;
  expected_value: number;
  measured_value: number;
  difference: number;
  percent_difference: number;
  acceptance_status: 'pass' | 'fail' | 'warning';
}

export interface StabilityTrend {
  trend_direction: TrendDirection;
  trend_magnitude: number;
  confidence_level: number;
  prediction_interval: number;
}

export interface ComplianceStatus {
  compliant: boolean;
  compliance_score: number;
  issues: ComplianceIssue[];
  recommendations: string[];
}

export interface ComplianceIssue {
  issue_type: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
  description: string;
  remediation_actions: string[];
}

export interface MaintenanceTracking {
  last_pm: Date;
  next_pm: Date;
  overdue_tasks: MaintenanceTask[];
  service_history: ServiceRecord[];
  cost_tracking: MaintenanceCost[];
}

export interface MaintenanceTask {
  task_id: string;
  task_description: string;
  due_date: Date;
  priority: 'low' | 'medium' | 'high' | 'critical';
  estimated_duration: number;
  required_skills: string[];
}

export interface ServiceRecord {
  service_date: Date;
  service_type: string;
  technician: string;
  description: string;
  parts_replaced: string[];
  cost: number;
  warranty_info?: WarrantyInfo;
}

export interface WarrantyInfo {
  warranty_type: string;
  expiration_date: Date;
  coverage_details: string;
}

export interface MaintenanceCost {
  cost_period: DateRange;
  total_cost: number;
  cost_breakdown: CostBreakdown[];
  cost_per_sample: number;
}

export interface CostBreakdown {
  category: string;
  amount: number;
  percentage: number;
}

export interface ConsumableStatus {
  consumable_id: string;
  name: string;
  current_level: number;
  capacity: number;
  units: string;
  reorder_point: number;
  estimated_depletion: Date;
  supplier_info: SupplierInfo;
}

export interface SupplierInfo {
  supplier_name: string;
  contact_info: ContactInfo;
  lead_time_days: number;
  cost_per_unit: number;
}

// ============================================================================
// QUALITY CONTROL TYPES
// ============================================================================

export interface TargetValue {
  analyte: string;
  target: number;
  uncertainty: number;
  units: string;
  confidence_level: number;
}

export interface QCStatistics {
  mean: number;
  std_dev: number;
  cv_percent: number;
  bias_percent: number;
  n_count: number;
  last_updated: Date;
  data_range: DateRange;
}

export interface ControlLimits {
  ucl: number;  // Upper Control Limit
  lcl: number;  // Lower Control Limit
  uwl: number;  // Upper Warning Limit
  lwl: number;  // Lower Warning Limit
  target: number;
  calculation_method: string;
}

export interface WestgardRules {
  rule_12s: RuleStatus;
  rule_13s: RuleStatus;
  rule_22s: RuleStatus;
  rule_r4s: RuleStatus;
  rule_41s: RuleStatus;
  rule_10x: RuleStatus;
}

export interface RuleStatus {
  rule_name: string;
  status: 'pass' | 'warning' | 'violation';
  last_violation?: Date;
  violation_count: number;
  description: string;
}

export interface TrendingAnalysis {
  levey_jennings_charts: LJChart[];
  cusum_analysis: CUSUMData[];
  moving_averages: MovingAverageData[];
  trend_detection: TrendDetection[];
}

export interface LJChart {
  chart_id: string;
  analyte: string;
  material_level: string;
  data_points: LJDataPoint[];
  control_limits: ControlLimits;
  chart_period: DateRange;
}

export interface LJDataPoint {
  date: Date;
  value: number;
  rule_violations: string[];
  comments?: string;
}

export interface CUSUMData {
  analyte: string;
  cusum_positive: number[];
  cusum_negative: number[];
  decision_limits: DecisionLimits;
  trend_status: TrendStatus;
}

export interface DecisionLimits {
  upper_limit: number;
  lower_limit: number;
  reset_value: number;
}

export interface TrendStatus {
  trend_detected: boolean;
  trend_direction: 'increasing' | 'decreasing' | 'stable';
  confidence: number;
}

export interface MovingAverageData {
  window_size: number;
  moving_averages: number[];
  timestamps: Date[];
  trend_analysis: TrendDetection;
}

export interface TrendDetection {
  trend_type: TrendType;
  start_date: Date;
  end_date?: Date;
  magnitude: number;
  significance: number;
  recommended_actions: string[];
}

export type TrendType = 'shift' | 'drift' | 'cycle' | 'outlier_cluster' | 'variance_change';

export interface OutlierDetection {
  statistical_outliers: OutlierData[];
  trend_violations: TrendViolation[];
  systematic_errors: SystematicError[];
}

export interface OutlierData {
  outlier_id: string;
  date: Date;
  value: number;
  z_score: number;
  outlier_type: OutlierType;
  investigation_status: InvestigationStatus;
}

export type OutlierType = 'statistical' | 'technical' | 'analytical' | 'transcription';
export type InvestigationStatus = 'pending' | 'investigating' | 'resolved' | 'rejected';

export interface TrendViolation {
  violation_id: string;
  violation_type: string;
  start_date: Date;
  end_date?: Date;
  affected_data_points: number;
  severity: ViolationSeverity;
}

export type ViolationSeverity = 'minor' | 'major' | 'critical';

export interface SystematicError {
  error_id: string;
  error_type: string;
  detection_date: Date;
  affected_period: DateRange;
  estimated_bias: number;
  root_cause?: string;
  corrective_actions: CorrectiveAction[];
}

export interface CorrectiveAction {
  action_id: string;
  action_type: string;
  description: string;
  assigned_to: string;
  due_date: Date;
  completion_date?: Date;
  status: ActionStatus;
  effectiveness_verification: EffectivenessVerification;
}

export type ActionStatus = 'planned' | 'in_progress' | 'completed' | 'verified' | 'ineffective';

export interface EffectivenessVerification {
  verification_method: string;
  verification_date?: Date;
  verification_result: VerificationResult;
  follow_up_required: boolean;
}

export type VerificationResult = 'effective' | 'partially_effective' | 'ineffective' | 'pending';

export interface Investigation {
  investigation_id: string;
  trigger_event: string;
  investigation_type: string;
  assigned_investigator: string;
  start_date: Date;
  target_completion: Date;
  status: InvestigationStatus;
  findings: InvestigationFinding[];
}

export interface InvestigationFinding {
  finding_type: string;
  description: string;
  evidence: string[];
  confidence_level: number;
  impact_assessment: ImpactAssessment;
}

export interface ImpactAssessment {
  affected_samples: string[];
  affected_tests: string[];
  patient_impact: PatientImpactLevel;
  regulatory_impact: RegulatoryImpactLevel;
}

export type PatientImpactLevel = 'none' | 'low' | 'medium' | 'high' | 'critical';
export type RegulatoryImpactLevel = 'none' | 'reportable' | 'critical' | 'recall';

export interface StatisticalQCAnalysis {
  control_charts: ControlChart[];
  process_capability: ProcessCapability;
  measurement_uncertainty: MeasurementUncertainty;
  six_sigma_metrics: SixSigmaMetrics;
}

export interface ControlChart {
  chart_type: ControlChartType;
  analyte: string;
  data_series: ControlChartDataPoint[];
  statistical_parameters: ControlChartParameters;
}

export type ControlChartType = 'individuals' | 'moving_range' | 'xbar_r' | 'xbar_s' | 'ewma' | 'cusum';

export interface ControlChartDataPoint {
  timestamp: Date;
  value: number;
  subgroup_size?: number;
  special_causes: SpecialCause[];
}

export interface SpecialCause {
  cause_type: string;
  description: string;
  assignable_cause?: string;
}

export interface ControlChartParameters {
  center_line: number;
  upper_control_limit: number;
  lower_control_limit: number;
  sigma_level: number;
}

export interface ProcessCapability {
  cp: number;
  cpk: number;
  pp: number;
  ppk: number;
  capability_rating: CapabilityRating;
}

export type CapabilityRating = 'inadequate' | 'adequate' | 'good' | 'excellent';

export interface MeasurementUncertainty {
  combined_uncertainty: number;
  expanded_uncertainty: number;
  coverage_factor: number;
  confidence_level: number;
  uncertainty_budget: UncertaintyComponent[];
}

export interface UncertaintyComponent {
  component_name: string;
  uncertainty_value: number;
  distribution_type: string;
  sensitivity_coefficient: number;
  contribution_percent: number;
}

export interface SixSigmaMetrics {
  sigma_level: number;
  defects_per_million: number;
  yield_percent: number;
  process_performance: ProcessPerformanceLevel;
}

export type ProcessPerformanceLevel = 'poor' | 'below_average' | 'average' | 'good' | 'excellent' | 'world_class';

// This file provides comprehensive type support for all stage components
// ensuring type safety and IntelliSense support throughout the application
