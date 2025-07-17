# LIMS Sample QC Review Agent Implementation Plan

## Feature Overview

**Feature ID**: 20250711-sample-qc-review  
**Priority**: HIGH  
**Complexity**: HIGH  
**Impact**: CRITICAL  

## Problem Statement

The ALIMS system needs a **QC Review Agent** to manage the transition of samples from `QC_PENDING` to `QC_APPROVED` or `QC_REJECTED` state. This agent must:

1. **Validate test results** against reference ranges and QC rules
2. **Perform statistical analysis** for outlier detection and trend analysis
3. **Apply Westgard rules** for quality control validation
4. **Handle critical values** with immediate flagging and notification
5. **Manage review workflows** including multi-level approval processes
6. **Integrate with PostgreSQL database** for QC rules and reference ranges
7. **Provide formal verification** of QC workflow correctness

## LIMS Workflow Context

```
RECEIVED → ACCESSIONED → SCHEDULED → TESTING → QC_PENDING → QC_APPROVED → REPORTED → ARCHIVED
                                                      ↑            ↓
                                                      └── QC_REJECTED
```

### Current State
- **Input**: Samples in `QC_PENDING` state (from Sample Testing Agent)
- **Output**: Samples in `QC_APPROVED` or `QC_REJECTED` state
- **Next Agent**: Sample Reporting Agent (for QC_APPROVED samples)

## TLA+ Specification Requirements

### State Variables
- `qcQueue`: Queue of samples awaiting QC review
- `qcResults`: Function mapping Sample ID to QC decision
- `qcRules`: Set of active quality control rules
- `referenceRanges`: Function mapping test type to acceptable ranges
- `criticalValues`: Set of test results requiring immediate attention
- `reviewerAssignments`: Function mapping samples to assigned reviewers
- `auditTrail`: Complete record of all QC decisions and actions

### QC States
- `QC_PENDING`: Sample results ready for quality control review
- `QC_IN_REVIEW`: Sample currently being reviewed by QC personnel
- `QC_APPROVED`: Sample passed quality control and ready for reporting
- `QC_REJECTED`: Sample failed quality control and requires corrective action
- `QC_ESCALATED`: Sample requires senior review or additional investigation

### Safety Properties
1. **QC Required**: No sample can transition to REPORTED without QC approval
2. **Audit Trail**: All QC decisions must be logged with timestamp and reviewer
3. **Critical Values**: Critical test results must be flagged immediately
4. **Reference Range Validation**: All results must be checked against valid ranges
5. **Reviewer Assignment**: Each sample must have an assigned qualified reviewer
6. **Decision Consistency**: QC decisions must be consistent with applied rules

### Liveness Properties
1. **Eventual Review**: All samples in QC_PENDING eventually get reviewed
2. **Critical Priority**: Critical samples get priority review within time limits
3. **Escalation Handling**: Failed QC samples trigger appropriate escalation
4. **Resource Availability**: QC reviewers eventually become available

## Implementation Architecture

### Core Components

1. **QCReviewAgent** - Main orchestration class
2. **StatisticalAnalyzer** - Performs statistical analysis and outlier detection
3. **ReferenceRangeValidator** - Validates results against reference ranges
4. **WestgardRuleEngine** - Applies Westgard quality control rules
5. **CriticalValueHandler** - Manages critical value flagging and notifications
6. **ReviewWorkflowManager** - Manages multi-level approval workflows

### PostgreSQL Integration

The agent will extend the existing database schema with:
- `lims.qc_rules` - Quality control rules and parameters
- `lims.reference_ranges` - Test-specific reference ranges
- `lims.qc_reviews` - QC review records and decisions
- `lims.critical_values` - Critical value definitions and thresholds
- `lims.qc_assignments` - Reviewer assignments and workload tracking

### Quality Control Rules

The agent will implement:
- **Westgard Rules**: 1-2s, 1-3s, 2-2s, R-4s, 4-1s, 10-x rules
- **Delta Checks**: Comparison with previous results for the same patient
- **Reference Range Validation**: Age/gender-specific normal ranges
- **Critical Value Detection**: Immediate flagging of life-threatening results
- **Trend Analysis**: Statistical process control for ongoing quality

## Acceptance Criteria

### TLA+ Validation
- [ ] TLA+ specification created and syntactically correct
- [ ] TLC model checker validates all safety properties
- [ ] No invariant violations found in state space exploration
- [ ] Liveness properties verified with appropriate fairness constraints
- [ ] Human approval of TLA+ specification obtained

### Implementation Requirements
- [ ] All existing LIMS workflow tests continue to pass
- [ ] TLA+ properties enforced at runtime
- [ ] Statistical analysis algorithms implemented and tested
- [ ] Westgard rules properly implemented
- [ ] Critical value detection working correctly
- [ ] Reference range validation functional
- [ ] Multi-level approval workflow implemented

### Integration Requirements
- [ ] Seamless integration with existing Sample Testing Agent
- [ ] PostgreSQL database schema extended correctly
- [ ] QC rules and reference ranges configurable
- [ ] Complete audit trail maintained
- [ ] Performance benchmarks met (<500ms per QC review)

### Quality Assurance
- [ ] Comprehensive unit test coverage (>90%)
- [ ] Integration tests with real database scenarios
- [ ] Performance tests under load
- [ ] Error handling and recovery tested
- [ ] Security and access control validated

## Quality Control Domain Knowledge

### Westgard Rules Implementation
1. **1-2s Rule**: One control outside ±2s limits
2. **1-3s Rule**: One control outside ±3s limits (reject)
3. **2-2s Rule**: Two consecutive controls outside ±2s limits
4. **R-4s Rule**: Range of two controls exceeds 4s
5. **4-1s Rule**: Four consecutive controls outside ±1s limits
6. **10-x Rule**: Ten consecutive controls on one side of mean

### Statistical Analysis Requirements
- **Mean and Standard Deviation**: Calculate for control samples
- **Coefficient of Variation**: Measure precision of testing
- **Outlier Detection**: Identify results requiring investigation
- **Trend Analysis**: Detect systematic shifts in performance
- **Control Chart Generation**: Visual representation of QC data

### Critical Value Management
- **Immediate Notification**: Alert system for critical results
- **Escalation Protocols**: Chain of command for critical findings
- **Documentation Requirements**: Complete record of critical value handling
- **Turnaround Time Tracking**: Monitor time to notification

## Risk Assessment

### High Risk Areas
1. **Statistical Complexity**: Advanced statistical calculations
2. **Domain Knowledge**: Deep understanding of laboratory QC practices
3. **Database Performance**: Complex queries for statistical analysis
4. **Integration Complexity**: Multiple systems and workflows

### Mitigation Strategies
1. **Incremental Implementation**: Start with basic rules, add complexity
2. **Domain Expert Consultation**: Validate QC rules with laboratory professionals
3. **Performance Testing**: Benchmark database queries and optimize
4. **Comprehensive Testing**: Cover all integration points thoroughly

## Success Metrics

### Functional Metrics
- **QC Review Accuracy**: >99% correct QC decisions
- **Critical Value Detection**: 100% detection rate
- **Processing Speed**: <500ms per QC review
- **Audit Compliance**: 100% audit trail completeness

### Quality Metrics
- **Test Coverage**: >90% code coverage
- **TLA+ Compliance**: All invariants maintained
- **Integration Success**: All workflow tests passing
- **Performance**: Meets or exceeds benchmarks

## Implementation Timeline

### Phase 1: TLA+ Specification (Day 1)
- [ ] Create TLA+ specification for QC Review Agent
- [ ] Define state variables and transitions
- [ ] Specify safety and liveness properties
- [ ] Validate with TLC model checker
- [ ] Obtain human approval

### Phase 2: Database Schema (Day 1-2)
- [ ] Design QC-specific database tables
- [ ] Create reference range management system
- [ ] Implement QC rules configuration
- [ ] Set up audit trail infrastructure

### Phase 3: Agent Implementation (Day 2-3)
- [ ] Implement core QC Review Agent class
- [ ] Add statistical analysis components
- [ ] Implement Westgard rules engine
- [ ] Add critical value handling
- [ ] Create review workflow management

### Phase 4: Testing and Validation (Day 3)
- [ ] TLA+ compliance test suite
- [ ] Comprehensive unit tests
- [ ] Integration tests with database
- [ ] Performance benchmarking
- [ ] End-to-end workflow testing

---

This implementation plan provides a comprehensive roadmap for creating a production-ready, TLA+-verified Sample QC Review Agent that meets all laboratory quality control requirements while maintaining the highest standards of software engineering and formal verification.
