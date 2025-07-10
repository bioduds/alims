# LIMS Sample Workflow State Machine Implementation Plan

## Feature Overview

**Feature ID**: 20250709-lims-sample-workflow
**Priority**: CRITICAL
**Complexity**: HIGH
**Impact**: CRITICAL

## Problem Statement

The ALIMS system has an excellent LIMS sample workflow implementation, but it lacks formal verification guarantees for:
- State transition correctness under all conditions
- Audit trail immutability and regulatory compliance
- Quality control requirement enforcement
- Resource constraint management
- Concurrent sample processing safety

This prevents providing mathematical guarantees for mission-critical laboratory operations and regulatory compliance (21 CFR Part 11).

## Solution Design

Implement a TLA+ verified LIMS Sample Workflow State Machine that ensures:

1. **Monotonic Progression** - Samples cannot regress to previous states
2. **Audit Trail Immutability** - All state changes are permanently recorded
3. **QC Required** - No sample can be reported without QC approval
4. **State Consistency** - All samples have well-defined states at all times
5. **Resource Bounds** - Testing capacity and equipment constraints are respected
6. **Regulatory Compliance** - 21 CFR Part 11 audit trail requirements

## TLA+ Specification Requirements

### State Variables
- `samples`: Set of all samples in the system
- `sampleStates`: Function mapping Sample ID to current state
- `auditTrail`: Function mapping Sample ID to sequence of state transitions
- `nextSampleID`: Next available sample identifier
- `qcApprovals`: Set of samples that have been QC approved
- `resourceAllocations`: Current testing resource usage

### Sample States
- `RECEIVED`: Sample has been received into the LIMS
- `ACCESSIONED`: Sample has been registered and assigned an ID
- `SCHEDULED`: Testing has been scheduled for the sample
- `TESTING`: Sample is currently being tested
- `QC_PENDING`: Testing complete, awaiting QC review
- `QC_APPROVED`: QC has approved the test results
- `REPORTED`: Results have been reported to client
- `ARCHIVED`: Sample and results have been archived (terminal state)

### Valid State Transitions
```
RECEIVED → ACCESSIONED → SCHEDULED → TESTING → QC_PENDING → QC_APPROVED → REPORTED → ARCHIVED
```

### Safety Properties
1. **MonotonicProgression**: ∀ sample ∈ Samples: Once a sample transitions from state A to state B, it cannot return to state A
2. **AuditTrailImmutability**: ∀ sample ∈ Samples: Audit trail entries can only be appended, never modified or deleted
3. **QCRequired**: ∀ sample ∈ Samples: sample.state ∈ {REPORTED, ARCHIVED} ⇒ QC_APPROVED ∈ sample.auditTrail
4. **StateConsistency**: ∀ sample ∈ Samples: sample.state ∈ SampleStates
5. **ResourceBounds**: Cardinality(samplesInState(TESTING)) ≤ MaxConcurrentTests
6. **ValidTransitions**: All state transitions follow the defined workflow progression

### Liveness Properties
1. **EventualProgression**: Samples eventually progress through the workflow
2. **QCCompletion**: Samples in QC_PENDING eventually get reviewed
3. **ResourceAvailability**: Testing resources eventually become available

## Acceptance Criteria

### TLA+ Validation
- [ ] TLA+ specification created and syntactically correct
- [ ] TLC model checker validates all safety properties
- [ ] No invariant violations found in state space exploration
- [ ] Liveness properties verified (with appropriate fairness constraints)
- [ ] Human approval of TLA+ specification obtained

### Implementation Requirements
- [ ] All existing LIMS workflow tests continue to pass
- [ ] TLA+ properties enforced at runtime
- [ ] Audit trail immutability verified
- [ ] QC requirement enforcement implemented
- [ ] Resource constraint validation added
- [ ] Performance benchmarks met (no regression)

### Regulatory Compliance
- [ ] 21 CFR Part 11 audit trail requirements satisfied
- [ ] Electronic signature integration points identified
- [ ] Data integrity validation implemented
- [ ] Tamper-evident logging enabled

## Testing Strategy

### Unit Tests
- Test each state transition individually
- Verify invalid transitions are rejected
- Validate audit trail immutability
- Test resource constraint enforcement

### Integration Tests
- Multi-sample workflow processing
- Concurrent sample processing safety
- QC approval workflow integration
- Resource allocation and deallocation

### Property-Based Tests
- Generate random sample workflows and verify TLA+ properties
- Stress test concurrent operations
- Validate audit trail integrity under load

### Regulatory Tests
- 21 CFR Part 11 compliance validation
- Electronic signature workflow testing
- Data integrity verification

## Implementation Phases

### Phase 1: TLA+ Specification (3-4 days)
1. Create formal TLA+ specification based on existing implementation
2. Model all 8 sample states and valid transitions
3. Define safety and liveness properties
4. Validate with TLC model checker

### Phase 2: Runtime Integration (2-3 days)
1. Enhance existing SampleWorkflow class with TLA+ property enforcement
2. Add runtime validation for all TLA+ properties
3. Implement resource constraint checking
4. Add comprehensive logging and monitoring

### Phase 3: Testing & Validation (2 days)
1. Create comprehensive test suite
2. Validate all TLA+ properties in implementation
3. Performance testing and optimization
4. Regulatory compliance verification

## Risk Mitigation

### Technical Risks
- **TLA+ model complexity**: Start with core properties, add complexity incrementally
- **Performance impact**: Implement efficient property checking with caching
- **Integration issues**: Maintain backward compatibility with existing APIs

### Regulatory Risks
- **Compliance gaps**: Involve regulatory expert in specification review
- **Audit trail integrity**: Use cryptographic signatures for tamper evidence
- **Data retention**: Implement automated archival with integrity verification

## Success Metrics

- **Correctness**: Zero TLA+ property violations in production
- **Performance**: No more than 5% overhead for property checking
- **Compliance**: 100% audit trail integrity under all conditions
- **Reliability**: Zero workflow corruption incidents

## Dependencies

- Service Health Monitoring (completed and validated)
- Existing LIMS models and workflow implementation
- TLA+ tools and model checker (already available)
- Regulatory compliance framework (to be defined)

## Deliverables

1. **TLA+ Specification**: `LIMSSampleWorkflow.tla` with full formal model
2. **Enhanced Implementation**: Updated Python code with TLA+ property enforcement
3. **Test Suite**: Comprehensive tests validating all properties
4. **Documentation**: Implementation guide and regulatory compliance report
5. **Validation Report**: TLC model checking results and human approval
