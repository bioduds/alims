# LIMS Sample Testing Agent Implementation Plan

## Feature Overview

**Feature ID**: 20250711-sample-testing
**Priority**: HIGH
**Complexity**: HIGH
**Impact**: CRITICAL

## Problem Statement

The ALIMS system needs a **Testing Agent** to manage the transition of samples from `SCHEDULED` to `TESTING` to `QC_PENDING` state. This agent must:

1. **Coordinate with laboratory instruments** for test execution
2. **Manage test result capture** and validation
3. **Handle testing failures** and automatic retries
4. **Ensure instrument availability** and proper resource utilization
5. **Integrate with the existing PostgreSQL database** for real-time tracking
6. **Provide formal verification** of testing workflow correctness

## Solution Design

Implement a **TLA+ verified Testing Agent** that ensures:

1. **Test Execution Safety** - No tests are lost or corrupted during execution
2. **Instrument Coordination** - Proper coordination between multiple laboratory instruments
3. **Resource Management** - Efficient use of testing resources and reagents
4. **Failure Handling** - Automatic retry logic for failed tests
5. **Result Integrity** - Validation of test results before QC submission
6. **Audit Trail** - Complete traceability of all testing activities

## TLA+ Specification Requirements

### State Variables
- `scheduledTests`: Set of tests scheduled for execution
- `testingInProgress`: Set of tests currently being executed
- `testResults`: Function mapping test IDs to results
- `instrumentStatus`: Function mapping instrument IDs to availability
- `testingQueue`: Priority queue of scheduled tests
- `failedTests`: Set of tests that failed and need retry

### Testing States
- `SCHEDULED`: Test is scheduled and waiting for execution
- `TESTING`: Test is currently being executed on instrument
- `COMPLETED`: Test execution completed successfully
- `FAILED`: Test execution failed and needs retry
- `QC_PENDING`: Test results ready for quality control review

### Safety Properties
1. **ExecutionSafety**: No test is executed on an unavailable instrument
2. **ResultIntegrity**: All test results are properly validated and stored
3. **NoDataLoss**: No test results are lost during execution or failure
4. **InstrumentSafety**: No instrument is overloaded with concurrent tests
5. **ResourceConsistency**: Consumables are properly tracked and updated

### Liveness Properties
1. **EventualExecution**: All scheduled tests eventually get executed
2. **FailureRecovery**: Failed tests eventually get retried
3. **ResultDelivery**: Completed tests eventually transition to QC_PENDING

## Implementation Architecture

### Core Components

1. **TestingAgent** - Main orchestration class
2. **InstrumentManager** - Manages instrument communication
3. **ResultProcessor** - Handles test result validation and storage
4. **FailureHandler** - Manages test failures and retry logic
5. **QueueManager** - Manages priority-based test execution queue

### PostgreSQL Integration

The agent will integrate with the existing database schema:
- `lims.sample_scheduling` - Source of scheduled tests
- `lims.test_execution` - Track test execution progress
- `lims.test_results` - Store test results
- `lims.equipment` - Manage instrument availability
- `lims.inventory_items` - Track consumable usage

### Instrument Communication

The agent will support:
- **Mock Instruments** - For testing and development
- **File-based Results** - Read results from instrument output files
- **Future Extensions** - API-based instrument communication

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
- [ ] Instrument coordination implemented
- [ ] Test result validation and storage
- [ ] Failure handling and retry logic
- [ ] Performance benchmarks met

### Integration Requirements
- [ ] Seamless integration with existing scheduling agent
- [ ] PostgreSQL database updates work correctly
- [ ] Instrument mock/simulation system functional
- [ ] Complete audit trail maintained

## Testing Strategy

### Unit Tests
- Test individual components in isolation
- Mock external dependencies (instruments, database)
- Validate TLA+ properties at component level

### Integration Tests
- End-to-end workflow testing
- Database integration validation
- Instrument communication testing

### Property-Based Tests
- Generate random test scenarios
- Verify TLA+ properties hold under all conditions
- Stress test concurrent operations

## Implementation Phases

### Phase 1: TLA+ Specification (Days 1-2)
1. **Day 1**: Create formal TLA+ specification
2. **Day 2**: Validate with TLC model checker and get human approval

### Phase 2: Core Implementation (Days 3-5)
1. **Day 3**: Implement TestingAgent and InstrumentManager
2. **Day 4**: Implement ResultProcessor and FailureHandler
3. **Day 5**: Implement QueueManager and database integration

### Phase 3: Testing & Validation (Days 6-7)
1. **Day 6**: Comprehensive testing and TLA+ property validation
2. **Day 7**: Integration testing and performance optimization

## Success Metrics

- **Safety**: Zero test data loss or corruption
- **Reliability**: 99.9% test execution success rate
- **Performance**: Process 100+ tests per hour per instrument
- **Accuracy**: All TLA+ properties verified in production

## Dependencies

- Sample Scheduling Agent (completed)
- PostgreSQL lab inventory schema (available)
- TLA+ tools and model checker (available)
- Mock instrument simulation system (to be created)

## Risk Mitigation

### Technical Risks
- **Instrument integration complexity**: Start with mock instruments
- **Database performance**: Implement efficient querying and indexing
- **TLA+ model complexity**: Iterate incrementally

### Operational Risks
- **Test execution failures**: Implement robust retry logic
- **Resource conflicts**: Ensure proper resource locking
- **Data integrity**: Implement comprehensive validation

## Deliverables

1. **TLA+ Specification**: `SampleTestingAgent.tla` with full formal model
2. **Implementation**: `sample_testing.py` with TLA+ property enforcement
3. **Test Suite**: Comprehensive tests validating all properties
4. **Integration Test**: End-to-end workflow validation
5. **Documentation**: Complete API documentation and usage guide
6. **Mock Instruments**: Simulation system for testing
