# Sample Testing Agent TLA+ Specification - Natural Language Translation

## Overview

This document provides a natural language translation of the formally verified TLA+ specification for the ALIMS Sample Testing Agent. The specification has been validated using the TLC model checker and all safety properties have been verified.

## System Purpose

The Sample Testing Agent manages the execution of laboratory tests on sample specimens. It coordinates with laboratory instruments to execute tests, captures results, handles failures with retry logic, and ensures proper resource utilization while maintaining complete audit trails.

## Core Components

### State Variables

1. **testState**: Maps each test ID to its current state
   - SCHEDULED: Test is ready for execution
   - TESTING: Test is currently being executed on an instrument
   - COMPLETED: Test execution completed successfully
   - FAILED: Test execution failed and needs retry
   - QC_PENDING: Test results are ready for quality control review

2. **testResults**: Maps each test ID to its result value (or NULL if no result yet)
   - Contains actual test results for completed tests
   - NULL for tests that haven't completed

3. **retryCount**: Tracks the number of retry attempts for each test
   - Bounded by MaxRetries constant
   - Used to prevent infinite retry loops

4. **instrumentStatus**: Maps each instrument ID to its current availability
   - AVAILABLE: Instrument is ready for new tests
   - BUSY: Instrument is currently executing tests
   - MAINTENANCE: Instrument is under maintenance

5. **testingQueue**: Priority queue of tests waiting for execution
   - Contains test ID and priority pairs
   - Processed in order to assign tests to available instruments

6. **currentlyTesting**: Maps each instrument to the set of tests it's currently executing
   - Used to track concurrent test execution
   - Bounded by MaxConcurrent per instrument

7. **consumedResources**: Tracks resource consumption for each test
   - Incremented when tests complete
   - Used for resource accounting and billing

8. **auditLog**: Complete audit trail of all system activities
   - Records all actions, test IDs, timestamps, and details
   - Provides complete traceability

### System Constants

- **TestIds**: Set of all test identifiers in the system
- **InstrumentIds**: Set of all laboratory instrument identifiers
- **ResultValues**: Set of possible test result values
- **MaxRetries**: Maximum number of retry attempts for failed tests
- **MaxConcurrent**: Maximum number of concurrent tests per instrument

## System Operations

### 1. Test Scheduling (ScheduleTest)

**Purpose**: Assign a scheduled test to an available instrument for execution

**Preconditions**:
- Test queue is not empty
- Test is in SCHEDULED state
- At least one instrument is available
- Selected instrument has capacity for concurrent tests

**Actions**:
- Move test from SCHEDULED to TESTING state
- Assign test to selected instrument
- Mark instrument as BUSY
- Remove test from queue
- Record action in audit log

**Postconditions**:
- Test is actively being executed
- Instrument capacity is properly tracked
- System state remains consistent

### 2. Test Execution (ExecuteTest)

**Purpose**: Complete test execution and capture results

**Preconditions**:
- Test is in TESTING state
- Test is assigned to a BUSY instrument
- Test result is available

**Actions**:
- Move test from TESTING to COMPLETED state
- Store test result
- Remove test from instrument assignment
- Increment resource consumption
- Mark instrument as AVAILABLE if no other tests
- Record completion in audit log

**Postconditions**:
- Test has valid result
- Resources are properly tracked
- Instrument availability is updated

### 3. Test Failure Handling (TestFailure)

**Purpose**: Handle test execution failures with retry logic

**Preconditions**:
- Test is in TESTING state
- Test is assigned to a BUSY instrument
- Test has not exceeded maximum retry attempts

**Actions**:
- Move test from TESTING to FAILED state
- Increment retry count
- Remove test from instrument assignment
- Mark instrument as AVAILABLE if no other tests
- Record failure in audit log

**Postconditions**:
- Test is marked for retry
- Retry count is updated
- Instrument is freed for other tests

### 4. Test Retry (RetryTest)

**Purpose**: Reschedule failed tests for another execution attempt

**Preconditions**:
- Test is in FAILED state
- Test has not exceeded maximum retry attempts

**Actions**:
- Move test from FAILED to SCHEDULED state
- Add test back to execution queue
- Record retry attempt in audit log

**Postconditions**:
- Test is ready for execution
- Queue contains test for processing

### 5. Test Abandonment (AbandonTest)

**Purpose**: Abandon tests that have exceeded maximum retry attempts

**Preconditions**:
- Test is in FAILED state
- Test has reached maximum retry attempts

**Actions**:
- Keep test in FAILED state permanently
- Record abandonment in audit log

**Postconditions**:
- Test is permanently failed
- No further retry attempts will be made

### 6. QC Transition (TransitionToQc)

**Purpose**: Move completed tests to quality control review

**Preconditions**:
- Test is in COMPLETED state
- Test has a valid result

**Actions**:
- Move test from COMPLETED to QC_PENDING state
- Record transition in audit log

**Postconditions**:
- Test is ready for quality control review
- Results are preserved

### 7. Queue Management (AddToQueue)

**Purpose**: Add scheduled tests to the execution queue

**Preconditions**:
- Test is in SCHEDULED state
- Test is not already in queue

**Actions**:
- Add test to execution queue with priority
- Record queue addition in audit log

**Postconditions**:
- Test is queued for execution
- Queue maintains proper ordering

### 8. Instrument Maintenance (InstrumentMaintenance)

**Purpose**: Take instruments offline for maintenance

**Preconditions**:
- Instrument is AVAILABLE
- Instrument is not executing any tests

**Actions**:
- Move instrument from AVAILABLE to MAINTENANCE state
- Record maintenance start in audit log

**Postconditions**:
- Instrument is unavailable for new tests
- Maintenance is properly tracked

### 9. Instrument Restoration (RestoreInstrument)

**Purpose**: Restore instruments from maintenance to service

**Preconditions**:
- Instrument is in MAINTENANCE state

**Actions**:
- Move instrument from MAINTENANCE to AVAILABLE state
- Record restoration in audit log

**Postconditions**:
- Instrument is available for new tests
- Service restoration is tracked

## Safety Properties

### 1. Execution Safety
**Guarantee**: No test is ever executed on an unavailable instrument
**Verification**: All tests in TESTING state are only assigned to BUSY instruments

### 2. Result Integrity
**Guarantee**: Test results are only set for tests that have completed execution
**Verification**: Only COMPLETED and QC_PENDING tests have non-NULL results

### 3. Instrument Safety
**Guarantee**: No instrument is overloaded with concurrent tests
**Verification**: All instruments respect the MaxConcurrent limit

### 4. No Data Loss
**Guarantee**: No test is lost during execution
**Verification**: All tests remain in valid states throughout the workflow

### 5. Retry Bounds
**Guarantee**: Retry attempts are bounded to prevent infinite loops
**Verification**: No test exceeds MaxRetries attempts

### 6. Resource Consistency
**Guarantee**: Resources are properly tracked for completed tests
**Verification**: All completed tests have positive resource consumption

### 7. Audit Trail Integrity
**Guarantee**: Audit log maintains temporal ordering
**Verification**: All timestamps are monotonically increasing

## Liveness Properties

### 1. Eventual Execution
**Guarantee**: All scheduled tests eventually get executed
**Mechanism**: Weak fairness on test scheduling and execution

### 2. Failure Recovery
**Guarantee**: Failed tests are eventually retried or abandoned
**Mechanism**: Retry logic with bounded attempts

### 3. Result Delivery
**Guarantee**: Completed tests eventually transition to QC
**Mechanism**: Automatic QC transition for completed tests

### 4. Instrument Availability
**Guarantee**: Busy instruments eventually become available
**Mechanism**: Test completion frees instruments

### 5. Queue Processing
**Guarantee**: Test queue eventually becomes empty
**Mechanism**: Continuous processing of queued tests

## Fairness Constraints

### Weak Fairness
- Test scheduling actions are eventually taken when enabled
- Test execution actions are eventually taken when enabled
- QC transitions are eventually taken when enabled
- Retry actions are eventually taken when enabled

### Strong Fairness
- Test abandonment actions are eventually taken when repeatedly enabled
- Instrument restoration actions are eventually taken when repeatedly enabled

## Implementation Guarantees

Based on the formal verification, the implementation will guarantee:

1. **Correctness**: All safety properties are maintained
2. **Progress**: All liveness properties ensure forward progress
3. **Consistency**: Type invariants prevent invalid states
4. **Reliability**: Bounded retry logic prevents infinite loops
5. **Traceability**: Complete audit trail for all operations
6. **Resource Management**: Proper tracking of instrument usage and consumables
7. **Fault Tolerance**: Graceful handling of test failures and instrument maintenance

## Conclusion

This TLA+ specification provides a mathematically precise and formally verified foundation for implementing the Sample Testing Agent. All safety and liveness properties have been validated through exhaustive model checking, ensuring the implementation will behave correctly under all possible execution scenarios.

The natural language translation preserves the formal semantics while making the specification accessible to implementers and stakeholders who need to understand the system behavior and guarantees.

---

**Specification Status**: ✅ VALIDATED  
**Model Checker**: TLC  
**Properties Verified**: All safety and liveness properties  
**Ready for Implementation**: YES
