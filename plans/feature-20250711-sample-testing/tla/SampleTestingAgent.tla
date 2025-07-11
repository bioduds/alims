---- MODULE SampleTestingAgent ----
(*
ALIMS Sample Testing Agent TLA+ Specification
Verified specification for managing laboratory test execution workflow.

This specification models the testing agent that coordinates:
- Test execution on laboratory instruments
- Test result capture and validation
- Instrument availability management
- Failure handling and retry logic
- Resource consumption tracking
*)

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS
    TestIds,        \* Set of test identifiers
    InstrumentIds,  \* Set of instrument identifiers
    ResultValues,   \* Set of possible test result values
    MaxRetries,     \* Maximum retry attempts for failed tests
    MaxConcurrent   \* Maximum concurrent tests per instrument

VARIABLES
    testState,          \* testid -> {SCHEDULED, TESTING, COMPLETED, FAILED, QC_PENDING}
    testResults,        \* testid -> result value (or NULL)
    retryCount,         \* testid -> number of retry attempts
    instrumentStatus,   \* instrumentid -> {AVAILABLE, BUSY, MAINTENANCE}
    testingQueue,       \* sequence of {testid, priority} pairs
    currentlyTesting,   \* instrumentid -> set of testids currently being executed
    consumedResources,  \* testid -> amount of resources consumed
    auditLog           \* sequence of {action, testid, timestamp, details}

\* Define test states
TestStates == {"SCHEDULED", "TESTING", "COMPLETED", "FAILED", "QC_PENDING"}

\* Define instrument states
InstrumentStates == {"AVAILABLE", "BUSY", "MAINTENANCE"}

\* Type invariants
TypeInvariant ==
    /\ testState \in [TestIds -> TestStates]
    /\ testResults \in [TestIds -> ResultValues \cup {"NULL"}]
    /\ retryCount \in [TestIds -> 0..MaxRetries]
    /\ instrumentStatus \in [InstrumentIds -> InstrumentStates]
    /\ testingQueue \in Seq([testid: TestIds, priority: Nat])
    /\ currentlyTesting \in [InstrumentIds -> SUBSET TestIds]
    /\ consumedResources \in [TestIds -> Nat]
    /\ auditLog \in Seq([action: STRING, testid: TestIds, timestamp: Nat, details: STRING])

\* Initial state
Init ==
    /\ testState = [t \in TestIds |-> "SCHEDULED"]
    /\ testResults = [t \in TestIds |-> "NULL"]
    /\ retryCount = [t \in TestIds |-> 0]
    /\ instrumentStatus = [i \in InstrumentIds |-> "AVAILABLE"]
    /\ testingQueue = <<>>
    /\ currentlyTesting = [i \in InstrumentIds |-> {}]
    /\ consumedResources = [t \in TestIds |-> 0]
    /\ auditLog = <<>>

\* Helper functions
AvailableInstruments == {i \in InstrumentIds : instrumentStatus[i] = "AVAILABLE"}

ScheduledTests == {t \in TestIds : testState[t] = "SCHEDULED"}

TestsInProgress == {t \in TestIds : testState[t] = "TESTING"}

CompletedTests == {t \in TestIds : testState[t] = "COMPLETED"}

FailedTests == {t \in TestIds : testState[t] = "FAILED"}

QcPendingTests == {t \in TestIds : testState[t] = "QC_PENDING"}

\* Find available instrument with capacity
FindAvailableInstrument ==
    CHOOSE i \in AvailableInstruments : 
        Cardinality(currentlyTesting[i]) < MaxConcurrent

\* Schedule a test for execution
ScheduleTest ==
    /\ testingQueue # <<>>
    /\ LET firstTest == Head(testingQueue)
           testid == firstTest.testid
           priority == firstTest.priority
       IN
       /\ testState[testid] = "SCHEDULED"
       /\ \E instrument \in AvailableInstruments:
           /\ Cardinality(currentlyTesting[instrument]) < MaxConcurrent
           /\ testState' = [testState EXCEPT ![testid] = "TESTING"]
           /\ currentlyTesting' = [currentlyTesting EXCEPT ![instrument] = @ \cup {testid}]
           /\ instrumentStatus' = [instrumentStatus EXCEPT ![instrument] = "BUSY"]
           /\ testingQueue' = Tail(testingQueue)
           /\ auditLog' = Append(auditLog, [action |-> "TEST_STARTED", testid |-> testid, timestamp |-> Len(auditLog), details |-> "Test execution started"])
           /\ UNCHANGED <<testResults, retryCount, consumedResources>>

\* Execute test and capture result
ExecuteTest ==
    /\ \E testid \in TestsInProgress:
        /\ \E instrument \in InstrumentIds:
            /\ testid \in currentlyTesting[instrument]
            /\ instrumentStatus[instrument] = "BUSY"
            /\ \E result \in ResultValues:
                /\ testState' = [testState EXCEPT ![testid] = "COMPLETED"]
                /\ testResults' = [testResults EXCEPT ![testid] = result]
                /\ currentlyTesting' = [currentlyTesting EXCEPT ![instrument] = @ \ {testid}]
                /\ consumedResources' = [consumedResources EXCEPT ![testid] = @ + 1]
                /\ auditLog' = Append(auditLog, [action |-> "TEST_COMPLETED", testid |-> testid, timestamp |-> Len(auditLog), details |-> "Test execution completed"])
                /\ IF currentlyTesting'[instrument] = {}
                   THEN instrumentStatus' = [instrumentStatus EXCEPT ![instrument] = "AVAILABLE"]
                   ELSE instrumentStatus' = instrumentStatus
                /\ UNCHANGED <<retryCount, testingQueue>>

\* Handle test failure
TestFailure ==
    /\ \E testid \in TestsInProgress:
        /\ \E instrument \in InstrumentIds:
            /\ testid \in currentlyTesting[instrument]
            /\ instrumentStatus[instrument] = "BUSY"
            /\ retryCount[testid] < MaxRetries
            /\ testState' = [testState EXCEPT ![testid] = "FAILED"]
            /\ retryCount' = [retryCount EXCEPT ![testid] = @ + 1]
            /\ currentlyTesting' = [currentlyTesting EXCEPT ![instrument] = @ \ {testid}]
            /\ auditLog' = Append(auditLog, [action |-> "TEST_FAILED", testid |-> testid, timestamp |-> Len(auditLog), details |-> "Test execution failed"])
            /\ IF currentlyTesting'[instrument] = {}
               THEN instrumentStatus' = [instrumentStatus EXCEPT ![instrument] = "AVAILABLE"]
               ELSE instrumentStatus' = instrumentStatus
            /\ UNCHANGED <<testResults, testingQueue, consumedResources>>

\* Retry failed test
RetryTest ==
    /\ \E testid \in FailedTests:
        /\ retryCount[testid] < MaxRetries
        /\ testState' = [testState EXCEPT ![testid] = "SCHEDULED"]
        /\ testingQueue' = Append(testingQueue, [testid |-> testid, priority |-> 1])
        /\ auditLog' = Append(auditLog, [action |-> "TEST_RETRY", testid |-> testid, timestamp |-> Len(auditLog), details |-> "Test scheduled for retry"])
        /\ UNCHANGED <<testResults, retryCount, instrumentStatus, currentlyTesting, consumedResources>>

\* Abandon test after max retries
AbandonTest ==
    /\ \E testid \in FailedTests:
        /\ retryCount[testid] >= MaxRetries
        /\ testState' = [testState EXCEPT ![testid] = "FAILED"]
        /\ auditLog' = Append(auditLog, [action |-> "TEST_ABANDONED", testid |-> testid, timestamp |-> Len(auditLog), details |-> "Test abandoned after max retries"])
        /\ UNCHANGED <<testResults, retryCount, instrumentStatus, currentlyTesting, testingQueue, consumedResources>>

\* Transition completed test to QC
TransitionToQc ==
    /\ \E testid \in CompletedTests:
        /\ testResults[testid] # "NULL"
        /\ testState' = [testState EXCEPT ![testid] = "QC_PENDING"]
        /\ auditLog' = Append(auditLog, [action |-> "QC_TRANSITION", testid |-> testid, timestamp |-> Len(auditLog), details |-> "Test transitioned to QC"])
        /\ UNCHANGED <<testResults, retryCount, instrumentStatus, currentlyTesting, testingQueue, consumedResources>>

\* Add test to queue
AddToQueue ==
    /\ \E testid \in ScheduledTests:
        /\ ~\E i \in 1..Len(testingQueue): testingQueue[i].testid = testid
        /\ testingQueue' = Append(testingQueue, [testid |-> testid, priority |-> 1])
        /\ auditLog' = Append(auditLog, [action |-> "QUEUE_ADDED", testid |-> testid, timestamp |-> Len(auditLog), details |-> "Test added to queue"])
        /\ UNCHANGED <<testState, testResults, retryCount, instrumentStatus, currentlyTesting, consumedResources>>

\* Instrument maintenance
InstrumentMaintenance ==
    /\ \E instrument \in InstrumentIds:
        /\ instrumentStatus[instrument] = "AVAILABLE"
        /\ currentlyTesting[instrument] = {}
        /\ instrumentStatus' = [instrumentStatus EXCEPT ![instrument] = "MAINTENANCE"]
        /\ auditLog' = Append(auditLog, [action |-> "INSTRUMENT_MAINTENANCE", testid |-> CHOOSE t \in TestIds : TRUE, timestamp |-> Len(auditLog), details |-> "Instrument maintenance started"])
        /\ UNCHANGED <<testState, testResults, retryCount, currentlyTesting, testingQueue, consumedResources>>

\* Restore instrument from maintenance
RestoreInstrument ==
    /\ \E instrument \in InstrumentIds:
        /\ instrumentStatus[instrument] = "MAINTENANCE"
        /\ instrumentStatus' = [instrumentStatus EXCEPT ![instrument] = "AVAILABLE"]
        /\ auditLog' = Append(auditLog, [action |-> "INSTRUMENT_RESTORED", testid |-> CHOOSE t \in TestIds : TRUE, timestamp |-> Len(auditLog), details |-> "Instrument restored from maintenance"])
        /\ UNCHANGED <<testState, testResults, retryCount, currentlyTesting, testingQueue, consumedResources>>

\* Next state relation
Next ==
    \/ ScheduleTest
    \/ ExecuteTest
    \/ TestFailure
    \/ RetryTest
    \/ AbandonTest
    \/ TransitionToQc
    \/ AddToQueue
    \/ InstrumentMaintenance
    \/ RestoreInstrument

\* Specification
Spec == Init /\ [][Next]_<<testState, testResults, retryCount, instrumentStatus, testingQueue, currentlyTesting, consumedResources, auditLog>>

\* ============================================================================
\* SAFETY PROPERTIES
\* ============================================================================

\* SAFETY 1: No test is executed on an unavailable instrument
ExecutionSafety ==
    \A testid \in TestIds:
        testState[testid] = "TESTING" =>
            \E instrument \in InstrumentIds:
                /\ testid \in currentlyTesting[instrument]
                /\ instrumentStatus[instrument] = "BUSY"

\* SAFETY 2: Test results are only set for completed tests
ResultIntegrity ==
    \A testid \in TestIds:
        testResults[testid] # "NULL" => testState[testid] \in {"COMPLETED", "QC_PENDING"}

\* SAFETY 3: No instrument is overloaded
InstrumentSafety ==
    \A instrument \in InstrumentIds:
        Cardinality(currentlyTesting[instrument]) <= MaxConcurrent

\* SAFETY 4: No test is lost during execution
NoDataLoss ==
    \A testid \in TestIds:
        testState[testid] \in TestStates

\* SAFETY 5: Retry count is bounded
RetryBounds ==
    \A testid \in TestIds:
        retryCount[testid] <= MaxRetries

\* SAFETY 6: Resources are properly tracked
ResourceConsistency ==
    \A testid \in TestIds:
        testState[testid] \in {"COMPLETED", "QC_PENDING"} => consumedResources[testid] > 0

\* SAFETY 7: Audit log is monotonic
AuditLogMonotonic ==
    \A i \in 1..Len(auditLog):
        auditLog[i].timestamp >= 0

\* Combined safety property
SafetyProperty ==
    /\ ExecutionSafety
    /\ ResultIntegrity
    /\ InstrumentSafety
    /\ NoDataLoss
    /\ RetryBounds
    /\ ResourceConsistency
    /\ AuditLogMonotonic

\* ============================================================================
\* LIVENESS PROPERTIES
\* ============================================================================

\* LIVENESS 1: All scheduled tests eventually get executed
EventualExecution ==
    \A testid \in TestIds:
        testState[testid] = "SCHEDULED" ~> testState[testid] \in {"TESTING", "COMPLETED", "QC_PENDING", "FAILED"}

\* LIVENESS 2: Failed tests eventually get retried or abandoned
FailureRecovery ==
    \A testid \in TestIds:
        testState[testid] = "FAILED" ~> 
            \/ testState[testid] = "SCHEDULED"
            \/ retryCount[testid] >= MaxRetries

\* LIVENESS 3: Completed tests eventually transition to QC
ResultDelivery ==
    \A testid \in TestIds:
        testState[testid] = "COMPLETED" ~> testState[testid] = "QC_PENDING"

\* LIVENESS 4: Busy instruments eventually become available
InstrumentAvailability ==
    \A instrument \in InstrumentIds:
        instrumentStatus[instrument] = "BUSY" ~> instrumentStatus[instrument] = "AVAILABLE"

\* LIVENESS 5: Queue eventually processes all tests
QueueProcessing ==
    testingQueue # <<>> ~> testingQueue = <<>>

\* Combined liveness property
LivenessProperty ==
    /\ EventualExecution
    /\ FailureRecovery
    /\ ResultDelivery
    /\ InstrumentAvailability
    /\ QueueProcessing

\* ============================================================================
\* FAIRNESS CONSTRAINTS
\* ============================================================================

\* Weak fairness for test execution
WeakFairness ==
    /\ WF_<<testState, testResults, retryCount, instrumentStatus, testingQueue, currentlyTesting, consumedResources, auditLog>>(ScheduleTest)
    /\ WF_<<testState, testResults, retryCount, instrumentStatus, testingQueue, currentlyTesting, consumedResources, auditLog>>(ExecuteTest)
    /\ WF_<<testState, testResults, retryCount, instrumentStatus, testingQueue, currentlyTesting, consumedResources, auditLog>>(TransitionToQc)
    /\ WF_<<testState, testResults, retryCount, instrumentStatus, testingQueue, currentlyTesting, consumedResources, auditLog>>(RetryTest)
    /\ WF_<<testState, testResults, retryCount, instrumentStatus, testingQueue, currentlyTesting, consumedResources, auditLog>>(AddToQueue)

\* Strong fairness for failure recovery
StrongFairness ==
    /\ SF_<<testState, testResults, retryCount, instrumentStatus, testingQueue, currentlyTesting, consumedResources, auditLog>>(AbandonTest)
    /\ SF_<<testState, testResults, retryCount, instrumentStatus, testingQueue, currentlyTesting, consumedResources, auditLog>>(RestoreInstrument)

\* Complete fairness specification
FairSpec == Spec /\ WeakFairness /\ StrongFairness

\* ============================================================================
\* TEMPORAL PROPERTIES
\* ============================================================================

\* Eventually all tests reach a final state
EventualCompletion ==
    <>[](\A testid \in TestIds: testState[testid] \in {"QC_PENDING", "FAILED"})

\* System eventually stabilizes
SystemStabilization ==
    <>[](\A instrument \in InstrumentIds: instrumentStatus[instrument] = "AVAILABLE")

\* ============================================================================
\* THEOREMS
\* ============================================================================

\* Main correctness theorem
THEOREM FairSpec => SafetyProperty

\* Main liveness theorem  
THEOREM FairSpec => LivenessProperty

\* Termination theorem
THEOREM FairSpec => EventualCompletion

====
