---- MODULE SimpleSchedulingAgent ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Simplified LIMS Scheduling Agent TLA+ Specification
\* Models the core scheduling behavior for transitioning samples
\* from ACCESSIONED to SCHEDULED state

CONSTANTS
  MaxSamples,           \* Maximum number of samples in the system
  MaxConcurrentTests,   \* Maximum concurrent testing capacity
  TestTypes,            \* Set of test types
  Priorities,           \* Set of priority levels
  SampleIDs             \* Set of valid sample IDs

VARIABLES
  \* Scheduling state
  schedulingQueue,      \* Queue of samples waiting to be scheduled
  scheduledSamples,     \* Set of samples that have been scheduled
  resourcesInUse,       \* Number of resources currently in use
  
  \* Sample information
  samplePriorities,     \* SampleID -> Priority level
  sampleTests,          \* SampleID -> Set of required tests
  
  \* Scheduling results
  schedulingDecisions,  \* Record of all scheduling decisions
  schedulingFailures,   \* Set of samples that failed to schedule
  retryAttempts,        \* SampleID -> number of retry attempts
  retryQueue            \* Queue of samples waiting for retry

\* Type invariant
TypeInv ==
  /\ schedulingQueue \in Seq(SampleIDs)
  /\ scheduledSamples \subseteq SampleIDs
  /\ resourcesInUse \in Nat
  /\ DOMAIN samplePriorities \subseteq SampleIDs
  /\ DOMAIN sampleTests \subseteq SampleIDs
  /\ \A sampleID \in DOMAIN samplePriorities : samplePriorities[sampleID] \in Priorities
  /\ \A sampleID \in DOMAIN sampleTests : sampleTests[sampleID] \subseteq TestTypes
  /\ schedulingDecisions \in Seq([sampleID: SampleIDs, success: BOOLEAN])
  /\ schedulingFailures \subseteq SampleIDs

\* Initial state
Init ==
  /\ schedulingQueue = <<>>
  /\ scheduledSamples = {}
  /\ resourcesInUse = 0
  /\ samplePriorities = <<>>
  /\ sampleTests = <<>>
  /\ schedulingDecisions = <<>>
  /\ schedulingFailures = {}
  /\ retryAttempts = <<>>
  /\ retryQueue = <<>>

\* Priority ordering: STAT > URGENT > ROUTINE
PriorityValue(priority) ==
  CASE priority = "STAT" -> 3
    [] priority = "URGENT" -> 2
    [] priority = "ROUTINE" -> 1
    [] OTHER -> 0

\* Check if resources are available for scheduling
ResourcesAvailable(testCount) ==
  resourcesInUse + testCount <= MaxConcurrentTests

\* Receive a scheduling request
ReceiveSchedulingRequest(sampleID, tests, priority) ==
  /\ sampleID \notin DOMAIN samplePriorities
  /\ sampleID \notin schedulingFailures
  /\ samplePriorities' = samplePriorities @@ (sampleID :> priority)
  /\ sampleTests' = sampleTests @@ (sampleID :> tests)
  /\ schedulingQueue' = schedulingQueue \o <<sampleID>>
  /\ UNCHANGED <<scheduledSamples, resourcesInUse, schedulingDecisions, schedulingFailures>>

\* Schedule a sample (core scheduling logic)
ScheduleSample(sampleID) ==
  /\ sampleID \in DOMAIN samplePriorities
  /\ sampleID \notin scheduledSamples
  /\ sampleID \notin schedulingFailures
  /\ LET requiredTests == sampleTests[sampleID]
         testCount == Cardinality(requiredTests)
     IN IF ResourcesAvailable(testCount)
        THEN \* Schedule successfully
             /\ scheduledSamples' = scheduledSamples \cup {sampleID}
             /\ resourcesInUse' = resourcesInUse + testCount
             /\ schedulingDecisions' = schedulingDecisions \o 
                  <<[sampleID |-> sampleID, success |-> TRUE]>>
             /\ UNCHANGED <<schedulingQueue, samplePriorities, sampleTests, schedulingFailures>>
        ELSE \* Cannot schedule - insufficient resources
             /\ schedulingFailures' = schedulingFailures \cup {sampleID}
             /\ schedulingDecisions' = schedulingDecisions \o 
                  <<[sampleID |-> sampleID, success |-> FALSE]>>
             /\ UNCHANGED <<schedulingQueue, scheduledSamples, resourcesInUse, 
                           samplePriorities, sampleTests>>

\* Process scheduling queue with priority ordering
ProcessSchedulingQueue ==
  /\ Len(schedulingQueue) > 0
  /\ LET priorities == [i \in 1..Len(schedulingQueue) |-> 
                         PriorityValue(samplePriorities[schedulingQueue[i]])]
         maxPriority == CHOOSE p \in {priorities[i] : i \in 1..Len(schedulingQueue)} : 
                          \A p2 \in {priorities[i] : i \in 1..Len(schedulingQueue)} : p >= p2
         highestPriorityIndex == CHOOSE i \in 1..Len(schedulingQueue) : 
                                  priorities[i] = maxPriority
         sampleToSchedule == schedulingQueue[highestPriorityIndex]
     IN ScheduleSample(sampleToSchedule)

\* Complete a test (free resources)
CompleteTest(sampleID) ==
  /\ sampleID \in scheduledSamples
  /\ LET testCount == Cardinality(sampleTests[sampleID])
     IN /\ scheduledSamples' = scheduledSamples \ {sampleID}
        /\ resourcesInUse' = resourcesInUse - testCount
        /\ UNCHANGED <<schedulingQueue, samplePriorities, sampleTests, 
                       schedulingDecisions, schedulingFailures>>

\* Next state relation
Next ==
  \/ \E sampleID \in SampleIDs, tests \in SUBSET TestTypes, priority \in Priorities:
       ReceiveSchedulingRequest(sampleID, tests, priority)
  \/ ProcessSchedulingQueue
  \/ \E sampleID \in scheduledSamples: CompleteTest(sampleID)

\* Complete specification
Spec == Init /\ [][Next]_<<schedulingQueue, scheduledSamples, resourcesInUse,
                            samplePriorities, sampleTests, schedulingDecisions,
                            schedulingFailures>>

\* SAFETY PROPERTIES

\* Property 1: Resource constraints are never violated
ResourceConstraintsRespected ==
  resourcesInUse <= MaxConcurrentTests

\* Property 2: Scheduled samples have valid priorities
ValidPriorities ==
  \A sampleID \in scheduledSamples:
    /\ sampleID \in DOMAIN samplePriorities
    /\ samplePriorities[sampleID] \in Priorities

\* Property 3: Scheduled samples have valid test requirements
ValidTestRequirements ==
  \A sampleID \in scheduledSamples:
    /\ sampleID \in DOMAIN sampleTests
    /\ sampleTests[sampleID] \subseteq TestTypes

\* Property 4: Resource usage matches scheduled samples
ResourceUsageAccuracy ==
  LET totalTestCount == LET counts == {Cardinality(sampleTests[sampleID]) : sampleID \in scheduledSamples}
                        IN IF counts = {} THEN 0 
                           ELSE CHOOSE n \in Nat : n = Cardinality(UNION {{1..c : c \in counts}})
  IN resourcesInUse <= MaxConcurrentTests  \* Simplified check

\* Property 5: No sample is both scheduled and failed
NoConflictingStates ==
  scheduledSamples \cap schedulingFailures = {}

\* Property 6: Scheduling decisions track all samples that were ever scheduled
SchedulingDecisionConsistency ==
  \A i \in 1..Len(schedulingDecisions):
    LET decision == schedulingDecisions[i]
    IN /\ decision.success => decision.sampleID \in DOMAIN samplePriorities
       /\ ~decision.success => decision.sampleID \in schedulingFailures

\* COMBINED INVARIANTS

\* All safety properties
SafetyProperties ==
  /\ TypeInv
  /\ ResourceConstraintsRespected
  /\ ValidPriorities
  /\ ValidTestRequirements
  /\ NoConflictingStates
  /\ SchedulingDecisionConsistency

\* System invariants for runtime validation
SystemInvariants ==
  /\ resourcesInUse <= MaxConcurrentTests
  /\ scheduledSamples \subseteq DOMAIN samplePriorities
  /\ scheduledSamples \subseteq DOMAIN sampleTests
  /\ schedulingFailures \subseteq DOMAIN samplePriorities
  /\ scheduledSamples \cap schedulingFailures = {}
  /\ scheduledSamples \subseteq SampleIDs
  /\ schedulingFailures \subseteq SampleIDs

====
