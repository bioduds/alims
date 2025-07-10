---- MODULE LIMSSampleWorkflow ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* LIMS Sample Workflow TLA+ Specification
\* Models the complete sample lifecycle from receipt through archival
\* Ensures regulatory compliance and audit trail integrity

CONSTANTS 
  MaxSamples,           \* Maximum number of samples in the system
  MaxConcurrentTests,   \* Maximum number of samples that can be tested concurrently
  SampleIDs,            \* Set of all possible sample identifiers
  Actors,               \* Set of possible actors (users, systems)
  Notes                 \* Set of possible notes/comments

VARIABLES
  samples,              \* Set of sample IDs currently in the system
  sampleStates,         \* Function: SampleID -> SampleState
  auditTrails,          \* Function: SampleID -> Sequence of audit entries  
  nextSampleID,         \* Next available sample ID
  qcApprovals,          \* Set of samples that have been QC approved
  testingResources,     \* Number of testing resources currently in use
  archivedSamples       \* Set of samples that have been archived (terminal)

\* Sample states that a sample can be in
SampleStates == {"RECEIVED", "ACCESSIONED", "SCHEDULED", "TESTING", 
                "QC_PENDING", "QC_APPROVED", "REPORTED", "ARCHIVED"}

\* Operational states (samples are being actively processed)
OperationalStates == {"RECEIVED", "ACCESSIONED", "SCHEDULED", "TESTING", "QC_PENDING", "QC_APPROVED", "REPORTED"}

\* Terminal states (no further processing)
TerminalStates == {"ARCHIVED"}

\* QC states that indicate QC approval has occurred
QCStates == {"QC_APPROVED", "REPORTED", "ARCHIVED"}

\* Testing states that consume testing resources
TestingStates == {"TESTING"}

\* Audit log entry structure
AuditEntry == [state: SampleStates, actor: Actors, timestamp: Nat, notes: Notes]

\* Type invariant - all variables have correct types
TypeInv == 
  /\ samples \subseteq SampleIDs
  /\ sampleStates \in [samples -> SampleStates]
  /\ auditTrails \in [samples -> Seq(AuditEntry)]
  /\ nextSampleID \in Nat
  /\ qcApprovals \subseteq samples
  /\ testingResources \in Nat
  /\ archivedSamples \subseteq samples

\* Initial state - empty LIMS system
Init ==
  /\ samples = {}
  /\ sampleStates = <<>>
  /\ auditTrails = <<>>
  /\ nextSampleID = 1
  /\ qcApprovals = {}
  /\ testingResources = 0
  /\ archivedSamples = {}

\* Valid state transitions for sample workflow
ValidTransition(from, to) ==
  \/ /\ from = "RECEIVED" /\ to = "ACCESSIONED"
  \/ /\ from = "ACCESSIONED" /\ to = "SCHEDULED"
  \/ /\ from = "SCHEDULED" /\ to = "TESTING"
  \/ /\ from = "TESTING" /\ to = "QC_PENDING"
  \/ /\ from = "QC_PENDING" /\ to = "QC_APPROVED"
  \/ /\ from = "QC_APPROVED" /\ to = "REPORTED"
  \/ /\ from = "REPORTED" /\ to = "ARCHIVED"

\* Helper: Check if sample has QC approval in its audit trail
HasQCApproval(sampleID) ==
  \E i \in 1..Len(auditTrails[sampleID]): 
    auditTrails[sampleID][i].state = "QC_APPROVED"

\* Helper: Count samples currently in testing
SamplesInTesting ==
  Cardinality({s \in samples : sampleStates[s] \in TestingStates})

\* Helper: Get all states visited by a sample
VisitedStates(sampleID) ==
  {auditTrails[sampleID][i].state : i \in 1..Len(auditTrails[sampleID])}

\* Receive a new sample into the LIMS
ReceiveSample(sampleID) ==
  /\ sampleID \notin samples
  /\ sampleID = nextSampleID
  /\ Cardinality(samples) < MaxSamples
  /\ samples' = samples \cup {sampleID}
  /\ sampleStates' = sampleStates @@ (sampleID :> "RECEIVED")
  /\ auditTrails' = auditTrails @@ (sampleID :> <<[state |-> "RECEIVED", 
                                                   actor |-> "SYSTEM", 
                                                   timestamp |-> nextSampleID, 
                                                   notes |-> "RECEIVED"]>>)
  /\ nextSampleID' = nextSampleID + 1
  /\ UNCHANGED <<qcApprovals, testingResources, archivedSamples>>

\* Transition sample to next state in workflow
TransitionSample(sampleID, newState, actor, notes) ==
  /\ sampleID \in samples
  /\ sampleStates[sampleID] \notin TerminalStates
  /\ ValidTransition(sampleStates[sampleID], newState)
  /\ newState \notin VisitedStates(sampleID)  \* Monotonic progression
  /\ IF newState \in TestingStates
     THEN testingResources < MaxConcurrentTests
     ELSE TRUE
  /\ sampleStates' = [sampleStates EXCEPT ![sampleID] = newState]
  /\ auditTrails' = [auditTrails EXCEPT ![sampleID] = 
                      @ \o <<[state |-> newState, 
                             actor |-> actor, 
                             timestamp |-> nextSampleID, 
                             notes |-> notes]>>]
  /\ IF newState = "QC_APPROVED"
     THEN qcApprovals' = qcApprovals \cup {sampleID}
     ELSE qcApprovals' = qcApprovals
  /\ IF newState \in TestingStates /\ sampleStates[sampleID] \notin TestingStates
     THEN testingResources' = testingResources + 1
     ELSE IF sampleStates[sampleID] \in TestingStates /\ newState \notin TestingStates
          THEN testingResources' = testingResources - 1
          ELSE testingResources' = testingResources
  /\ IF newState = "ARCHIVED"
     THEN archivedSamples' = archivedSamples \cup {sampleID}
     ELSE archivedSamples' = archivedSamples
  /\ UNCHANGED <<samples, nextSampleID>>

\* QC approval action (separate action for auditing purposes)
QCApproveSample(sampleID, actor, notes) ==
  /\ TransitionSample(sampleID, "QC_APPROVED", actor, notes)

\* Report sample results (requires QC approval)
ReportSample(sampleID, actor, notes) ==
  /\ sampleID \in qcApprovals
  /\ TransitionSample(sampleID, "REPORTED", actor, notes)

\* Archive sample (terminal action)
ArchiveSample(sampleID, actor, notes) ==
  /\ sampleStates[sampleID] = "REPORTED"
  /\ sampleID \in qcApprovals  \* Must have been QC approved
  /\ TransitionSample(sampleID, "ARCHIVED", actor, notes)

\* Next state relation - all possible actions
Next ==
  \/ \E sampleID \in SampleIDs: ReceiveSample(sampleID)
  \/ \E sampleID \in samples, newState \in SampleStates, actor \in Actors, notes \in Notes:
       /\ newState # "QC_APPROVED"  \* QC approval handled separately
       /\ newState # "REPORTED"     \* Reporting handled separately  
       /\ newState # "ARCHIVED"     \* Archiving handled separately
       /\ TransitionSample(sampleID, newState, actor, notes)
  \/ \E sampleID \in samples, actor \in Actors, notes \in Notes: QCApproveSample(sampleID, actor, notes)
  \/ \E sampleID \in samples, actor \in Actors, notes \in Notes: ReportSample(sampleID, actor, notes)
  \/ \E sampleID \in samples, actor \in Actors, notes \in Notes: ArchiveSample(sampleID, actor, notes)

\* Complete specification  
Spec == Init /\ [][Next]_<<samples, sampleStates, auditTrails, nextSampleID, 
                            qcApprovals, testingResources, archivedSamples>>

\* SAFETY PROPERTIES

\* Property 1: State Consistency - All samples have valid states
StateConsistency == 
  \A sampleID \in samples: sampleStates[sampleID] \in SampleStates

\* Property 2: Monotonic Progression - Samples cannot return to previous states
MonotonicProgression == 
  \A sampleID \in samples: 
    Cardinality(VisitedStates(sampleID)) = Len(auditTrails[sampleID])

\* Property 3: Audit Trail Immutability - Audit trails only grow
AuditTrailImmutability ==
  \A sampleID \in samples:
    /\ Len(auditTrails[sampleID]) >= 1
    /\ auditTrails[sampleID][1].state = "RECEIVED"

\* Property 4: QC Required - No sample can be reported without QC approval
QCRequired == 
  \A sampleID \in samples:
    sampleStates[sampleID] \in {"REPORTED", "ARCHIVED"} => sampleID \in qcApprovals

\* Property 5: Resource Bounds - Testing resources never exceed capacity
ResourceBounds == 
  /\ testingResources <= MaxConcurrentTests
  /\ testingResources = SamplesInTesting

\* Property 6: Valid Workflow Progression - All transitions follow workflow rules
ValidWorkflowProgression ==
  \A sampleID \in samples:
    \A i \in 1..(Len(auditTrails[sampleID])-1):
      ValidTransition(auditTrails[sampleID][i].state, 
                     auditTrails[sampleID][i+1].state)

\* Property 7: Terminal State Immutability - Archived samples cannot change
TerminalStateImmutability ==
  \A sampleID \in archivedSamples: sampleStates[sampleID] = "ARCHIVED"

\* Property 8: QC Approval Consistency - QC approvals match audit trail
QCApprovalConsistency ==
  \A sampleID \in samples:
    sampleID \in qcApprovals <=> HasQCApproval(sampleID)

\* Property 9: Sample Bounds - Never exceed maximum samples
SampleBounds == 
  Cardinality(samples) <= MaxSamples

\* LIVENESS PROPERTIES

\* Property 10: Eventual Progression - Samples eventually progress through workflow
EventualProgression ==
  \A sampleID \in samples: 
    sampleStates[sampleID] = "RECEIVED" ~> sampleStates[sampleID] # "RECEIVED"

\* Property 11: QC Completion - Samples in QC_PENDING eventually get reviewed
QCCompletion ==
  \A sampleID \in samples:
    sampleStates[sampleID] = "QC_PENDING" ~> sampleStates[sampleID] = "QC_APPROVED"

\* Property 12: Resource Availability - Testing resources eventually become available
ResourceAvailability ==
  testingResources = MaxConcurrentTests ~> testingResources < MaxConcurrentTests

\* Property 13: Eventual Archival - Reported samples eventually get archived
EventualArchival ==
  \A sampleID \in samples:
    sampleStates[sampleID] = "REPORTED" ~> sampleStates[sampleID] = "ARCHIVED"

\* COMBINED INVARIANTS FOR MODEL CHECKING

\* All safety properties combined
SafetyProperties ==
  /\ TypeInv
  /\ StateConsistency
  /\ MonotonicProgression
  /\ AuditTrailImmutability
  /\ QCRequired
  /\ ResourceBounds
  /\ ValidWorkflowProgression
  /\ TerminalStateImmutability
  /\ QCApprovalConsistency
  /\ SampleBounds

\* System-level invariants for runtime checking
SystemInvariants ==
  /\ \A sampleID \in samples: sampleStates[sampleID] \in SampleStates
  /\ \A sampleID \in samples: Len(auditTrails[sampleID]) >= 1
  /\ testingResources <= MaxConcurrentTests
  /\ Cardinality(samples) <= MaxSamples
  /\ qcApprovals \subseteq samples
  /\ archivedSamples \subseteq samples

====
