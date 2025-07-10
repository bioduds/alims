----------------------- MODULE CoreLIMSWorkflow -----------------------
(*
 * TLA+ Specification for Core LIMS Sample Workflow
 * 
 * This specification models the fundamental sample processing workflow
 * in the ALIMS laboratory information management system.
 * 
 * Key Properties:
 * - Sample Traceability: Every sample has unique ID and full audit trail
 * - State Consistency: Samples progress through valid state transitions only
 * - Data Integrity: No corruption or loss of sample data
 * - Quality Control: All results validated before reporting
 *)

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Sample states enumeration
CONSTANTS RECEIVED, ACCESSIONED, SCHEDULED, TESTING, QC_PENDING, QC_APPROVED, REPORTED, ARCHIVED

\* Set of all valid sample states
SampleStates == {RECEIVED, ACCESSIONED, SCHEDULED, TESTING, QC_PENDING, QC_APPROVED, REPORTED, ARCHIVED}

\* Maximum number of samples in the system (for model checking)
CONSTANTS MaxSamples

\* Assume reasonable bounds for model checking
ASSUME MaxSamples \in Nat /\ MaxSamples > 0

\* Sample IDs
SampleIDs == 1..MaxSamples

\* Variables
VARIABLES
    samples,        \* Sample ID -> Sample record
    sampleStates,   \* Sample ID -> Current state
    auditTrail,     \* Sample ID -> Sequence of state transitions
    nextSampleID    \* Next available sample ID

vars == <<samples, sampleStates, auditTrail, nextSampleID>>

\* Type invariant
TypeInv ==
    /\ samples \in [SampleIDs -> [id: SampleIDs, barcode: STRING, receivedAt: Nat]]
    /\ sampleStates \in [SampleIDs -> SampleStates]
    /\ auditTrail \in [SampleIDs -> Seq(SampleStates)]
    /\ nextSampleID \in 1..(MaxSamples + 1)

\* Initial state
Init ==
    /\ samples = [id \in SampleIDs |-> [id |-> id, barcode |-> "", receivedAt |-> 0]]
    /\ sampleStates = [id \in SampleIDs |-> RECEIVED]
    /\ auditTrail = [id \in SampleIDs |-> <<>>]
    /\ nextSampleID = 1

\* Helper predicates
SampleExists(id) == id < nextSampleID
ValidTransition(from, to) ==
    \/ (from = RECEIVED /\ to = ACCESSIONED)
    \/ (from = ACCESSIONED /\ to = SCHEDULED)
    \/ (from = SCHEDULED /\ to = TESTING)
    \/ (from = TESTING /\ to = QC_PENDING)
    \/ (from = QC_PENDING /\ to = QC_APPROVED)
    \/ (from = QC_APPROVED /\ to = REPORTED)
    \/ (from = REPORTED /\ to = ARCHIVED)

\* Action: Receive new sample
ReceiveSample ==
    /\ nextSampleID <= MaxSamples
    /\ samples' = [samples EXCEPT ![nextSampleID] = 
        [id |-> nextSampleID, barcode |-> ToString(nextSampleID), receivedAt |-> 1]]
    /\ sampleStates' = [sampleStates EXCEPT ![nextSampleID] = RECEIVED]
    /\ auditTrail' = [auditTrail EXCEPT ![nextSampleID] = <<RECEIVED>>]
    /\ nextSampleID' = nextSampleID + 1

\* Action: Transition sample to next state
TransitionSample(id, newState) ==
    /\ SampleExists(id)
    /\ ValidTransition(sampleStates[id], newState)
    /\ sampleStates' = [sampleStates EXCEPT ![id] = newState]
    /\ auditTrail' = [auditTrail EXCEPT ![id] = Append(auditTrail[id], newState)]
    /\ UNCHANGED <<samples, nextSampleID>>

\* Action: Accession sample (RECEIVED -> ACCESSIONED)
AccessionSample(id) ==
    /\ SampleExists(id)
    /\ sampleStates[id] = RECEIVED
    /\ TransitionSample(id, ACCESSIONED)

\* Action: Schedule tests (ACCESSIONED -> SCHEDULED)
ScheduleTests(id) ==
    /\ SampleExists(id)
    /\ sampleStates[id] = ACCESSIONED
    /\ TransitionSample(id, SCHEDULED)

\* Action: Begin testing (SCHEDULED -> TESTING)
BeginTesting(id) ==
    /\ SampleExists(id)
    /\ sampleStates[id] = SCHEDULED
    /\ TransitionSample(id, TESTING)

\* Action: Complete testing (TESTING -> QC_PENDING)
CompleteTesting(id) ==
    /\ SampleExists(id)
    /\ sampleStates[id] = TESTING
    /\ TransitionSample(id, QC_PENDING)

\* Action: Approve QC (QC_PENDING -> QC_APPROVED)
ApproveQC(id) ==
    /\ SampleExists(id)
    /\ sampleStates[id] = QC_PENDING
    /\ TransitionSample(id, QC_APPROVED)

\* Action: Generate report (QC_APPROVED -> REPORTED)
GenerateReport(id) ==
    /\ SampleExists(id)
    /\ sampleStates[id] = QC_APPROVED
    /\ TransitionSample(id, REPORTED)

\* Action: Archive sample (REPORTED -> ARCHIVED)
ArchiveSample(id) ==
    /\ SampleExists(id)
    /\ sampleStates[id] = REPORTED
    /\ TransitionSample(id, ARCHIVED)

\* Next state relation
Next ==
    \/ ReceiveSample
    \/ \E id \in SampleIDs:
        \/ AccessionSample(id)
        \/ ScheduleTests(id)
        \/ BeginTesting(id)
        \/ CompleteTesting(id)
        \/ ApproveQC(id)
        \/ GenerateReport(id)
        \/ ArchiveSample(id)

\* Specification
Spec == Init /\ [][Next]_vars

\* Safety Properties (Invariants)

\* INV1: Sample IDs are unique and valid
SampleIDUniqueness ==
    \A id \in DOMAIN sampleStates : samples[id].id = id

\* INV2: Audit trail consistency
AuditTrailConsistency ==
    \A id \in SampleIDs :
        id < nextSampleID => 
            /\ Len(auditTrail[id]) > 0 
            /\ Head(auditTrail[id]) = RECEIVED
            /\ sampleStates[id] = auditTrail[id][Len(auditTrail[id])]

\* INV3: State transition validity
StateTransitionValidity ==
    \A id \in DOMAIN auditTrail :
        \A i \in 1..(Len(auditTrail[id])-1) :
            ValidTransition(auditTrail[id][i], auditTrail[id][i+1])

\* INV4: No sample can be reported without QC approval
QCRequired ==
    \A id \in DOMAIN sampleStates :
        sampleStates[id] \in {REPORTED, ARCHIVED} =>
            \E i \in 1..Len(auditTrail[id]) : auditTrail[id][i] = QC_APPROVED

\* INV5: Monotonic progression (no backwards transitions)
MonotonicProgression ==
    \A id \in DOMAIN auditTrail :
        \A i, j \in 1..Len(auditTrail[id]) :
            i < j => auditTrail[id][i] # auditTrail[id][j]

\* Combined safety property
SafetyInv ==
    /\ TypeInv
    /\ SampleIDUniqueness
    /\ AuditTrailConsistency
    /\ StateTransitionValidity
    /\ QCRequired
    /\ MonotonicProgression

\* Liveness Properties

\* LIVE1: Every received sample eventually gets processed
EventualProcessing ==
    \A id \in DOMAIN sampleStates :
        sampleStates[id] = RECEIVED ~> sampleStates[id] = ARCHIVED

\* LIVE2: No sample gets stuck in any intermediate state
NoDeadlock ==
    \A id \in DOMAIN sampleStates :
        sampleStates[id] \in {ACCESSIONED, SCHEDULED, TESTING, QC_PENDING, QC_APPROVED, REPORTED}
        ~> sampleStates[id] = ARCHIVED

\* Combined liveness property
LivenessSpec ==
    /\ EventualProcessing
    /\ NoDeadlock

============================================================================
