---- MODULE SampleQCReviewAgent ----
EXTENDS Naturals, Sequences, FiniteSets

\* LIMS Sample QC Review Agent TLA+ Specification
\* Models the quality control review process for laboratory samples

CONSTANTS
  MaxSamples,
  MaxReviewers,
  SampleIDs

VARIABLES
  qcQueue,              \* Queue of samples awaiting QC review
  qcInReview,           \* Set of samples currently being reviewed
  qcApproved,           \* Set of samples that passed QC review
  qcRejected,           \* Set of samples that failed QC review
  qcEscalated,          \* Set of samples requiring escalation
  sampleResults,        \* Function mapping Sample ID to test results
  reviewerAssignments,  \* Function mapping Sample ID to assigned reviewer
  reviewerWorkload,     \* Function mapping Reviewer ID to current workload
  qcDecisions,          \* Sequence of QC decisions made
  auditTrail            \* Complete audit trail of all QC actions

Init ==
  /\ qcQueue = <<>>
  /\ qcInReview = {}
  /\ qcApproved = {}
  /\ qcRejected = {}
  /\ qcEscalated = {}
  /\ sampleResults = [s \in SampleIDs |-> [value |-> 0, critical |-> FALSE]]
  /\ reviewerAssignments = [s \in SampleIDs |-> 0]
  /\ reviewerWorkload = [r \in 1..MaxReviewers |-> 0]
  /\ qcDecisions = <<>>
  /\ auditTrail = <<>>

\* Helper functions
HasCriticalValues(sampleID) ==
  sampleResults[sampleID].critical = TRUE

WithinReferenceRange(sampleID) ==
  sampleResults[sampleID].value >= 4 /\ sampleResults[sampleID].value <= 12

RequiresEscalation(sampleID) ==
  HasCriticalValues(sampleID) \/ ~WithinReferenceRange(sampleID)

\* Actions
ReceiveForQCReview(sampleID, value, critical) ==
  /\ sampleID \in SampleIDs
  /\ sampleID \notin (qcApproved \cup qcRejected \cup qcEscalated)
  /\ Len(qcQueue) < MaxSamples
  /\ qcQueue' = qcQueue \o <<sampleID>>
  /\ sampleResults' = [sampleResults EXCEPT ![sampleID] = [value |-> value, critical |-> critical]]
  /\ auditTrail' = auditTrail \o <<[action |-> "RECEIVED_FOR_QC", sampleID |-> sampleID]>>
  /\ UNCHANGED <<qcInReview, qcApproved, qcRejected, qcEscalated,
                 reviewerAssignments, reviewerWorkload, qcDecisions>>

AssignReviewer(sampleID, reviewerID) ==
  /\ sampleID \in SampleIDs
  /\ reviewerAssignments[sampleID] = 0
  /\ reviewerID \in 1..MaxReviewers
  /\ reviewerWorkload[reviewerID] < 3
  /\ reviewerAssignments' = [reviewerAssignments EXCEPT ![sampleID] = reviewerID]
  /\ reviewerWorkload' = [reviewerWorkload EXCEPT ![reviewerID] = @ + 1]
  /\ auditTrail' = auditTrail \o <<[action |-> "REVIEWER_ASSIGNED", sampleID |-> sampleID]>>
  /\ UNCHANGED <<qcQueue, qcInReview, qcApproved, qcRejected, qcEscalated,
                 sampleResults, qcDecisions>>

StartQCReview(sampleID) ==
  /\ sampleID \in SampleIDs
  /\ reviewerAssignments[sampleID] # 0
  /\ sampleID \notin qcInReview
  /\ qcInReview' = qcInReview \cup {sampleID}
  /\ qcQueue' = SelectSeq(qcQueue, LAMBDA x: x # sampleID)
  /\ auditTrail' = auditTrail \o <<[action |-> "QC_REVIEW_STARTED", sampleID |-> sampleID]>>
  /\ UNCHANGED <<qcApproved, qcRejected, qcEscalated, sampleResults,
                 reviewerAssignments, reviewerWorkload, qcDecisions>>

ApproveQCReview(sampleID) ==
  /\ sampleID \in qcInReview
  /\ WithinReferenceRange(sampleID)
  /\ ~HasCriticalValues(sampleID)
  /\ qcInReview' = qcInReview \ {sampleID}
  /\ qcApproved' = qcApproved \cup {sampleID}
  /\ reviewerWorkload' = [reviewerWorkload EXCEPT ![reviewerAssignments[sampleID]] = @ - 1]
  /\ qcDecisions' = qcDecisions \o <<[sampleID |-> sampleID, decision |-> "APPROVED"]>>
  /\ auditTrail' = auditTrail \o <<[action |-> "QC_APPROVED", sampleID |-> sampleID]>>
  /\ UNCHANGED <<qcQueue, qcRejected, qcEscalated, sampleResults, reviewerAssignments>>

RejectQCReview(sampleID) ==
  /\ sampleID \in qcInReview
  /\ ~WithinReferenceRange(sampleID)
  /\ ~HasCriticalValues(sampleID)
  /\ qcInReview' = qcInReview \ {sampleID}
  /\ qcRejected' = qcRejected \cup {sampleID}
  /\ reviewerWorkload' = [reviewerWorkload EXCEPT ![reviewerAssignments[sampleID]] = @ - 1]
  /\ qcDecisions' = qcDecisions \o <<[sampleID |-> sampleID, decision |-> "REJECTED"]>>
  /\ auditTrail' = auditTrail \o <<[action |-> "QC_REJECTED", sampleID |-> sampleID]>>
  /\ UNCHANGED <<qcQueue, qcApproved, qcEscalated, sampleResults, reviewerAssignments>>

EscalateQCReview(sampleID) ==
  /\ sampleID \in qcInReview
  /\ RequiresEscalation(sampleID)
  /\ qcInReview' = qcInReview \ {sampleID}
  /\ qcEscalated' = qcEscalated \cup {sampleID}
  /\ reviewerWorkload' = [reviewerWorkload EXCEPT ![reviewerAssignments[sampleID]] = @ - 1]
  /\ qcDecisions' = qcDecisions \o <<[sampleID |-> sampleID, decision |-> "ESCALATED"]>>
  /\ auditTrail' = auditTrail \o <<[action |-> "QC_ESCALATED", sampleID |-> sampleID]>>
  /\ UNCHANGED <<qcQueue, qcApproved, qcRejected, sampleResults, reviewerAssignments>>

Next ==
  \/ \E sampleID \in SampleIDs, value \in 1..20, critical \in BOOLEAN:
       ReceiveForQCReview(sampleID, value, critical)
  \/ \E sampleID \in SampleIDs, reviewerID \in 1..MaxReviewers:
       AssignReviewer(sampleID, reviewerID)
  \/ \E sampleID \in SampleIDs:
       StartQCReview(sampleID)
  \/ \E sampleID \in SampleIDs:
       ApproveQCReview(sampleID)
  \/ \E sampleID \in SampleIDs:
       RejectQCReview(sampleID)
  \/ \E sampleID \in SampleIDs:
       EscalateQCReview(sampleID)
  \/ UNCHANGED <<qcQueue, qcInReview, qcApproved, qcRejected, qcEscalated,
                 sampleResults, reviewerAssignments, reviewerWorkload, qcDecisions, auditTrail>>

Spec == Init /\ [][Next]_<<qcQueue, qcInReview, qcApproved, qcRejected, qcEscalated,
                            sampleResults, reviewerAssignments, reviewerWorkload, qcDecisions, auditTrail>>

\* SAFETY PROPERTIES

TypeInv ==
  /\ qcQueue \in Seq(SampleIDs)
  /\ qcInReview \subseteq SampleIDs
  /\ qcApproved \subseteq SampleIDs
  /\ qcRejected \subseteq SampleIDs
  /\ qcEscalated \subseteq SampleIDs
  /\ sampleResults \in [SampleIDs -> [value: Nat, critical: BOOLEAN]]
  /\ reviewerAssignments \in [SampleIDs -> 0..MaxReviewers]
  /\ reviewerWorkload \in [1..MaxReviewers -> Nat]

QCRequired ==
  \A sampleID \in qcApproved:
    \E i \in DOMAIN qcDecisions:
      /\ qcDecisions[i].sampleID = sampleID
      /\ qcDecisions[i].decision = "APPROVED"

AuditTrailComplete ==
  \A sampleID \in (qcApproved \cup qcRejected \cup qcEscalated):
    \E i \in DOMAIN auditTrail:
      auditTrail[i].sampleID = sampleID

CriticalValuesEscalated ==
  \A sampleID \in SampleIDs:
    HasCriticalValues(sampleID) => 
      (sampleID \in qcEscalated \/ sampleID \in qcInReview \/ 
       \E i \in DOMAIN qcQueue: qcQueue[i] = sampleID)

ReviewerAssignmentRequired ==
  \A sampleID \in qcInReview:
    reviewerAssignments[sampleID] # 0

MutualExclusion ==
  \A sampleID \in SampleIDs:
    Cardinality({s \in {qcInReview, qcApproved, qcRejected, qcEscalated} : sampleID \in s}) <= 1

WorkloadLimits ==
  \A reviewerID \in 1..MaxReviewers:
    reviewerWorkload[reviewerID] <= 3

DecisionConsistency ==
  \A i \in DOMAIN qcDecisions:
    /\ qcDecisions[i].decision = "APPROVED" => WithinReferenceRange(qcDecisions[i].sampleID)
    /\ qcDecisions[i].decision = "ESCALATED" => RequiresEscalation(qcDecisions[i].sampleID)

SafetyProperties ==
  /\ TypeInv
  /\ QCRequired
  /\ AuditTrailComplete
  /\ CriticalValuesEscalated
  /\ ReviewerAssignmentRequired
  /\ MutualExclusion
  /\ WorkloadLimits
  /\ DecisionConsistency

SystemInvariants ==
  /\ SafetyProperties
  /\ Len(qcQueue) <= MaxSamples
  /\ Cardinality(qcInReview) <= MaxReviewers * 3

====
