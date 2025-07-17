---- MODULE SimpleQCReviewAgent ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  MaxSamples,
  SampleIDs

VARIABLES
  qcQueue,
  qcApproved,
  qcRejected

Init ==
  /\ qcQueue = <<>>
  /\ qcApproved = {}
  /\ qcRejected = {}

AddToQueue(sampleID) ==
  /\ sampleID \in SampleIDs
  /\ sampleID \notin (qcApproved \cup qcRejected)
  /\ qcQueue' = qcQueue \o <<sampleID>>
  /\ UNCHANGED <<qcApproved, qcRejected>>

ApproveQC(sampleID) ==
  /\ sampleID \in DOMAIN qcQueue
  /\ qcApproved' = qcApproved \cup {sampleID}
  /\ qcQueue' = SelectSeq(qcQueue, LAMBDA x: x # sampleID)
  /\ UNCHANGED qcRejected

RejectQC(sampleID) ==
  /\ sampleID \in DOMAIN qcQueue
  /\ qcRejected' = qcRejected \cup {sampleID}
  /\ qcQueue' = SelectSeq(qcQueue, LAMBDA x: x # sampleID)
  /\ UNCHANGED qcApproved

Next ==
  \/ \E sampleID \in SampleIDs: AddToQueue(sampleID)
  \/ \E sampleID \in SampleIDs: ApproveQC(sampleID)
  \/ \E sampleID \in SampleIDs: RejectQC(sampleID)

Spec == Init /\ [][Next]_<<qcQueue, qcApproved, qcRejected>>

TypeInv ==
  /\ qcQueue \in Seq(SampleIDs)
  /\ qcApproved \subseteq SampleIDs
  /\ qcRejected \subseteq SampleIDs

SafetyProperties == TypeInv

====
