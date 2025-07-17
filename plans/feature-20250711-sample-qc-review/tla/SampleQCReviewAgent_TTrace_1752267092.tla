---- MODULE SampleQCReviewAgent_TTrace_1752267092 ----
EXTENDS Sequences, TLCExt, Toolbox, SampleQCReviewAgent, Naturals, TLC

_expression ==
    LET SampleQCReviewAgent_TEExpression == INSTANCE SampleQCReviewAgent_TEExpression
    IN SampleQCReviewAgent_TEExpression!expression
----

_trace ==
    LET SampleQCReviewAgent_TETrace == INSTANCE SampleQCReviewAgent_TETrace
    IN SampleQCReviewAgent_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        qcEscalated = ({})
        /\
        reviewerAssignments = (<<0, 0, 0>>)
        /\
        reviewerWorkload = (<<0, 0>>)
        /\
        qcQueue = (<<1>>)
        /\
        qcInReview = ({})
        /\
        qcRejected = ({})
        /\
        qcApproved = ({})
        /\
        sampleResults = (<<[value |-> 1, critical |-> TRUE], [value |-> 0, critical |-> FALSE], [value |-> 0, critical |-> FALSE]>>)
        /\
        qcDecisions = (<<>>)
        /\
        auditTrail = (<<[sampleID |-> 1, action |-> "RECEIVED_FOR_QC"]>>)
    )
----

_init ==
    /\ reviewerAssignments = _TETrace[1].reviewerAssignments
    /\ qcRejected = _TETrace[1].qcRejected
    /\ qcApproved = _TETrace[1].qcApproved
    /\ qcDecisions = _TETrace[1].qcDecisions
    /\ auditTrail = _TETrace[1].auditTrail
    /\ reviewerWorkload = _TETrace[1].reviewerWorkload
    /\ sampleResults = _TETrace[1].sampleResults
    /\ qcQueue = _TETrace[1].qcQueue
    /\ qcEscalated = _TETrace[1].qcEscalated
    /\ qcInReview = _TETrace[1].qcInReview
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ reviewerAssignments  = _TETrace[i].reviewerAssignments
        /\ reviewerAssignments' = _TETrace[j].reviewerAssignments
        /\ qcRejected  = _TETrace[i].qcRejected
        /\ qcRejected' = _TETrace[j].qcRejected
        /\ qcApproved  = _TETrace[i].qcApproved
        /\ qcApproved' = _TETrace[j].qcApproved
        /\ qcDecisions  = _TETrace[i].qcDecisions
        /\ qcDecisions' = _TETrace[j].qcDecisions
        /\ auditTrail  = _TETrace[i].auditTrail
        /\ auditTrail' = _TETrace[j].auditTrail
        /\ reviewerWorkload  = _TETrace[i].reviewerWorkload
        /\ reviewerWorkload' = _TETrace[j].reviewerWorkload
        /\ sampleResults  = _TETrace[i].sampleResults
        /\ sampleResults' = _TETrace[j].sampleResults
        /\ qcQueue  = _TETrace[i].qcQueue
        /\ qcQueue' = _TETrace[j].qcQueue
        /\ qcEscalated  = _TETrace[i].qcEscalated
        /\ qcEscalated' = _TETrace[j].qcEscalated
        /\ qcInReview  = _TETrace[i].qcInReview
        /\ qcInReview' = _TETrace[j].qcInReview

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("SampleQCReviewAgent_TTrace_1752267092.json", _TETrace)

=============================================================================

 Note that you can extract this module `SampleQCReviewAgent_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `SampleQCReviewAgent_TEExpression.tla` file takes precedence 
  over the module `SampleQCReviewAgent_TEExpression` below).

---- MODULE SampleQCReviewAgent_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, SampleQCReviewAgent, Naturals, TLC

expression == 
    [
        \* To hide variables of the `SampleQCReviewAgent` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        reviewerAssignments |-> reviewerAssignments
        ,qcRejected |-> qcRejected
        ,qcApproved |-> qcApproved
        ,qcDecisions |-> qcDecisions
        ,auditTrail |-> auditTrail
        ,reviewerWorkload |-> reviewerWorkload
        ,sampleResults |-> sampleResults
        ,qcQueue |-> qcQueue
        ,qcEscalated |-> qcEscalated
        ,qcInReview |-> qcInReview
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_reviewerAssignmentsUnchanged |-> reviewerAssignments = reviewerAssignments'
        
        \* Format the `reviewerAssignments` variable as Json value.
        \* ,_reviewerAssignmentsJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(reviewerAssignments)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_reviewerAssignmentsModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].reviewerAssignments # _TETrace[s-1].reviewerAssignments
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE SampleQCReviewAgent_TETrace ----
\*EXTENDS IOUtils, SampleQCReviewAgent, TLC
\*
\*trace == IODeserialize("SampleQCReviewAgent_TTrace_1752267092.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE SampleQCReviewAgent_TETrace ----
EXTENDS SampleQCReviewAgent, TLC

trace == 
    <<
    ([qcEscalated |-> {},reviewerAssignments |-> <<0, 0, 0>>,reviewerWorkload |-> <<0, 0>>,qcQueue |-> <<>>,qcInReview |-> {},qcRejected |-> {},qcApproved |-> {},sampleResults |-> <<[value |-> 0, critical |-> FALSE], [value |-> 0, critical |-> FALSE], [value |-> 0, critical |-> FALSE]>>,qcDecisions |-> <<>>,auditTrail |-> <<>>]),
    ([qcEscalated |-> {},reviewerAssignments |-> <<0, 0, 0>>,reviewerWorkload |-> <<0, 0>>,qcQueue |-> <<1>>,qcInReview |-> {},qcRejected |-> {},qcApproved |-> {},sampleResults |-> <<[value |-> 1, critical |-> TRUE], [value |-> 0, critical |-> FALSE], [value |-> 0, critical |-> FALSE]>>,qcDecisions |-> <<>>,auditTrail |-> <<[sampleID |-> 1, action |-> "RECEIVED_FOR_QC"]>>])
    >>
----


=============================================================================

---- CONFIG SampleQCReviewAgent_TTrace_1752267092 ----
CONSTANTS
    MaxSamples = 3
    MaxReviewers = 2
    TestTypes = { "CBC" , "BMP" , "LIPID" }
    QCRules = { "1_2s" , "1_3s" , "2_2s" }
    CriticalThresholds = { "Critical" }
    ReferenceRanges = { "Normal" }
    SampleIDs = { 1 , 2 , 3 }

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Fri Jul 11 17:51:32 BRT 2025