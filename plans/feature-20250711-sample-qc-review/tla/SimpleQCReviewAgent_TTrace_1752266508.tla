---- MODULE SimpleQCReviewAgent_TTrace_1752266508 ----
EXTENDS SimpleQCReviewAgent, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET SimpleQCReviewAgent_TEExpression == INSTANCE SimpleQCReviewAgent_TEExpression
    IN SimpleQCReviewAgent_TEExpression!expression
----

_trace ==
    LET SimpleQCReviewAgent_TETrace == INSTANCE SimpleQCReviewAgent_TETrace
    IN SimpleQCReviewAgent_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        qcQueue = (<<>>)
        /\
        qcRejected = ({})
        /\
        qcApproved = ({1, 2, 3})
    )
----

_init ==
    /\ qcRejected = _TETrace[1].qcRejected
    /\ qcApproved = _TETrace[1].qcApproved
    /\ qcQueue = _TETrace[1].qcQueue
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ qcRejected  = _TETrace[i].qcRejected
        /\ qcRejected' = _TETrace[j].qcRejected
        /\ qcApproved  = _TETrace[i].qcApproved
        /\ qcApproved' = _TETrace[j].qcApproved
        /\ qcQueue  = _TETrace[i].qcQueue
        /\ qcQueue' = _TETrace[j].qcQueue

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("SimpleQCReviewAgent_TTrace_1752266508.json", _TETrace)

=============================================================================

 Note that you can extract this module `SimpleQCReviewAgent_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `SimpleQCReviewAgent_TEExpression.tla` file takes precedence 
  over the module `SimpleQCReviewAgent_TEExpression` below).

---- MODULE SimpleQCReviewAgent_TEExpression ----
EXTENDS SimpleQCReviewAgent, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `SimpleQCReviewAgent` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        qcRejected |-> qcRejected
        ,qcApproved |-> qcApproved
        ,qcQueue |-> qcQueue
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_qcRejectedUnchanged |-> qcRejected = qcRejected'
        
        \* Format the `qcRejected` variable as Json value.
        \* ,_qcRejectedJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(qcRejected)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_qcRejectedModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].qcRejected # _TETrace[s-1].qcRejected
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE SimpleQCReviewAgent_TETrace ----
\*EXTENDS SimpleQCReviewAgent, IOUtils, TLC
\*
\*trace == IODeserialize("SimpleQCReviewAgent_TTrace_1752266508.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE SimpleQCReviewAgent_TETrace ----
EXTENDS SimpleQCReviewAgent, TLC

trace == 
    <<
    ([qcQueue |-> <<>>,qcRejected |-> {},qcApproved |-> {}]),
    ([qcQueue |-> <<1>>,qcRejected |-> {},qcApproved |-> {}]),
    ([qcQueue |-> <<1, 3>>,qcRejected |-> {},qcApproved |-> {}]),
    ([qcQueue |-> <<1, 3, 1>>,qcRejected |-> {},qcApproved |-> {}]),
    ([qcQueue |-> <<1, 3, 1>>,qcRejected |-> {},qcApproved |-> {2}]),
    ([qcQueue |-> <<1, 1>>,qcRejected |-> {},qcApproved |-> {2, 3}]),
    ([qcQueue |-> <<>>,qcRejected |-> {},qcApproved |-> {1, 2, 3}])
    >>
----


=============================================================================

---- CONFIG SimpleQCReviewAgent_TTrace_1752266508 ----
CONSTANTS
    MaxSamples = 3
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
\* Generated on Fri Jul 11 17:41:48 BRT 2025