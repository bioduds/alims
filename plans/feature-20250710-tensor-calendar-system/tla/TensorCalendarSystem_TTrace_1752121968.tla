---- MODULE TensorCalendarSystem_TTrace_1752121968 ----
EXTENDS TensorCalendarSystem, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET TensorCalendarSystem_TEExpression == INSTANCE TensorCalendarSystem_TEExpression
    IN TensorCalendarSystem_TEExpression!expression
----

_trace ==
    LET TensorCalendarSystem_TETrace == INSTANCE TensorCalendarSystem_TETrace
    IN TensorCalendarSystem_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        systemMetrics = ([totalScheduled |-> 2, conflictCount |-> 0, utilizationRate |-> 30, averageLatency |-> 0])
        /\
        workflowTimelines = (<<{1, 4}, {}>>)
        /\
        lastUpdate = (3)
        /\
        activeConstraints = ({})
        /\
        tensorCalendar = ([tensor |-> (<<1, 1, 1, 1>> :> TRUE @@ <<1, 1, 1, 2>> :> FALSE @@ <<1, 1, 2, 1>> :> FALSE @@ <<1, 1, 2, 2>> :> FALSE @@ <<1, 1, 3, 1>> :> FALSE @@ <<1, 1, 3, 2>> :> FALSE @@ <<1, 1, 4, 1>> :> FALSE @@ <<1, 1, 4, 2>> :> FALSE @@ <<1, 2, 1, 1>> :> FALSE @@ <<1, 2, 1, 2>> :> FALSE @@ <<1, 2, 2, 1>> :> FALSE @@ <<1, 2, 2, 2>> :> FALSE @@ <<1, 2, 3, 1>> :> FALSE @@ <<1, 2, 3, 2>> :> FALSE @@ <<1, 2, 4, 1>> :> TRUE @@ <<1, 2, 4, 2>> :> FALSE @@ <<2, 1, 1, 1>> :> FALSE @@ <<2, 1, 1, 2>> :> FALSE @@ <<2, 1, 2, 1>> :> FALSE @@ <<2, 1, 2, 2>> :> FALSE @@ <<2, 1, 3, 1>> :> FALSE @@ <<2, 1, 3, 2>> :> FALSE @@ <<2, 1, 4, 1>> :> FALSE @@ <<2, 1, 4, 2>> :> FALSE @@ <<2, 2, 1, 1>> :> FALSE @@ <<2, 2, 1, 2>> :> FALSE @@ <<2, 2, 2, 1>> :> FALSE @@ <<2, 2, 2, 2>> :> FALSE @@ <<2, 2, 3, 1>> :> FALSE @@ <<2, 2, 3, 2>> :> FALSE @@ <<2, 2, 4, 1>> :> FALSE @@ <<2, 2, 4, 2>> :> FALSE @@ <<3, 1, 1, 1>> :> FALSE @@ <<3, 1, 1, 2>> :> FALSE @@ <<3, 1, 2, 1>> :> FALSE @@ <<3, 1, 2, 2>> :> FALSE @@ <<3, 1, 3, 1>> :> FALSE @@ <<3, 1, 3, 2>> :> FALSE @@ <<3, 1, 4, 1>> :> FALSE @@ <<3, 1, 4, 2>> :> FALSE @@ <<3, 2, 1, 1>> :> FALSE @@ <<3, 2, 1, 2>> :> FALSE @@ <<3, 2, 2, 1>> :> FALSE @@ <<3, 2, 2, 2>> :> FALSE @@ <<3, 2, 3, 1>> :> FALSE @@ <<3, 2, 3, 2>> :> FALSE @@ <<3, 2, 4, 1>> :> FALSE @@ <<3, 2, 4, 2>> :> FALSE), conflicts |-> {}, capacity |-> <<1, 1>>, deadlines |-> <<3, 4, 4>>, dependencies |-> <<{}, {}>>])
        /\
        sampleSchedules = (<<{1, 4}, {}, {}>>)
        /\
        resourceBookings = (<<{1}, {4}>>)
    )
----

_init ==
    /\ activeConstraints = _TETrace[1].activeConstraints
    /\ resourceBookings = _TETrace[1].resourceBookings
    /\ sampleSchedules = _TETrace[1].sampleSchedules
    /\ systemMetrics = _TETrace[1].systemMetrics
    /\ workflowTimelines = _TETrace[1].workflowTimelines
    /\ tensorCalendar = _TETrace[1].tensorCalendar
    /\ lastUpdate = _TETrace[1].lastUpdate
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ activeConstraints  = _TETrace[i].activeConstraints
        /\ activeConstraints' = _TETrace[j].activeConstraints
        /\ resourceBookings  = _TETrace[i].resourceBookings
        /\ resourceBookings' = _TETrace[j].resourceBookings
        /\ sampleSchedules  = _TETrace[i].sampleSchedules
        /\ sampleSchedules' = _TETrace[j].sampleSchedules
        /\ systemMetrics  = _TETrace[i].systemMetrics
        /\ systemMetrics' = _TETrace[j].systemMetrics
        /\ workflowTimelines  = _TETrace[i].workflowTimelines
        /\ workflowTimelines' = _TETrace[j].workflowTimelines
        /\ tensorCalendar  = _TETrace[i].tensorCalendar
        /\ tensorCalendar' = _TETrace[j].tensorCalendar
        /\ lastUpdate  = _TETrace[i].lastUpdate
        /\ lastUpdate' = _TETrace[j].lastUpdate

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("TensorCalendarSystem_TTrace_1752121968.json", _TETrace)

=============================================================================

 Note that you can extract this module `TensorCalendarSystem_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `TensorCalendarSystem_TEExpression.tla` file takes precedence 
  over the module `TensorCalendarSystem_TEExpression` below).

---- MODULE TensorCalendarSystem_TEExpression ----
EXTENDS TensorCalendarSystem, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `TensorCalendarSystem` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        activeConstraints |-> activeConstraints
        ,resourceBookings |-> resourceBookings
        ,sampleSchedules |-> sampleSchedules
        ,systemMetrics |-> systemMetrics
        ,workflowTimelines |-> workflowTimelines
        ,tensorCalendar |-> tensorCalendar
        ,lastUpdate |-> lastUpdate
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_activeConstraintsUnchanged |-> activeConstraints = activeConstraints'
        
        \* Format the `activeConstraints` variable as Json value.
        \* ,_activeConstraintsJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(activeConstraints)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_activeConstraintsModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].activeConstraints # _TETrace[s-1].activeConstraints
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE TensorCalendarSystem_TETrace ----
\*EXTENDS TensorCalendarSystem, IOUtils, TLC
\*
\*trace == IODeserialize("TensorCalendarSystem_TTrace_1752121968.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE TensorCalendarSystem_TETrace ----
EXTENDS TensorCalendarSystem, TLC

trace == 
    <<
    ([systemMetrics |-> [totalScheduled |-> 0, conflictCount |-> 0, utilizationRate |-> 0, averageLatency |-> 0],workflowTimelines |-> <<{}, {}>>,lastUpdate |-> 0,activeConstraints |-> {},tensorCalendar |-> [tensor |-> (<<1, 1, 1, 1>> :> FALSE @@ <<1, 1, 1, 2>> :> FALSE @@ <<1, 1, 2, 1>> :> FALSE @@ <<1, 1, 2, 2>> :> FALSE @@ <<1, 1, 3, 1>> :> FALSE @@ <<1, 1, 3, 2>> :> FALSE @@ <<1, 1, 4, 1>> :> FALSE @@ <<1, 1, 4, 2>> :> FALSE @@ <<1, 2, 1, 1>> :> FALSE @@ <<1, 2, 1, 2>> :> FALSE @@ <<1, 2, 2, 1>> :> FALSE @@ <<1, 2, 2, 2>> :> FALSE @@ <<1, 2, 3, 1>> :> FALSE @@ <<1, 2, 3, 2>> :> FALSE @@ <<1, 2, 4, 1>> :> FALSE @@ <<1, 2, 4, 2>> :> FALSE @@ <<2, 1, 1, 1>> :> FALSE @@ <<2, 1, 1, 2>> :> FALSE @@ <<2, 1, 2, 1>> :> FALSE @@ <<2, 1, 2, 2>> :> FALSE @@ <<2, 1, 3, 1>> :> FALSE @@ <<2, 1, 3, 2>> :> FALSE @@ <<2, 1, 4, 1>> :> FALSE @@ <<2, 1, 4, 2>> :> FALSE @@ <<2, 2, 1, 1>> :> FALSE @@ <<2, 2, 1, 2>> :> FALSE @@ <<2, 2, 2, 1>> :> FALSE @@ <<2, 2, 2, 2>> :> FALSE @@ <<2, 2, 3, 1>> :> FALSE @@ <<2, 2, 3, 2>> :> FALSE @@ <<2, 2, 4, 1>> :> FALSE @@ <<2, 2, 4, 2>> :> FALSE @@ <<3, 1, 1, 1>> :> FALSE @@ <<3, 1, 1, 2>> :> FALSE @@ <<3, 1, 2, 1>> :> FALSE @@ <<3, 1, 2, 2>> :> FALSE @@ <<3, 1, 3, 1>> :> FALSE @@ <<3, 1, 3, 2>> :> FALSE @@ <<3, 1, 4, 1>> :> FALSE @@ <<3, 1, 4, 2>> :> FALSE @@ <<3, 2, 1, 1>> :> FALSE @@ <<3, 2, 1, 2>> :> FALSE @@ <<3, 2, 2, 1>> :> FALSE @@ <<3, 2, 2, 2>> :> FALSE @@ <<3, 2, 3, 1>> :> FALSE @@ <<3, 2, 3, 2>> :> FALSE @@ <<3, 2, 4, 1>> :> FALSE @@ <<3, 2, 4, 2>> :> FALSE), conflicts |-> {}, capacity |-> <<1, 1>>, deadlines |-> <<4, 4, 4>>, dependencies |-> <<{}, {}>>],sampleSchedules |-> <<{}, {}, {}>>,resourceBookings |-> <<{}, {}>>]),
    ([systemMetrics |-> [totalScheduled |-> 1, conflictCount |-> 0, utilizationRate |-> 5, averageLatency |-> 0],workflowTimelines |-> <<{1}, {}>>,lastUpdate |-> 1,activeConstraints |-> {},tensorCalendar |-> [tensor |-> (<<1, 1, 1, 1>> :> TRUE @@ <<1, 1, 1, 2>> :> FALSE @@ <<1, 1, 2, 1>> :> FALSE @@ <<1, 1, 2, 2>> :> FALSE @@ <<1, 1, 3, 1>> :> FALSE @@ <<1, 1, 3, 2>> :> FALSE @@ <<1, 1, 4, 1>> :> FALSE @@ <<1, 1, 4, 2>> :> FALSE @@ <<1, 2, 1, 1>> :> FALSE @@ <<1, 2, 1, 2>> :> FALSE @@ <<1, 2, 2, 1>> :> FALSE @@ <<1, 2, 2, 2>> :> FALSE @@ <<1, 2, 3, 1>> :> FALSE @@ <<1, 2, 3, 2>> :> FALSE @@ <<1, 2, 4, 1>> :> FALSE @@ <<1, 2, 4, 2>> :> FALSE @@ <<2, 1, 1, 1>> :> FALSE @@ <<2, 1, 1, 2>> :> FALSE @@ <<2, 1, 2, 1>> :> FALSE @@ <<2, 1, 2, 2>> :> FALSE @@ <<2, 1, 3, 1>> :> FALSE @@ <<2, 1, 3, 2>> :> FALSE @@ <<2, 1, 4, 1>> :> FALSE @@ <<2, 1, 4, 2>> :> FALSE @@ <<2, 2, 1, 1>> :> FALSE @@ <<2, 2, 1, 2>> :> FALSE @@ <<2, 2, 2, 1>> :> FALSE @@ <<2, 2, 2, 2>> :> FALSE @@ <<2, 2, 3, 1>> :> FALSE @@ <<2, 2, 3, 2>> :> FALSE @@ <<2, 2, 4, 1>> :> FALSE @@ <<2, 2, 4, 2>> :> FALSE @@ <<3, 1, 1, 1>> :> FALSE @@ <<3, 1, 1, 2>> :> FALSE @@ <<3, 1, 2, 1>> :> FALSE @@ <<3, 1, 2, 2>> :> FALSE @@ <<3, 1, 3, 1>> :> FALSE @@ <<3, 1, 3, 2>> :> FALSE @@ <<3, 1, 4, 1>> :> FALSE @@ <<3, 1, 4, 2>> :> FALSE @@ <<3, 2, 1, 1>> :> FALSE @@ <<3, 2, 1, 2>> :> FALSE @@ <<3, 2, 2, 1>> :> FALSE @@ <<3, 2, 2, 2>> :> FALSE @@ <<3, 2, 3, 1>> :> FALSE @@ <<3, 2, 3, 2>> :> FALSE @@ <<3, 2, 4, 1>> :> FALSE @@ <<3, 2, 4, 2>> :> FALSE), conflicts |-> {}, capacity |-> <<1, 1>>, deadlines |-> <<4, 4, 4>>, dependencies |-> <<{}, {}>>],sampleSchedules |-> <<{1}, {}, {}>>,resourceBookings |-> <<{1}, {}>>]),
    ([systemMetrics |-> [totalScheduled |-> 2, conflictCount |-> 0, utilizationRate |-> 30, averageLatency |-> 0],workflowTimelines |-> <<{1, 4}, {}>>,lastUpdate |-> 2,activeConstraints |-> {},tensorCalendar |-> [tensor |-> (<<1, 1, 1, 1>> :> TRUE @@ <<1, 1, 1, 2>> :> FALSE @@ <<1, 1, 2, 1>> :> FALSE @@ <<1, 1, 2, 2>> :> FALSE @@ <<1, 1, 3, 1>> :> FALSE @@ <<1, 1, 3, 2>> :> FALSE @@ <<1, 1, 4, 1>> :> FALSE @@ <<1, 1, 4, 2>> :> FALSE @@ <<1, 2, 1, 1>> :> FALSE @@ <<1, 2, 1, 2>> :> FALSE @@ <<1, 2, 2, 1>> :> FALSE @@ <<1, 2, 2, 2>> :> FALSE @@ <<1, 2, 3, 1>> :> FALSE @@ <<1, 2, 3, 2>> :> FALSE @@ <<1, 2, 4, 1>> :> TRUE @@ <<1, 2, 4, 2>> :> FALSE @@ <<2, 1, 1, 1>> :> FALSE @@ <<2, 1, 1, 2>> :> FALSE @@ <<2, 1, 2, 1>> :> FALSE @@ <<2, 1, 2, 2>> :> FALSE @@ <<2, 1, 3, 1>> :> FALSE @@ <<2, 1, 3, 2>> :> FALSE @@ <<2, 1, 4, 1>> :> FALSE @@ <<2, 1, 4, 2>> :> FALSE @@ <<2, 2, 1, 1>> :> FALSE @@ <<2, 2, 1, 2>> :> FALSE @@ <<2, 2, 2, 1>> :> FALSE @@ <<2, 2, 2, 2>> :> FALSE @@ <<2, 2, 3, 1>> :> FALSE @@ <<2, 2, 3, 2>> :> FALSE @@ <<2, 2, 4, 1>> :> FALSE @@ <<2, 2, 4, 2>> :> FALSE @@ <<3, 1, 1, 1>> :> FALSE @@ <<3, 1, 1, 2>> :> FALSE @@ <<3, 1, 2, 1>> :> FALSE @@ <<3, 1, 2, 2>> :> FALSE @@ <<3, 1, 3, 1>> :> FALSE @@ <<3, 1, 3, 2>> :> FALSE @@ <<3, 1, 4, 1>> :> FALSE @@ <<3, 1, 4, 2>> :> FALSE @@ <<3, 2, 1, 1>> :> FALSE @@ <<3, 2, 1, 2>> :> FALSE @@ <<3, 2, 2, 1>> :> FALSE @@ <<3, 2, 2, 2>> :> FALSE @@ <<3, 2, 3, 1>> :> FALSE @@ <<3, 2, 3, 2>> :> FALSE @@ <<3, 2, 4, 1>> :> FALSE @@ <<3, 2, 4, 2>> :> FALSE), conflicts |-> {}, capacity |-> <<1, 1>>, deadlines |-> <<4, 4, 4>>, dependencies |-> <<{}, {}>>],sampleSchedules |-> <<{1, 4}, {}, {}>>,resourceBookings |-> <<{1}, {4}>>]),
    ([systemMetrics |-> [totalScheduled |-> 2, conflictCount |-> 0, utilizationRate |-> 30, averageLatency |-> 0],workflowTimelines |-> <<{1, 4}, {}>>,lastUpdate |-> 3,activeConstraints |-> {},tensorCalendar |-> [tensor |-> (<<1, 1, 1, 1>> :> TRUE @@ <<1, 1, 1, 2>> :> FALSE @@ <<1, 1, 2, 1>> :> FALSE @@ <<1, 1, 2, 2>> :> FALSE @@ <<1, 1, 3, 1>> :> FALSE @@ <<1, 1, 3, 2>> :> FALSE @@ <<1, 1, 4, 1>> :> FALSE @@ <<1, 1, 4, 2>> :> FALSE @@ <<1, 2, 1, 1>> :> FALSE @@ <<1, 2, 1, 2>> :> FALSE @@ <<1, 2, 2, 1>> :> FALSE @@ <<1, 2, 2, 2>> :> FALSE @@ <<1, 2, 3, 1>> :> FALSE @@ <<1, 2, 3, 2>> :> FALSE @@ <<1, 2, 4, 1>> :> TRUE @@ <<1, 2, 4, 2>> :> FALSE @@ <<2, 1, 1, 1>> :> FALSE @@ <<2, 1, 1, 2>> :> FALSE @@ <<2, 1, 2, 1>> :> FALSE @@ <<2, 1, 2, 2>> :> FALSE @@ <<2, 1, 3, 1>> :> FALSE @@ <<2, 1, 3, 2>> :> FALSE @@ <<2, 1, 4, 1>> :> FALSE @@ <<2, 1, 4, 2>> :> FALSE @@ <<2, 2, 1, 1>> :> FALSE @@ <<2, 2, 1, 2>> :> FALSE @@ <<2, 2, 2, 1>> :> FALSE @@ <<2, 2, 2, 2>> :> FALSE @@ <<2, 2, 3, 1>> :> FALSE @@ <<2, 2, 3, 2>> :> FALSE @@ <<2, 2, 4, 1>> :> FALSE @@ <<2, 2, 4, 2>> :> FALSE @@ <<3, 1, 1, 1>> :> FALSE @@ <<3, 1, 1, 2>> :> FALSE @@ <<3, 1, 2, 1>> :> FALSE @@ <<3, 1, 2, 2>> :> FALSE @@ <<3, 1, 3, 1>> :> FALSE @@ <<3, 1, 3, 2>> :> FALSE @@ <<3, 1, 4, 1>> :> FALSE @@ <<3, 1, 4, 2>> :> FALSE @@ <<3, 2, 1, 1>> :> FALSE @@ <<3, 2, 1, 2>> :> FALSE @@ <<3, 2, 2, 1>> :> FALSE @@ <<3, 2, 2, 2>> :> FALSE @@ <<3, 2, 3, 1>> :> FALSE @@ <<3, 2, 3, 2>> :> FALSE @@ <<3, 2, 4, 1>> :> FALSE @@ <<3, 2, 4, 2>> :> FALSE), conflicts |-> {}, capacity |-> <<1, 1>>, deadlines |-> <<3, 4, 4>>, dependencies |-> <<{}, {}>>],sampleSchedules |-> <<{1, 4}, {}, {}>>,resourceBookings |-> <<{1}, {4}>>])
    >>
----


=============================================================================

---- CONFIG TensorCalendarSystem_TTrace_1752121968 ----
CONSTANTS
    MaxSamples = 3
    MaxResources = 2
    MaxTimeSlots = 4
    MaxWorkflows = 2
    MaxTensorSize = 20

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
\* Generated on Thu Jul 10 01:32:49 BRT 2025