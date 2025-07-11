---- MODULE SimpleSchedulingAgent_TTrace_1752203452 ----
EXTENDS Sequences, TLCExt, SimpleSchedulingAgent, Toolbox, Naturals, TLC

_expression ==
    LET SimpleSchedulingAgent_TEExpression == INSTANCE SimpleSchedulingAgent_TEExpression
    IN SimpleSchedulingAgent_TEExpression!expression
----

_trace ==
    LET SimpleSchedulingAgent_TETrace == INSTANCE SimpleSchedulingAgent_TETrace
    IN SimpleSchedulingAgent_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        samplePriorities = (<<"URGENT", "URGENT", "STAT">>)
        /\
        schedulingFailures = ({3})
        /\
        sampleTests = (<<{"CBC"}, {"CBC"}, {"CBC", "BMP"}>>)
        /\
        resourcesInUse = (0)
        /\
        schedulingQueue = (<<1, 2, 3>>)
        /\
        schedulingDecisions = (<<[sampleID |-> 1, success |-> TRUE], [sampleID |-> 3, success |-> FALSE]>>)
        /\
        scheduledSamples = ({})
    )
----

_init ==
    /\ schedulingQueue = _TETrace[1].schedulingQueue
    /\ samplePriorities = _TETrace[1].samplePriorities
    /\ schedulingFailures = _TETrace[1].schedulingFailures
    /\ resourcesInUse = _TETrace[1].resourcesInUse
    /\ scheduledSamples = _TETrace[1].scheduledSamples
    /\ sampleTests = _TETrace[1].sampleTests
    /\ schedulingDecisions = _TETrace[1].schedulingDecisions
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ schedulingQueue  = _TETrace[i].schedulingQueue
        /\ schedulingQueue' = _TETrace[j].schedulingQueue
        /\ samplePriorities  = _TETrace[i].samplePriorities
        /\ samplePriorities' = _TETrace[j].samplePriorities
        /\ schedulingFailures  = _TETrace[i].schedulingFailures
        /\ schedulingFailures' = _TETrace[j].schedulingFailures
        /\ resourcesInUse  = _TETrace[i].resourcesInUse
        /\ resourcesInUse' = _TETrace[j].resourcesInUse
        /\ scheduledSamples  = _TETrace[i].scheduledSamples
        /\ scheduledSamples' = _TETrace[j].scheduledSamples
        /\ sampleTests  = _TETrace[i].sampleTests
        /\ sampleTests' = _TETrace[j].sampleTests
        /\ schedulingDecisions  = _TETrace[i].schedulingDecisions
        /\ schedulingDecisions' = _TETrace[j].schedulingDecisions

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("SimpleSchedulingAgent_TTrace_1752203452.json", _TETrace)

=============================================================================

 Note that you can extract this module `SimpleSchedulingAgent_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `SimpleSchedulingAgent_TEExpression.tla` file takes precedence 
  over the module `SimpleSchedulingAgent_TEExpression` below).

---- MODULE SimpleSchedulingAgent_TEExpression ----
EXTENDS Sequences, TLCExt, SimpleSchedulingAgent, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `SimpleSchedulingAgent` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        schedulingQueue |-> schedulingQueue
        ,samplePriorities |-> samplePriorities
        ,schedulingFailures |-> schedulingFailures
        ,resourcesInUse |-> resourcesInUse
        ,scheduledSamples |-> scheduledSamples
        ,sampleTests |-> sampleTests
        ,schedulingDecisions |-> schedulingDecisions
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_schedulingQueueUnchanged |-> schedulingQueue = schedulingQueue'
        
        \* Format the `schedulingQueue` variable as Json value.
        \* ,_schedulingQueueJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(schedulingQueue)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_schedulingQueueModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].schedulingQueue # _TETrace[s-1].schedulingQueue
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE SimpleSchedulingAgent_TETrace ----
\*EXTENDS IOUtils, SimpleSchedulingAgent, TLC
\*
\*trace == IODeserialize("SimpleSchedulingAgent_TTrace_1752203452.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE SimpleSchedulingAgent_TETrace ----
EXTENDS SimpleSchedulingAgent, TLC

trace == 
    <<
    ([samplePriorities |-> <<>>,schedulingFailures |-> {},sampleTests |-> <<>>,resourcesInUse |-> 0,schedulingQueue |-> <<>>,schedulingDecisions |-> <<>>,scheduledSamples |-> {}]),
    ([samplePriorities |-> <<"URGENT">>,schedulingFailures |-> {},sampleTests |-> <<{"CBC"}>>,resourcesInUse |-> 0,schedulingQueue |-> <<1>>,schedulingDecisions |-> <<>>,scheduledSamples |-> {}]),
    ([samplePriorities |-> <<"URGENT", "URGENT">>,schedulingFailures |-> {},sampleTests |-> <<{"CBC"}, {"CBC"}>>,resourcesInUse |-> 0,schedulingQueue |-> <<1, 2>>,schedulingDecisions |-> <<>>,scheduledSamples |-> {}]),
    ([samplePriorities |-> <<"URGENT", "URGENT">>,schedulingFailures |-> {},sampleTests |-> <<{"CBC"}, {"CBC"}>>,resourcesInUse |-> 1,schedulingQueue |-> <<1, 2>>,schedulingDecisions |-> <<[sampleID |-> 1, success |-> TRUE]>>,scheduledSamples |-> {1}]),
    ([samplePriorities |-> <<"URGENT", "URGENT", "STAT">>,schedulingFailures |-> {},sampleTests |-> <<{"CBC"}, {"CBC"}, {"CBC", "BMP"}>>,resourcesInUse |-> 1,schedulingQueue |-> <<1, 2, 3>>,schedulingDecisions |-> <<[sampleID |-> 1, success |-> TRUE]>>,scheduledSamples |-> {1}]),
    ([samplePriorities |-> <<"URGENT", "URGENT", "STAT">>,schedulingFailures |-> {3},sampleTests |-> <<{"CBC"}, {"CBC"}, {"CBC", "BMP"}>>,resourcesInUse |-> 1,schedulingQueue |-> <<1, 2, 3>>,schedulingDecisions |-> <<[sampleID |-> 1, success |-> TRUE], [sampleID |-> 3, success |-> FALSE]>>,scheduledSamples |-> {1}]),
    ([samplePriorities |-> <<"URGENT", "URGENT", "STAT">>,schedulingFailures |-> {3},sampleTests |-> <<{"CBC"}, {"CBC"}, {"CBC", "BMP"}>>,resourcesInUse |-> 0,schedulingQueue |-> <<1, 2, 3>>,schedulingDecisions |-> <<[sampleID |-> 1, success |-> TRUE], [sampleID |-> 3, success |-> FALSE]>>,scheduledSamples |-> {}])
    >>
----


=============================================================================

---- CONFIG SimpleSchedulingAgent_TTrace_1752203452 ----
CONSTANTS
    MaxSamples = 3
    MaxConcurrentTests = 2
    TestTypes = { "CBC" , "BMP" }
    Priorities = { "STAT" , "URGENT" , "ROUTINE" }
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
\* Generated on Fri Jul 11 00:10:55 BRT 2025