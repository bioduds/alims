---- MODULE ServiceHealthMonitoring_TTrace_1752108508 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, ServiceHealthMonitoring, ServiceHealthMonitoring_TEConstants

_expression ==
    LET ServiceHealthMonitoring_TEExpression == INSTANCE ServiceHealthMonitoring_TEExpression
    IN ServiceHealthMonitoring_TEExpression!expression
----

_trace ==
    LET ServiceHealthMonitoring_TETrace == INSTANCE ServiceHealthMonitoring_TETrace
    IN ServiceHealthMonitoring_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        discovery_registry = ({})
        /\
        last_check_time = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0))
        /\
        failed_checks = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0))
        /\
        health_checks = ({})
        /\
        health_status = ((s1 :> "STOPPED" @@ s2 :> "STOPPED" @@ s3 :> "STOPPED"))
    )
----

_init ==
    /\ health_status = _TETrace[1].health_status
    /\ failed_checks = _TETrace[1].failed_checks
    /\ discovery_registry = _TETrace[1].discovery_registry
    /\ last_check_time = _TETrace[1].last_check_time
    /\ health_checks = _TETrace[1].health_checks
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ health_status  = _TETrace[i].health_status
        /\ health_status' = _TETrace[j].health_status
        /\ failed_checks  = _TETrace[i].failed_checks
        /\ failed_checks' = _TETrace[j].failed_checks
        /\ discovery_registry  = _TETrace[i].discovery_registry
        /\ discovery_registry' = _TETrace[j].discovery_registry
        /\ last_check_time  = _TETrace[i].last_check_time
        /\ last_check_time' = _TETrace[j].last_check_time
        /\ health_checks  = _TETrace[i].health_checks
        /\ health_checks' = _TETrace[j].health_checks

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("ServiceHealthMonitoring_TTrace_1752108508.json", _TETrace)

=============================================================================

 Note that you can extract this module `ServiceHealthMonitoring_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `ServiceHealthMonitoring_TEExpression.tla` file takes precedence 
  over the module `ServiceHealthMonitoring_TEExpression` below).

---- MODULE ServiceHealthMonitoring_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, ServiceHealthMonitoring, ServiceHealthMonitoring_TEConstants

expression == 
    [
        \* To hide variables of the `ServiceHealthMonitoring` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        health_status |-> health_status
        ,failed_checks |-> failed_checks
        ,discovery_registry |-> discovery_registry
        ,last_check_time |-> last_check_time
        ,health_checks |-> health_checks
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_health_statusUnchanged |-> health_status = health_status'
        
        \* Format the `health_status` variable as Json value.
        \* ,_health_statusJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(health_status)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_health_statusModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].health_status # _TETrace[s-1].health_status
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE ServiceHealthMonitoring_TETrace ----
\*EXTENDS IOUtils, TLC, ServiceHealthMonitoring, ServiceHealthMonitoring_TEConstants
\*
\*trace == IODeserialize("ServiceHealthMonitoring_TTrace_1752108508.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE ServiceHealthMonitoring_TETrace ----
EXTENDS TLC, ServiceHealthMonitoring, ServiceHealthMonitoring_TEConstants

trace == 
    <<
    ([discovery_registry |-> {},last_check_time |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),failed_checks |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),health_checks |-> {},health_status |-> (s1 :> "UNKNOWN" @@ s2 :> "UNKNOWN" @@ s3 :> "UNKNOWN")]),
    ([discovery_registry |-> {},last_check_time |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),failed_checks |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),health_checks |-> {},health_status |-> (s1 :> "STOPPING" @@ s2 :> "UNKNOWN" @@ s3 :> "UNKNOWN")]),
    ([discovery_registry |-> {},last_check_time |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),failed_checks |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),health_checks |-> {},health_status |-> (s1 :> "STOPPING" @@ s2 :> "STOPPING" @@ s3 :> "UNKNOWN")]),
    ([discovery_registry |-> {},last_check_time |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),failed_checks |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),health_checks |-> {},health_status |-> (s1 :> "STOPPING" @@ s2 :> "STOPPING" @@ s3 :> "STOPPING")]),
    ([discovery_registry |-> {},last_check_time |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),failed_checks |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),health_checks |-> {},health_status |-> (s1 :> "STOPPED" @@ s2 :> "STOPPING" @@ s3 :> "STOPPING")]),
    ([discovery_registry |-> {},last_check_time |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),failed_checks |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),health_checks |-> {},health_status |-> (s1 :> "STOPPED" @@ s2 :> "STOPPED" @@ s3 :> "STOPPING")]),
    ([discovery_registry |-> {},last_check_time |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),failed_checks |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),health_checks |-> {},health_status |-> (s1 :> "STOPPED" @@ s2 :> "STOPPED" @@ s3 :> "STOPPED")])
    >>
----


=============================================================================

---- MODULE ServiceHealthMonitoring_TEConstants ----
EXTENDS ServiceHealthMonitoring

CONSTANTS s1, s2, s3

=============================================================================

---- CONFIG ServiceHealthMonitoring_TTrace_1752108508 ----
CONSTANTS
    Services = { s1 , s2 , s3 }
    MaxHealthChecks = 5
    s1 = s1
    s2 = s2
    s3 = s3

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
\* Generated on Wed Jul 09 21:48:29 BRT 2025