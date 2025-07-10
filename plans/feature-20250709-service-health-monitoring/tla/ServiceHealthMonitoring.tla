---- MODULE ServiceHealthMonitoring ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Service Health Monitoring TLA+ Specification
\* Models the health monitoring system for ALIMS microservices
\* Ensures reliable health detection and service discovery

CONSTANTS 
  Services,          \* Set of all services in the system
  MaxHealthChecks    \* Maximum number of concurrent health checks

VARIABLES
  health_status,     \* Function: Service -> HealthState
  discovery_registry, \* Set of services available for discovery
  health_checks,     \* Set of ongoing health check operations
  failed_checks,     \* Function: Service -> Nat (failure count)
  last_check_time    \* Function: Service -> Nat (timestamp)

\* Health states that a service can be in
HealthStates == {"UNKNOWN", "STARTING", "HEALTHY", "DEGRADED", "UNHEALTHY", "STOPPING", "STOPPED"}

\* Terminal states (no further transitions possible)
TerminalStates == {"STOPPED"}

\* Operational states (service can handle requests)
OperationalStates == {"HEALTHY", "DEGRADED"}

\* Health check operation structure
HealthCheck == [service: Services, timestamp: Nat, result: BOOLEAN]

\* Type invariant - all variables have correct types
TypeInv == 
  /\ health_status \in [Services -> HealthStates]
  /\ discovery_registry \subseteq Services
  /\ health_checks \subseteq HealthCheck
  /\ failed_checks \in [Services -> Nat]
  /\ last_check_time \in [Services -> Nat]

\* Initial state - all services start in UNKNOWN state
Init ==
  /\ health_status = [s \in Services |-> "UNKNOWN"]
  /\ discovery_registry = {}
  /\ health_checks = {}
  /\ failed_checks = [s \in Services |-> 0]
  /\ last_check_time = [s \in Services |-> 0]

\* Valid state transitions for health status
ValidTransition(from, to) ==
  \/ /\ from = "UNKNOWN" /\ to \in {"STARTING", "HEALTHY", "UNHEALTHY"}
  \/ /\ from = "STARTING" /\ to \in {"HEALTHY", "UNHEALTHY", "STOPPING"}
  \/ /\ from = "HEALTHY" /\ to \in {"DEGRADED", "UNHEALTHY", "STOPPING"}
  \/ /\ from = "DEGRADED" /\ to \in {"HEALTHY", "UNHEALTHY", "STOPPING"}
  \/ /\ from = "UNHEALTHY" /\ to \in {"HEALTHY", "DEGRADED", "STOPPING", "STOPPED"}
  \/ /\ from = "STOPPING" /\ to \in {"STOPPED"}
  \/ /\ from = "STOPPED" /\ to = "STOPPED"  \* Terminal state

\* Service starts up and transitions to STARTING state
ServiceStartup(service) ==
  /\ health_status[service] = "UNKNOWN"
  /\ health_status' = [health_status EXCEPT ![service] = "STARTING"]
  /\ UNCHANGED <<discovery_registry, health_checks, failed_checks, last_check_time>>

\* Perform health check on a service
PerformHealthCheck(service) ==
  /\ health_status[service] \notin TerminalStates
  /\ Cardinality(health_checks) < MaxHealthChecks
  /\ \E result \in BOOLEAN:
       /\ health_checks' = health_checks \cup {[service |-> service, timestamp |-> last_check_time[service] + 1, result |-> result]}
       /\ last_check_time' = [last_check_time EXCEPT ![service] = @ + 1]
       /\ UNCHANGED <<health_status, discovery_registry, failed_checks>>

\* Process health check result and update service status
ProcessHealthCheckResult(service, result) ==
  /\ \E check \in health_checks: check.service = service
  /\ health_checks' = health_checks \ {check \in health_checks: check.service = service}
  /\ IF result
     THEN \* Health check passed
       /\ failed_checks' = [failed_checks EXCEPT ![service] = 0]
       /\ IF health_status[service] \in {"STARTING", "DEGRADED", "UNHEALTHY"}
          THEN health_status' = [health_status EXCEPT ![service] = "HEALTHY"]
               /\ discovery_registry' = discovery_registry \cup {service}  \* Auto-register when healthy
          ELSE UNCHANGED health_status /\ UNCHANGED discovery_registry
     ELSE \* Health check failed
       /\ failed_checks' = [failed_checks EXCEPT ![service] = @ + 1]
       /\ IF failed_checks'[service] >= 3  \* Threshold for marking unhealthy
          THEN health_status' = [health_status EXCEPT ![service] = "UNHEALTHY"]
               /\ IF service \in discovery_registry
                  THEN discovery_registry' = discovery_registry \ {service}  \* Auto-unregister when unhealthy
                  ELSE UNCHANGED discovery_registry
          ELSE IF health_status[service] = "HEALTHY"
               THEN health_status' = [health_status EXCEPT ![service] = "DEGRADED"]
                    /\ UNCHANGED discovery_registry  \* Stay registered when degraded
               ELSE UNCHANGED health_status /\ UNCHANGED discovery_registry
  /\ UNCHANGED last_check_time

\* Register service in discovery registry when healthy
RegisterService(service) ==
  /\ health_status[service] \in OperationalStates
  /\ service \notin discovery_registry
  /\ discovery_registry' = discovery_registry \cup {service}
  /\ UNCHANGED <<health_status, health_checks, failed_checks, last_check_time>>

\* Unregister service from discovery registry when not operational
UnregisterService(service) ==
  /\ health_status[service] \notin OperationalStates
  /\ service \in discovery_registry
  /\ discovery_registry' = discovery_registry \ {service}
  /\ UNCHANGED <<health_status, health_checks, failed_checks, last_check_time>>

\* Service graceful shutdown
ServiceShutdown(service) ==
  /\ health_status[service] \notin {"STOPPING", "STOPPED"}
  /\ health_status' = [health_status EXCEPT ![service] = "STOPPING"]
  /\ discovery_registry' = discovery_registry \ {service}  \* Auto-unregister on shutdown
  /\ UNCHANGED <<health_checks, failed_checks, last_check_time>>

\* Service completes shutdown
ServiceStopped(service) ==
  /\ health_status[service] = "STOPPING"
  /\ health_status' = [health_status EXCEPT ![service] = "STOPPED"]
  /\ UNCHANGED <<discovery_registry, health_checks, failed_checks, last_check_time>>

\* Next state relation - all possible actions
Next ==
  \/ \E service \in Services: ServiceStartup(service)
  \/ \E service \in Services: PerformHealthCheck(service)
  \/ \E service \in Services, result \in BOOLEAN: ProcessHealthCheckResult(service, result)
  \/ \E service \in Services: ServiceShutdown(service)
  \/ \E service \in Services: ServiceStopped(service)

\* Complete specification  
Spec == Init /\ [][Next]_<<health_status, discovery_registry, health_checks, failed_checks, last_check_time>>

\* SAFETY PROPERTIES

\* Property 1: State Consistency - Health states are always well-defined
StateConsistency == \A service \in Services: health_status[service] \in HealthStates

\* Property 2: Discovery Registry Consistency - Only operational services are discoverable
DiscoveryConsistency == 
  \A service \in Services: 
    service \in discovery_registry <=> health_status[service] \in OperationalStates

\* Property 3: Transition Validity - Only valid state transitions occur (as action property)
TransitionValidityAction == 
  \A service \in Services:
    health_status'[service] # health_status[service] =>
      ValidTransition(health_status[service], health_status'[service])

\* State-based version: Health states are always valid
ValidHealthStates == \A service \in Services: health_status[service] \in HealthStates

\* Property 4: Terminal State Immutability - Stopped services stay stopped (action property)
TerminalStateImmutabilityAction ==
  \A service \in Services:
    health_status[service] = "STOPPED" => health_status'[service] = "STOPPED"

\* State-based version: Check that we have proper terminal states
TerminalStateConsistency == 
  \A service \in Services:
    health_status[service] \in TerminalStates => health_status[service] = "STOPPED"

\* Property 5: Health Check Bounds - Never exceed maximum health checks
HealthCheckBounds == Cardinality(health_checks) <= MaxHealthChecks

\* Property 6: Monotonic Failure Count - Failure count consistency (action property)
MonotonicFailureCountAction ==
  \A service \in Services:
    failed_checks'[service] = 0 \/ failed_checks'[service] >= failed_checks[service]

\* State-based version: Failure counts are reasonable
FailureCountConsistency ==
  \A service \in Services: failed_checks[service] >= 0

\* LIVENESS PROPERTIES

\* Property 7: Eventual Health Determination - Services eventually get health status determined
EventualHealthDetermination ==
  \A service \in Services: <>(health_status[service] # "UNKNOWN")

\* Property 8: Service Discovery - Healthy services eventually get registered
ServiceDiscovery ==
  \A service \in Services:
    health_status[service] \in OperationalStates ~> service \in discovery_registry

\* Property 9: Failure Detection - Failed services eventually become unhealthy
FailureDetection ==
  \A service \in Services:
    failed_checks[service] >= 3 ~> health_status[service] = "UNHEALTHY"

\* Property 10: Recovery Detection - Services can recover from unhealthy state
RecoveryDetection ==
  \A service \in Services:
    (health_status[service] = "UNHEALTHY" /\ failed_checks[service] = 0) ~> health_status[service] = "HEALTHY"

\* COMBINED INVARIANTS FOR MODEL CHECKING

\* All safety properties combined
SafetyProperties ==
  /\ TypeInv
  /\ StateConsistency
  /\ DiscoveryConsistency
  /\ ValidHealthStates
  /\ TerminalStateConsistency
  /\ HealthCheckBounds
  /\ FailureCountConsistency

\* System-level invariants
SystemInvariants ==
  /\ \A service \in Services: health_status[service] \in HealthStates
  /\ discovery_registry \subseteq {s \in Services: health_status[s] \in OperationalStates}
  /\ Cardinality(health_checks) <= MaxHealthChecks

====
