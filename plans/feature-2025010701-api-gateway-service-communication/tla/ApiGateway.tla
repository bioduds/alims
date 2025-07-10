---- MODULE ApiGateway ----
(*
API Gateway Service Communication Specification
Formal model of service routing, circuit breakers, and load balancing
for the ALIMS system API Gateway.

This specification models:
- Service health monitoring and state management
- Circuit breaker patterns for resilience
- Load balancing across healthy services
- Request routing with failure handling
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Services,          \* Set of backend service identifiers
    MaxRequests,       \* Maximum concurrent requests to model
    CircuitThreshold,  \* Failure count to trip circuit breaker
    MaxServiceLoad     \* Maximum load per service

VARIABLES
    services,          \* Function: service_id -> service_state
    circuit_breakers,  \* Function: service_id -> circuit_state  
    request_queue,     \* Sequence of pending requests
    active_requests,   \* Set of requests being processed
    service_loads,     \* Function: service_id -> current_load
    failure_counts,    \* Function: service_id -> consecutive_failures
    history           \* History of all operations for verification

\* Service health states
ServiceStates == {"HEALTHY", "DEGRADED", "FAILED", "UNKNOWN"}

\* Circuit breaker states
CircuitStates == {"CLOSED", "OPEN", "HALF_OPEN"}

\* Request states
RequestStates == {"PENDING", "ROUTED", "COMPLETED", "FAILED"}

\* Type definitions for requests
RequestType == [
    id: Nat,
    target_service: Services,
    state: RequestStates,
    retry_count: Nat
]

\* Variables type invariant
TypeInvariant ==
    /\ services \in [Services -> ServiceStates]
    /\ circuit_breakers \in [Services -> CircuitStates]
    /\ request_queue \in Seq(RequestType)
    /\ active_requests \subseteq RequestType
    /\ service_loads \in [Services -> 0..MaxServiceLoad]
    /\ failure_counts \in [Services -> Nat]
    /\ history \in Seq([action: STRING, service: Services, request: RequestType])

----

\* Initial state specification
Init ==
    /\ services = [s \in Services |-> "UNKNOWN"]
    /\ circuit_breakers = [s \in Services |-> "CLOSED"]
    /\ request_queue = <<>>
    /\ active_requests = {}
    /\ service_loads = [s \in Services |-> 0]
    /\ failure_counts = [s \in Services |-> 0]
    /\ history = <<>>

----

\* Helper predicates

\* Check if a service is available for routing
ServiceAvailable(service) ==
    /\ services[service] \in {"HEALTHY", "DEGRADED"}
    /\ circuit_breakers[service] \in {"CLOSED", "HALF_OPEN"}
    /\ service_loads[service] < MaxServiceLoad

\* Get healthy services for load balancing
HealthyServices ==
    {s \in Services : ServiceAvailable(s)}

\* Check if system can accept more requests
CanAcceptRequest ==
    Len(request_queue) + Cardinality(active_requests) < MaxRequests

\* Check if a specific target service is available for routing
TargetServiceAvailable(target) ==
    ServiceAvailable(target)

----

\* Action: Receive new request from client
ReceiveRequest ==
    /\ CanAcceptRequest
    /\ \E target \in Services :
        LET new_request == [
            id |-> Len(request_queue) + Cardinality(active_requests) + 1,
            target_service |-> target,
            state |-> "PENDING", 
            retry_count |-> 0
        ] IN
        /\ request_queue' = Append(request_queue, new_request)
        /\ history' = Append(history, [action |-> "RECEIVE_REQUEST", service |-> target, request |-> new_request])
        /\ UNCHANGED <<services, circuit_breakers, active_requests, service_loads, failure_counts>>

\* Action: Route request to a healthy service
RouteRequest ==
    /\ request_queue /= <<>>
    /\ LET request == Head(request_queue)
           target_service == request.target_service
       IN
        /\ TargetServiceAvailable(target_service)
        /\ request_queue' = Tail(request_queue)
        /\ active_requests' = active_requests \cup {[request EXCEPT !.state = "ROUTED"]}
        /\ service_loads' = [service_loads EXCEPT ![target_service] = @ + 1]
        /\ history' = Append(history, [action |-> "ROUTE_REQUEST", service |-> target_service, request |-> request])
        /\ UNCHANGED <<services, circuit_breakers, failure_counts>>

\* Action: Complete request successfully
CompleteRequest ==
    /\ active_requests /= {}
    /\ \E request \in active_requests :
        /\ request.state = "ROUTED"
        /\ LET target == request.target_service IN
            /\ active_requests' = (active_requests \ {request}) \cup {[request EXCEPT !.state = "COMPLETED"]}
            /\ service_loads' = [service_loads EXCEPT ![target] = @ - 1]
            /\ failure_counts' = [failure_counts EXCEPT ![target] = 0]  \* Reset failure count on success
            /\ history' = Append(history, [action |-> "COMPLETE_REQUEST", service |-> target, request |-> request])
            /\ UNCHANGED <<services, circuit_breakers, request_queue>>

\* Action: Handle request failure
FailRequest ==
    /\ active_requests /= {}
    /\ \E request \in active_requests :
        /\ request.state = "ROUTED"
        /\ LET target == request.target_service IN
            /\ active_requests' = (active_requests \ {request}) \cup {[request EXCEPT !.state = "FAILED"]}
            /\ service_loads' = [service_loads EXCEPT ![target] = @ - 1]
            /\ failure_counts' = [failure_counts EXCEPT ![target] = @ + 1]
            /\ \* Trip circuit breaker if failure threshold exceeded
               circuit_breakers' = IF failure_counts'[target] >= CircuitThreshold
                                  THEN [circuit_breakers EXCEPT ![target] = "OPEN"]
                                  ELSE circuit_breakers
            /\ history' = Append(history, [action |-> "FAIL_REQUEST", service |-> target, request |-> request])
            /\ UNCHANGED <<services, request_queue>>

\* Action: Update service health status
UpdateServiceHealth ==
    /\ \E service \in Services, new_state \in ServiceStates :
        /\ services[service] /= new_state
        /\ services' = [services EXCEPT ![service] = new_state]
        /\ \* If service becomes healthy, reset failure count
           failure_counts' = IF new_state = "HEALTHY"
                            THEN [failure_counts EXCEPT ![service] = 0]
                            ELSE failure_counts
        /\ \* If service fails, open circuit breaker
           circuit_breakers' = IF new_state = "FAILED"
                              THEN [circuit_breakers EXCEPT ![service] = "OPEN"]
                              ELSE circuit_breakers
        /\ history' = Append(history, [action |-> "UPDATE_HEALTH", service |-> service, request |-> [id |-> 0, target_service |-> service, state |-> "PENDING", retry_count |-> 0]])
        /\ UNCHANGED <<request_queue, active_requests, service_loads>>

\* Action: Test service in half-open circuit state
TestServiceRecovery ==
    /\ \E service \in Services :
        /\ circuit_breakers[service] = "OPEN"
        /\ services[service] \in {"HEALTHY", "DEGRADED"}
        /\ circuit_breakers' = [circuit_breakers EXCEPT ![service] = "HALF_OPEN"]
        /\ history' = Append(history, [action |-> "TEST_RECOVERY", service |-> service, request |-> [id |-> 0, target_service |-> service, state |-> "PENDING", retry_count |-> 0]])
        /\ UNCHANGED <<services, request_queue, active_requests, service_loads, failure_counts>>

\* Action: Close circuit breaker after successful test
CloseCircuitBreaker ==
    /\ \E service \in Services :
        /\ circuit_breakers[service] = "HALF_OPEN"
        /\ services[service] = "HEALTHY"
        /\ failure_counts[service] = 0
        /\ circuit_breakers' = [circuit_breakers EXCEPT ![service] = "CLOSED"]
        /\ history' = Append(history, [action |-> "CLOSE_CIRCUIT", service |-> service, request |-> [id |-> 0, target_service |-> service, state |-> "PENDING", retry_count |-> 0]])
        /\ UNCHANGED <<services, request_queue, active_requests, service_loads, failure_counts>>

----

\* Next state relation: all possible actions
Next ==
    \/ ReceiveRequest
    \/ RouteRequest
    \/ CompleteRequest
    \/ FailRequest
    \/ UpdateServiceHealth
    \/ TestServiceRecovery
    \/ CloseCircuitBreaker

\* Complete specification
Spec == Init /\ [][Next]_<<services, circuit_breakers, request_queue, active_requests, service_loads, failure_counts, history>>

----

\* Safety Properties (Invariants)

\* The key safety property: don't route requests to unavailable services
\* Requests can be received for any service, but only routed to available ones
SafeRouting ==
    \* The RouteRequest action should only happen when target service is available
    \* We express this as: if we can route (queue not empty) and service is not available,
    \* then there should be no pending requests for that service that could be routed
    \A service \in Services :
        (~ServiceAvailable(service) /\ request_queue /= <<>>) =>
            \A i \in 1..Len(request_queue) :
                request_queue[i].target_service /= service

\* Circuit breakers prevent routing to failed services
CircuitBreakerConsistency ==
    \A service \in Services :
        (services[service] = "FAILED" \/ failure_counts[service] >= CircuitThreshold) 
        => circuit_breakers[service] \in {"OPEN", "HALF_OPEN"}

\* Load balancing fairness - no service overloaded while others idle
LoadBalancingFairness ==
    \A s1, s2 \in Services :
        (ServiceAvailable(s1) /\ ServiceAvailable(s2) /\ service_loads[s1] > 0)
        => service_loads[s2] <= service_loads[s1] + 1

\* Service discovery accuracy
ServiceDiscoveryAccuracy ==
    \A service \in Services :
        (circuit_breakers[service] = "CLOSED" /\ service_loads[service] > 0)
        => services[service] \in {"HEALTHY", "DEGRADED"}

\* System capacity limits
CapacityLimits ==
    /\ Len(request_queue) + Cardinality(active_requests) <= MaxRequests
    /\ \A service \in Services : service_loads[service] <= MaxServiceLoad

\* Combine all safety properties
SafetyProperties ==
    /\ TypeInvariant
    /\ SafeRouting
    /\ CircuitBreakerConsistency
    /\ LoadBalancingFairness
    /\ ServiceDiscoveryAccuracy
    /\ CapacityLimits

----

\* Liveness Properties (Temporal)

\* All pending requests eventually get processed (assuming healthy services exist)
RequestProgress ==
    [](\E service \in Services : ServiceAvailable(service))
    => [](request_queue /= <<>> => <>(request_queue = <<>>))

\* Failed services eventually get tested for recovery
CircuitBreakerRecovery ==
    \A service \in Services :
        [](circuit_breakers[service] = "OPEN" 
           => <>(circuit_breakers[service] = "HALF_OPEN"))

\* Services can recover from failure states
ServiceRecovery ==
    \A service \in Services :
        [](services[service] = "FAILED" 
           => <>(services[service] \in {"HEALTHY", "DEGRADED"}))

\* System maintains availability (at least one service available)
SystemAvailability ==
    <>[](\E service \in Services : ServiceAvailable(service))

----

\* State constraint to bound model checking
StateConstraint ==
    /\ Len(request_queue) + Cardinality(active_requests) <= MaxRequests
    /\ Len(history) <= 20

----

\* Properties to check
THEOREM SafetyTheorem == Spec => []SafetyProperties
THEOREM LivenessTheorem == Spec => RequestProgress /\ CircuitBreakerRecovery

====
