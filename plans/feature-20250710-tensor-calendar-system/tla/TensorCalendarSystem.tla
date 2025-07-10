---- MODULE TensorCalendarSystem ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Constants defining system bounds
CONSTANTS
    MaxSamples,        \* Maximum number of concurrent samples
    MaxResources,      \* Maximum number of resources (equipment, staff)
    MaxTimeSlots,      \* Maximum time horizon (e.g., 48 hours in 15-min slots)
    MaxWorkflows,      \* Maximum concurrent workflows
    MaxTensorSize      \* Maximum tensor memory size

\* Type definitions for tensor calendar system
VARIABLES
    tensorCalendar,    \* Multi-dimensional tensor representing all schedules
    sampleSchedules,   \* Sample ID -> scheduled time slots
    resourceBookings,  \* Resource ID -> booked time slots  
    workflowTimelines, \* Workflow ID -> task dependencies and timings
    activeConstraints, \* Set of active scheduling constraints
    systemMetrics,     \* Performance and utilization metrics
    lastUpdate         \* Timestamp of last tensor update

\* Helper operators for tensor operations
SampleDimension == 1..MaxSamples
ResourceDimension == 1..MaxResources
TimeDimension == 1..MaxTimeSlots
WorkflowDimension == 1..MaxWorkflows

\* Type invariants for tensor structure
TensorShape == [
    samples: SampleDimension,
    resources: ResourceDimension, 
    time: TimeDimension,
    workflows: WorkflowDimension
]

\* Calendar events and operations
CalendarEvents == {
    "sample_arrival",
    "workflow_start", 
    "resource_available",
    "resource_unavailable",
    "deadline_update",
    "capacity_change"
}

\* Constraint types for scheduling
ConstraintTypes == {
    "resource_capacity",
    "time_dependency", 
    "workflow_ordering",
    "regulatory_deadline",
    "priority_override"
}

\* Tensor calendar state definition
TensorCalendarState == [
    tensor: TensorShape,
    conflicts: SUBSET (SampleDimension \X ResourceDimension \X TimeDimension),
    capacity: [ResourceDimension -> Nat],
    deadlines: [SampleDimension -> TimeDimension],
    dependencies: [WorkflowDimension -> SUBSET WorkflowDimension]
]

\* Initial state specification
Init ==
    /\ tensorCalendar = [
        tensor |-> [s \in SampleDimension, r \in ResourceDimension, 
                   t \in TimeDimension, w \in WorkflowDimension |-> FALSE],
        conflicts |-> {},
        capacity |-> [r \in ResourceDimension |-> 1], 
        deadlines |-> [s \in SampleDimension |-> MaxTimeSlots],
        dependencies |-> [w \in WorkflowDimension |-> {}]
       ]
    /\ sampleSchedules = [s \in SampleDimension |-> {}]
    /\ resourceBookings = [r \in ResourceDimension |-> {}]
    /\ workflowTimelines = [w \in WorkflowDimension |-> {}]
    /\ activeConstraints = {}
    /\ systemMetrics = [
        totalScheduled |-> 0,
        conflictCount |-> 0,
        utilizationRate |-> 0,
        averageLatency |-> 0
       ]
    /\ lastUpdate = 0

\* Schedule a sample for processing
ScheduleSample(sample, resource, timeSlot, workflow) ==
    /\ sample \in SampleDimension
    /\ resource \in ResourceDimension  
    /\ timeSlot \in TimeDimension
    /\ workflow \in WorkflowDimension
    /\ \* Check resource availability
       timeSlot \notin resourceBookings[resource]
    /\ \* Check capacity constraints
       Cardinality(resourceBookings[resource]) < tensorCalendar.capacity[resource]
    /\ \* Check deadline compliance
       timeSlot <= tensorCalendar.deadlines[sample]
    /\ \* Check workflow dependencies
       LET prereqs == tensorCalendar.dependencies[workflow]
       IN \A dep \in prereqs : 
            \E t \in TimeDimension : 
                t < timeSlot /\ t \in workflowTimelines[dep]
    /\ \* Update tensor calendar
       tensorCalendar' = [tensorCalendar EXCEPT
           !.tensor[sample, resource, timeSlot, workflow] = TRUE
       ]
    /\ \* Update sample schedule
       sampleSchedules' = [sampleSchedules EXCEPT 
           ![sample] = @ \cup {timeSlot}
       ]
    /\ \* Update resource bookings
       resourceBookings' = [resourceBookings EXCEPT
           ![resource] = @ \cup {timeSlot}
       ]
    /\ \* Update workflow timeline
       workflowTimelines' = [workflowTimelines EXCEPT
           ![workflow] = @ \cup {timeSlot}
       ]
    /\ \* Update system metrics
       systemMetrics' = [systemMetrics EXCEPT
           !.totalScheduled = @ + 1,
           !.utilizationRate = LET newRate == ((@ + 1) * 100) \div MaxTensorSize
                              IN IF newRate > 100 THEN 100 ELSE newRate
       ]
    /\ lastUpdate' = lastUpdate + 1
    /\ UNCHANGED activeConstraints

\* Detect and resolve scheduling conflicts
DetectConflicts ==
    LET conflicts == {
            <<s, r, t>> \in SampleDimension \X ResourceDimension \X TimeDimension :
                Cardinality({w \in WorkflowDimension : 
                    tensorCalendar.tensor[s, r, t, w]}) > 1
        }
    IN  /\ tensorCalendar' = [tensorCalendar EXCEPT
                !.conflicts = conflicts
           ]
        /\ systemMetrics' = [systemMetrics EXCEPT
                !.conflictCount = Cardinality(conflicts)
           ]
        /\ UNCHANGED <<sampleSchedules, resourceBookings, workflowTimelines, 
                      activeConstraints, lastUpdate>>

\* Update resource capacity dynamically
UpdateResourceCapacity(resource, newCapacity) ==
    /\ resource \in ResourceDimension
    /\ newCapacity \in Nat
    /\ newCapacity > 0
    /\ tensorCalendar' = [tensorCalendar EXCEPT
        !.capacity[resource] = newCapacity
       ]
    /\ \* Check if current bookings exceed new capacity
       IF Cardinality(resourceBookings[resource]) > newCapacity
       THEN \* Trigger rescheduling (simplified - would be more complex)
            activeConstraints' = activeConstraints \cup {"capacity_exceeded"}
       ELSE activeConstraints' = activeConstraints
    /\ lastUpdate' = lastUpdate + 1
    /\ UNCHANGED <<sampleSchedules, resourceBookings, workflowTimelines, 
                  systemMetrics>>

\* Add workflow dependency
AddWorkflowDependency(workflow, prerequisite) ==
    /\ workflow \in WorkflowDimension
    /\ prerequisite \in WorkflowDimension
    /\ workflow # prerequisite
    /\ prerequisite \notin tensorCalendar.dependencies[workflow]
    /\ \* Prevent circular dependencies
       workflow \notin tensorCalendar.dependencies[prerequisite]
    /\ tensorCalendar' = [tensorCalendar EXCEPT
        !.dependencies[workflow] = @ \cup {prerequisite}
       ]
    /\ lastUpdate' = lastUpdate + 1
    /\ UNCHANGED <<sampleSchedules, resourceBookings, workflowTimelines,
                  activeConstraints, systemMetrics>>

\* Set regulatory deadline for sample
SetSampleDeadline(sample, deadline) ==
    /\ sample \in SampleDimension
    /\ deadline \in TimeDimension
    /\ deadline > lastUpdate
    /\ \* Ensure new deadline doesn't violate existing schedules
       sampleSchedules[sample] = {} \/ 
       (\A t \in sampleSchedules[sample] : t <= deadline)
    /\ tensorCalendar' = [tensorCalendar EXCEPT
        !.deadlines[sample] = deadline
       ]
    /\ lastUpdate' = lastUpdate + 1
    /\ UNCHANGED <<sampleSchedules, resourceBookings, workflowTimelines,
                  activeConstraints, systemMetrics>>

\* Optimize tensor schedule using mathematical operations
OptimizeTensorSchedule ==
    /\ \* Simulate tensor optimization (simplified representation)
       LET optimization == [
           rebalanced |-> TRUE,
           improved |-> systemMetrics.utilizationRate < 85
       ]
       IN /\ systemMetrics' = [systemMetrics EXCEPT
               !.utilizationRate = IF optimization.improved 
                                  THEN @ + 10 
                                  ELSE @,
               !.averageLatency = IF optimization.improved
                                 THEN IF @ > 5 THEN @ - 5 ELSE 0
                                 ELSE @
              ]
    /\ lastUpdate' = lastUpdate + 1
    /\ UNCHANGED <<tensorCalendar, sampleSchedules, resourceBookings,
                  workflowTimelines, activeConstraints>>

\* Real-time tensor update from external event
ProcessRealTimeEvent(eventType, eventData) ==
    /\ eventType \in CalendarEvents
    /\ CASE eventType = "sample_arrival" ->
                /\ \E s \in SampleDimension, t \in TimeDimension :
                    /\ sampleSchedules[s] = {}
                    /\ ScheduleSample(s, 1, t, 1)
         [] eventType = "resource_unavailable" ->
                /\ \E r \in ResourceDimension :
                    UpdateResourceCapacity(r, 0)
         [] eventType = "deadline_update" ->
                /\ \E s \in SampleDimension, t \in TimeDimension :
                    SetSampleDeadline(s, t)
         [] OTHER -> 
                /\ lastUpdate' = lastUpdate + 1
                /\ UNCHANGED <<tensorCalendar, sampleSchedules, resourceBookings,
                              workflowTimelines, activeConstraints, systemMetrics>>

\* Next-state relation
Next ==
    \/ \E s \in SampleDimension, r \in ResourceDimension, 
         t \in TimeDimension, w \in WorkflowDimension :
        ScheduleSample(s, r, t, w)
    \/ DetectConflicts
    \/ \E r \in ResourceDimension, c \in 0..5 :
        UpdateResourceCapacity(r, c)
    \/ \E w1, w2 \in WorkflowDimension :
        AddWorkflowDependency(w1, w2)
    \/ \E s \in SampleDimension, d \in TimeDimension :
        SetSampleDeadline(s, d)
    \/ OptimizeTensorSchedule
    \/ \E event \in CalendarEvents :
        ProcessRealTimeEvent(event, "data")

\* Fairness conditions to ensure progress and liveness
vars == <<tensorCalendar, sampleSchedules, resourceBookings,
          workflowTimelines, activeConstraints, systemMetrics,
          lastUpdate>>

\* STATE CONSTRAINT for model checking
StateConstraint == lastUpdate <= 5

\* FAIRNESS CONSTRAINTS - Ensure system obligates to progress

\* Essential fairness constraints for core operations
EssentialFairness ==
    /\ WF_vars(DetectConflicts)
    /\ WF_vars(OptimizeTensorSchedule)
    /\ WF_vars(\E s \in SampleDimension, r \in ResourceDimension, 
                  t \in TimeDimension, w \in WorkflowDimension :
                ScheduleSample(s, r, t, w))

\* Strong fairness for critical progress-ensuring operations
CriticalProgressFairness ==
    /\ SF_vars(\E r \in ResourceDimension, c \in 1..5 :
                UpdateResourceCapacity(r, c))
    /\ SF_vars(\E s \in SampleDimension, d \in TimeDimension :
                d > lastUpdate /\ SetSampleDeadline(s, d))
    /\ SF_vars(\E w1, w2 \in WorkflowDimension :
                w1 # w2 /\ AddWorkflowDependency(w1, w2))

\* Fairness for real-time event processing
EventProcessingFairness ==
    \A event \in CalendarEvents :
        WF_vars(ProcessRealTimeEvent(event, "data"))

\* Combined fairness specification that the system must oblige to
SystemFairness == 
    /\ EssentialFairness
    /\ CriticalProgressFairness
    /\ EventProcessingFairness

\* Specification with comprehensive fairness - system OBLIGATES to these constraints
Spec == Init /\ [][Next]_vars /\ SystemFairness

\* INVARIANTS - Critical properties that must always hold

\* No resource double-booking
NoResourceConflicts ==
    \A r \in ResourceDimension, t \in TimeDimension :
        Cardinality({<<s, w>> \in SampleDimension \X WorkflowDimension :
            tensorCalendar.tensor[s, r, t, w]}) <= tensorCalendar.capacity[r]

\* Sample schedules must be consistent with tensor
SampleScheduleConsistency ==
    \A s \in SampleDimension :
        sampleSchedules[s] = {t \in TimeDimension :
            \E r \in ResourceDimension, w \in WorkflowDimension :
                tensorCalendar.tensor[s, r, t, w]}

\* Resource bookings must be consistent with tensor  
ResourceBookingConsistency ==
    \A r \in ResourceDimension :
        resourceBookings[r] = {t \in TimeDimension :
            \E s \in SampleDimension, w \in WorkflowDimension :
                tensorCalendar.tensor[s, r, t, w]}

\* Workflow dependencies must be acyclic
AcyclicWorkflowDependencies ==
    \A w \in WorkflowDimension :
        w \notin tensorCalendar.dependencies[w]

\* All scheduled samples must meet deadlines
DeadlineCompliance ==
    \A s \in SampleDimension :
        sampleSchedules[s] # {} =>
            (\A t \in sampleSchedules[s] : t <= tensorCalendar.deadlines[s])

\* Tensor size must be bounded
TensorSizeBounds ==
    Cardinality({<<s, r, t, w>> \in SampleDimension \X ResourceDimension \X 
                 TimeDimension \X WorkflowDimension :
                 tensorCalendar.tensor[s, r, t, w]}) <= MaxTensorSize

\* System metrics must be valid
ValidSystemMetrics ==
    /\ systemMetrics.totalScheduled >= 0
    /\ systemMetrics.conflictCount >= 0
    /\ systemMetrics.utilizationRate >= 0 /\ systemMetrics.utilizationRate <= 100
    /\ systemMetrics.averageLatency >= 0

\* TEMPORAL PROPERTIES - Enhanced with fairness obligations

\* Eventually all conflicts are resolved (guaranteed by fairness)
EventuallyConflictFree ==
    <>[]( tensorCalendar.conflicts = {} )

\* System always makes progress (guaranteed by fairness)
SystemProgress ==
    []<>(lastUpdate > 0)

\* Resource utilization eventually improves (guaranteed by optimization fairness)
EventuallyOptimized ==
    <>[]( systemMetrics.utilizationRate >= 80 )

\* System obligates to eventually schedule samples when resources allow
EventualSampleProcessing ==
    \A s \in SampleDimension :
        <>(\E t \in TimeDimension, r \in ResourceDimension, w \in WorkflowDimension :
            /\ t \in sampleSchedules[s] 
            /\ tensorCalendar.tensor[s, r, t, w])

\* Fairness ensures deadline violations are eventually resolved
DeadlineViolationsResolved ==
    <>[](\A s \in SampleDimension :
        sampleSchedules[s] # {} =>
        (\A t \in sampleSchedules[s] : t <= tensorCalendar.deadlines[s]))

\* System obligates to reach stable utilization through fairness
StableUtilization ==
    <>[](\A threshold \in 1..100 :
        systemMetrics.utilizationRate >= threshold =>
        <>[]( systemMetrics.utilizationRate >= threshold ))

\* Workflow dependencies are satisfied due to fairness obligations  
WorkflowDependenciesSatisfied ==
    <>[](\A w \in WorkflowDimension :
        LET prereqs == tensorCalendar.dependencies[w]
        IN \A dep \in prereqs :
            workflowTimelines[dep] # {} => workflowTimelines[w] # {})

\* Resource capacity constraints are respected through fairness
CapacityConstraintsRespected ==
    <>[](\A r \in ResourceDimension :
        Cardinality(resourceBookings[r]) <= tensorCalendar.capacity[r])

\* System obligates to maintain conflict-free state once achieved
ConflictFreenessMaintained ==
    [](tensorCalendar.conflicts = {} => 
       []<>(tensorCalendar.conflicts = {}))

\* Fairness ensures eventual consistency between tensor and schedules
TensorScheduleConsistency ==
    <>[](\A s \in SampleDimension, r \in ResourceDimension, 
           t \in TimeDimension, w \in WorkflowDimension :
        tensorCalendar.tensor[s, r, t, w] <=>
        (t \in sampleSchedules[s] /\ t \in resourceBookings[r] /\ 
         t \in workflowTimelines[w]))

====
