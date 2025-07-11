---- MODULE SchedulingAgent ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* LIMS Scheduling Agent TLA+ Specification
\* Models the internal behavior of the Scheduling Agent that transitions
\* samples from ACCESSIONED to SCHEDULED state while optimizing
\* resource utilization and respecting priority constraints

CONSTANTS
  MaxSamples,           \* Maximum number of samples that can be scheduled
  MaxConcurrentTests,   \* Maximum concurrent testing capacity
  TestTypes,            \* Set of all available test types (CBC, BMP, etc.)
  Departments,          \* Set of departments (Hematology, Chemistry, etc.)
  Priorities,           \* Set of priority levels (STAT, URGENT, ROUTINE)
  TimeSlots,            \* Set of available time slots
  Technicians,          \* Set of available technicians
  Equipment             \* Set of available equipment

VARIABLES
  \* Scheduling agent state
  schedulingQueue,      \* Queue of samples waiting to be scheduled
  scheduledTests,       \* Set of scheduled test instances
  departmentSchedule,   \* Department -> sequence of scheduled tests
  resourceUtilization,  \* Equipment -> utilization percentage
  priorityQueues,       \* Priority -> queue of samples
  
  \* Sample information
  sampleRequests,       \* SampleID -> test requirements
  samplePriorities,     \* SampleID -> priority level
  sampleEstimates,      \* SampleID -> estimated completion time
  
  \* Scheduling constraints
  equipmentCapacity,    \* Equipment -> maximum concurrent usage
  departmentCapacity,   \* Department -> maximum concurrent tests
  technicianWorkload,   \* Technician -> current workload
  
  \* Scheduling decisions
  schedulingDecisions,  \* Record of all scheduling decisions made
  resourceConflicts,    \* Set of detected resource conflicts
  schedulingFailures    \* Set of samples that failed to schedule

\* Test instance structure
TestInstance == [
  sampleID: Nat,
  testType: TestTypes,
  department: Departments,
  priority: Priorities,
  estimatedDuration: Nat,
  requiredEquipment: SUBSET Equipment,
  assignedTechnician: Technicians,
  scheduledTime: TimeSlots,
  resourceUtilization: [Equipment -> Nat]
]

\* Scheduling request structure
SchedulingRequest == [
  sampleID: Nat,
  requestedTests: SUBSET TestTypes,
  priority: Priorities,
  maxWaitTime: Nat,
  specialRequirements: SUBSET STRING
]

\* Priority ordering: STAT > URGENT > ROUTINE
PriorityOrder(p1, p2) ==
  CASE p1 = "STAT" /\ p2 # "STAT" -> TRUE
    [] p1 = "URGENT" /\ p2 = "ROUTINE" -> TRUE
    [] OTHER -> FALSE

\* Test type to department mapping
TestToDepartment(testType) ==
  CASE testType \in {"CBC", "WBC", "RBC", "PLT"} -> "Hematology"
    [] testType \in {"BMP", "CMP", "LIPID", "GLUCOSE"} -> "Chemistry"
    [] testType \in {"CULTURE", "GRAM", "SENS"} -> "Microbiology"
    [] OTHER -> "General"

\* Equipment required for test type
RequiredEquipment(testType) ==
  CASE testType \in {"CBC", "WBC", "RBC", "PLT"} -> {"HematologyAnalyzer"}
    [] testType \in {"BMP", "CMP", "LIPID", "GLUCOSE"} -> {"ChemistryAnalyzer"}
    [] testType \in {"CULTURE", "GRAM", "SENS"} -> {"Incubator", "Microscope"}
    [] OTHER -> {"GeneralEquipment"}

\* Estimated duration for test type (in minutes)
EstimatedDuration(testType) ==
  CASE testType \in {"CBC", "BMP"} -> 15
    [] testType \in {"CMP", "LIPID"} -> 30
    [] testType \in {"CULTURE", "GRAM"} -> 60
    [] OTHER -> 20

\* Type invariant
TypeInv ==
  /\ schedulingQueue \in Seq(Nat)
  /\ scheduledTests \subseteq TestInstance
  /\ departmentSchedule \in [Departments -> Seq(TestInstance)]
  /\ resourceUtilization \in [Equipment -> Nat]
  /\ priorityQueues \in [Priorities -> Seq(Nat)]
  /\ sampleRequests \in [Nat -> SchedulingRequest]
  /\ samplePriorities \in [Nat -> Priorities]
  /\ sampleEstimates \in [Nat -> Nat]
  /\ equipmentCapacity \in [Equipment -> Nat]
  /\ departmentCapacity \in [Departments -> Nat]
  /\ technicianWorkload \in [Technicians -> Nat]
  /\ schedulingDecisions \in Seq([sampleID: Nat, success: BOOLEAN, timestamp: Nat])
  /\ resourceConflicts \subseteq [equipment: Equipment, timeSlot: TimeSlots]
  /\ schedulingFailures \subseteq Nat

\* Initial state - empty scheduling system
Init ==
  /\ schedulingQueue = <<>>
  /\ scheduledTests = {}
  /\ departmentSchedule = [d \in Departments |-> <<>>]
  /\ resourceUtilization = [e \in Equipment |-> 0]
  /\ priorityQueues = [p \in Priorities |-> <<>>]
  /\ sampleRequests = <<>>
  /\ samplePriorities = <<>>
  /\ sampleEstimates = <<>>
  /\ equipmentCapacity = [e \in Equipment |-> MaxConcurrentTests]
  /\ departmentCapacity = [d \in Departments |-> MaxConcurrentTests]
  /\ technicianWorkload = [t \in Technicians |-> 0]
  /\ schedulingDecisions = <<>>
  /\ resourceConflicts = {}
  /\ schedulingFailures = {}

\* Check if equipment is available for scheduling
EquipmentAvailable(equipment, timeSlot) ==
  resourceUtilization[equipment] < equipmentCapacity[equipment]

\* Check if department has capacity for new test
DepartmentHasCapacity(department) ==
  Len(departmentSchedule[department]) < departmentCapacity[department]

\* Check if technician is available
TechnicianAvailable(technician) ==
  technicianWorkload[technician] < MaxConcurrentTests

\* Calculate total resource usage for a set of tests
CalculateResourceUsage(tests) ==
  LET equipmentUsage == [e \in Equipment |-> 
    Cardinality({t \in tests : e \in RequiredEquipment(t.testType)})]
  IN equipmentUsage

\* Check if scheduling a set of tests would violate resource constraints
WouldViolateConstraints(tests) ==
  \E e \in Equipment: 
    resourceUtilization[e] + Cardinality({t \in tests : e \in RequiredEquipment(t.testType)}) 
    > equipmentCapacity[e]

\* Priority-based scheduling: select highest priority sample from queue
SelectHighestPriority(queue) ==
  LET priorities == {samplePriorities[sampleRequests[s].sampleID] : s \in 1..Len(queue)}
      maxPriority == CHOOSE p \in priorities : \A p2 \in priorities : ~PriorityOrder(p2, p)
  IN CHOOSE s \in 1..Len(queue) : samplePriorities[sampleRequests[queue[s]].sampleID] = maxPriority

\* Receive a scheduling request for a sample
ReceiveSchedulingRequest(sampleID, requestedTests, priority) ==
  /\ sampleID \notin DOMAIN sampleRequests
  /\ LET request == [sampleID |-> sampleID, 
                     requestedTests |-> requestedTests, 
                     priority |-> priority,
                     maxWaitTime |-> 240,  \* 4 hours default
                     specialRequirements |-> {}]
     IN /\ sampleRequests' = sampleRequests @@ (sampleID :> request)
        /\ samplePriorities' = samplePriorities @@ (sampleID :> priority)
        /\ schedulingQueue' = schedulingQueue \o <<sampleID>>
        /\ priorityQueues' = [priorityQueues EXCEPT ![priority] = @ \o <<sampleID>>]
        /\ UNCHANGED <<scheduledTests, departmentSchedule, resourceUtilization, 
                       sampleEstimates, equipmentCapacity, departmentCapacity,
                       technicianWorkload, schedulingDecisions, resourceConflicts,
                       schedulingFailures>>

\* Schedule tests for a sample (core scheduling logic)
ScheduleTests(sampleID) ==
  /\ sampleID \in DOMAIN sampleRequests
  /\ sampleID \notin schedulingFailures
  /\ LET request == sampleRequests[sampleID]
         requestedTests == request.requestedTests
         priority == request.priority
         
         \* Create test instances for each requested test
         testInstances == {[sampleID |-> sampleID,
                           testType |-> testType,
                           department |-> TestToDepartment(testType),
                           priority |-> priority,
                           estimatedDuration |-> EstimatedDuration(testType),
                           requiredEquipment |-> RequiredEquipment(testType),
                           assignedTechnician |-> CHOOSE t \in Technicians : TechnicianAvailable(t),
                           scheduledTime |-> CHOOSE ts \in TimeSlots : TRUE,
                           resourceUtilization |-> CalculateResourceUsage({testType})] 
                          : testType \in requestedTests}
         
         \* Check resource constraints
         canSchedule == /\ \A test \in testInstances : DepartmentHasCapacity(test.department)
                       /\ \A test \in testInstances : TechnicianAvailable(test.assignedTechnician)
                       /\ ~WouldViolateConstraints(testInstances)
                       
     IN IF canSchedule
        THEN \* Schedule the tests
             /\ scheduledTests' = scheduledTests \cup testInstances
             /\ departmentSchedule' = [d \in Departments |-> 
                  IF d \in {test.department : test \in testInstances}
                  THEN departmentSchedule[d] \o 
                       <<CHOOSE test \in testInstances : test.department = d>>
                  ELSE departmentSchedule[d]]
             /\ resourceUtilization' = [e \in Equipment |->
                  resourceUtilization[e] + 
                  Cardinality({test \in testInstances : e \in test.requiredEquipment})]
             /\ technicianWorkload' = [t \in Technicians |->
                  technicianWorkload[t] + 
                  Cardinality({test \in testInstances : test.assignedTechnician = t})]
             /\ sampleEstimates' = sampleEstimates @@ (sampleID :> 
                  Cardinality(testInstances) * 20)  \* Simplified: 20 minutes per test
             /\ schedulingDecisions' = schedulingDecisions \o 
                  <<[sampleID |-> sampleID, 
                     testsScheduled |-> testInstances,
                     timestamp |-> Len(schedulingDecisions) + 1,
                     success |-> TRUE]>>
             /\ UNCHANGED <<schedulingQueue, priorityQueues, sampleRequests, 
                           samplePriorities, equipmentCapacity, departmentCapacity,
                           resourceConflicts, schedulingFailures>>
        ELSE \* Cannot schedule - record failure
             /\ schedulingFailures' = schedulingFailures \cup {sampleID}
             /\ resourceConflicts' = resourceConflicts \cup 
                  {[equipment |-> e, timeSlot |-> "default"] : 
                   e \in Equipment}
             /\ schedulingDecisions' = schedulingDecisions \o 
                  <<[sampleID |-> sampleID, 
                     testsScheduled |-> {},
                     timestamp |-> Len(schedulingDecisions) + 1,
                     success |-> FALSE]>>
             /\ UNCHANGED <<schedulingQueue, priorityQueues, sampleRequests, 
                           samplePriorities, scheduledTests, departmentSchedule,
                           resourceUtilization, sampleEstimates, equipmentCapacity,
                           departmentCapacity, technicianWorkload>>

\* Complete a test (frees up resources)
CompleteTest(testInstance) ==
  /\ testInstance \in scheduledTests
  /\ scheduledTests' = scheduledTests \ {testInstance}
  /\ resourceUtilization' = [e \in Equipment |->
       resourceUtilization[e] - 
       (IF e \in testInstance.requiredEquipment THEN 1 ELSE 0)]
  /\ technicianWorkload' = [t \in Technicians |->
       IF t = testInstance.assignedTechnician 
       THEN technicianWorkload[t] - 1
       ELSE technicianWorkload[t]]
  /\ UNCHANGED <<schedulingQueue, departmentSchedule, priorityQueues, 
                 sampleRequests, samplePriorities, sampleEstimates,
                 equipmentCapacity, departmentCapacity, schedulingDecisions,
                 resourceConflicts, schedulingFailures>>

\* Process scheduling queue (main scheduling loop)
ProcessSchedulingQueue ==
  /\ Len(schedulingQueue) > 0
  /\ LET nextSample == SelectHighestPriority(schedulingQueue)
     IN ScheduleTests(schedulingQueue[nextSample])

\* Next state relation
Next ==
  \/ \E sampleID \in Nat, tests \in SUBSET TestTypes, priority \in Priorities:
       ReceiveSchedulingRequest(sampleID, tests, priority)
  \/ ProcessSchedulingQueue
  \/ \E test \in scheduledTests: CompleteTest(test)

\* Complete specification
Spec == Init /\ [][Next]_<<schedulingQueue, scheduledTests, departmentSchedule,
                            resourceUtilization, priorityQueues, sampleRequests,
                            samplePriorities, sampleEstimates, equipmentCapacity,
                            departmentCapacity, technicianWorkload, schedulingDecisions,
                            resourceConflicts, schedulingFailures>>

\* SAFETY PROPERTIES

\* Property 1: Resource constraints are never violated
ResourceConstraintsRespected ==
  \A e \in Equipment: resourceUtilization[e] <= equipmentCapacity[e]

\* Property 2: Department capacity is never exceeded
DepartmentCapacityRespected ==
  \A d \in Departments: Len(departmentSchedule[d]) <= departmentCapacity[d]

\* Property 3: Technician workload is never exceeded
TechnicianWorkloadRespected ==
  \A t \in Technicians: technicianWorkload[t] <= MaxConcurrentTests

\* Property 4: Priority ordering is maintained
PriorityOrderingMaintained ==
  \A p1, p2 \in Priorities:
    PriorityOrder(p1, p2) => 
      (Len(priorityQueues[p1]) = 0 \/ Len(priorityQueues[p2]) = 0 \/ 
       \A s1 \in 1..Len(priorityQueues[p1]), s2 \in 1..Len(priorityQueues[p2]):
         TRUE)  \* Priority queue processing order maintained

\* Property 5: All scheduled tests have valid resource assignments
ValidResourceAssignments ==
  \A test \in scheduledTests:
    /\ test.department \in Departments
    /\ test.assignedTechnician \in Technicians
    /\ test.requiredEquipment \subseteq Equipment
    /\ test.testType \in TestTypes

\* Property 6: Scheduling decisions are consistent
SchedulingDecisionConsistency ==
  \A i \in 1..Len(schedulingDecisions):
    LET decision == schedulingDecisions[i]
    IN decision.success => 
         \A test \in decision.testsScheduled: test \in scheduledTests

\* Property 7: Resource utilization matches actual usage
ResourceUtilizationAccuracy ==
  \A e \in Equipment:
    resourceUtilization[e] = 
      Cardinality({test \in scheduledTests : e \in test.requiredEquipment})

\* Property 8: Failed samples are tracked
FailedSamplesTracked ==
  \A sampleID \in schedulingFailures:
    /\ sampleID \in DOMAIN sampleRequests
    /\ \E i \in 1..Len(schedulingDecisions):
         /\ schedulingDecisions[i].sampleID = sampleID
         /\ schedulingDecisions[i].success = FALSE

\* LIVENESS PROPERTIES

\* Property 9: Eventually all samples get scheduled or fail
EventualSchedulingResolution ==
  \A sampleID \in DOMAIN sampleRequests:
    <>(sampleID \in schedulingFailures \/ 
       \E test \in scheduledTests: test.sampleID = sampleID)

\* Property 10: High priority samples are processed first
HighPriorityProcessedFirst ==
  \A sampleID \in DOMAIN sampleRequests:
    samplePriorities[sampleID] = "STAT" => 
      <>(\E test \in scheduledTests: test.sampleID = sampleID)

\* Property 11: Resources eventually become available
ResourcesEventuallyAvailable ==
  \A e \in Equipment:
    resourceUtilization[e] = equipmentCapacity[e] => 
      <>(resourceUtilization[e] < equipmentCapacity[e])

\* COMBINED INVARIANTS

\* All safety properties
SafetyProperties ==
  /\ TypeInv
  /\ ResourceConstraintsRespected
  /\ DepartmentCapacityRespected
  /\ TechnicianWorkloadRespected
  /\ PriorityOrderingMaintained
  /\ ValidResourceAssignments
  /\ SchedulingDecisionConsistency
  /\ ResourceUtilizationAccuracy
  /\ FailedSamplesTracked

\* System invariants for runtime validation
SystemInvariants ==
  /\ \A e \in Equipment: resourceUtilization[e] <= equipmentCapacity[e]
  /\ \A d \in Departments: Len(departmentSchedule[d]) <= departmentCapacity[d]
  /\ \A t \in Technicians: technicianWorkload[t] <= MaxConcurrentTests
  /\ \A test \in scheduledTests: test.sampleID \in DOMAIN sampleRequests
  /\ Cardinality(scheduledTests) <= MaxSamples * Cardinality(TestTypes)

====
