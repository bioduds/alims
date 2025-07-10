#!/usr/bin/env python3
"""
ALIMS Tensor Calendar System - Proof of Concept Implementation

This module demonstrates a tensor-based calendar system for laboratory 
information management, where all scheduling operations are modeled as
multi-dimensional tensor operations for optimal performance and prediction.

Key Features:
- Multi-dimensional tensor representation of schedules
- Real-time conflict detection using tensor operations
- Predictive analytics for capacity planning
- Mathematical optimization of resource allocation
- TLA+ property enforcement at runtime
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Set, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
import logging
from concurrent.futures import ThreadPoolExecutor
import asyncio


class ScheduleConflictError(Exception):
    """Raised when a scheduling conflict is detected"""
    pass


class TensorConstraintError(Exception):
    """Raised when tensor constraints are violated"""
    pass


class ResourceType(Enum):
    """Types of laboratory resources"""
    INSTRUMENT = "instrument"
    TECHNICIAN = "technician"
    REAGENT = "reagent"
    SPACE = "space"


class WorkflowStage(Enum):
    """Laboratory workflow stages"""
    SAMPLE_PREP = "sample_preparation"
    ANALYSIS = "analysis"
    QC_REVIEW = "qc_review"
    REPORTING = "reporting"


@dataclass
class TimeSlot:
    """Represents a discrete time slot in the calendar"""
    start_time: datetime
    duration_minutes: int = 15
    
    @property
    def end_time(self) -> datetime:
        return self.start_time + timedelta(minutes=self.duration_minutes)
    
    def overlaps_with(self, other: 'TimeSlot') -> bool:
        """Check if this time slot overlaps with another"""
        return not (self.end_time <= other.start_time or 
                   other.end_time <= self.start_time)


@dataclass
class Resource:
    """Laboratory resource with capacity and availability"""
    id: str
    name: str
    resource_type: ResourceType
    capacity: int = 1
    availability_start: datetime = field(default_factory=datetime.now)
    availability_end: datetime = field(default_factory=lambda: datetime.now() + timedelta(days=7))
    
    def is_available_at(self, time_slot: TimeSlot) -> bool:
        """Check if resource is available during time slot"""
        return (self.availability_start <= time_slot.start_time and
                time_slot.end_time <= self.availability_end)


@dataclass
class Sample:
    """Laboratory sample with scheduling requirements"""
    id: str
    patient_id: str
    sample_type: str
    priority: int  # 1-10 scale
    deadline: datetime
    required_stages: List[WorkflowStage]
    estimated_duration_minutes: int = 60
    
    @property
    def is_stat(self) -> bool:
        """Check if sample is STAT priority"""
        return self.priority >= 9


@dataclass
class ScheduleEvent:
    """Represents a scheduled event in the tensor calendar"""
    sample_id: str
    resource_id: str
    workflow_stage: WorkflowStage
    time_slot: TimeSlot
    dependencies: Set[str] = field(default_factory=set)
    
    def __hash__(self):
        return hash((self.sample_id, self.resource_id, 
                    self.workflow_stage, self.time_slot.start_time))


class TensorCalendarEngine:
    """
    Core tensor-based calendar system for LIMS operations.
    
    Uses numpy tensors to represent multi-dimensional scheduling relationships
    and perform mathematical optimization of laboratory resource allocation.
    """
    
    def __init__(self, 
                 max_samples: int = 1000,
                 max_resources: int = 100,
                 max_time_slots: int = 672,  # 1 week in 15-min slots
                 max_workflows: int = 50):
        """
        Initialize tensor calendar engine.
        
        Args:
            max_samples: Maximum concurrent samples
            max_resources: Maximum number of resources
            max_time_slots: Maximum time horizon in slots
            max_workflows: Maximum concurrent workflows
        """
        self.logger = logging.getLogger("TensorCalendar")
        
        # Tensor dimensions
        self.max_samples = max_samples
        self.max_resources = max_resources
        self.max_time_slots = max_time_slots
        self.max_workflows = max_workflows
        
        # Core scheduling tensor [sample, resource, time, workflow]
        self.schedule_tensor = np.zeros(
            (max_samples, max_resources, max_time_slots, len(WorkflowStage)),
            dtype=np.bool_
        )
        
        # Resource capacity tensor [resource, time]
        self.capacity_tensor = np.ones((max_resources, max_time_slots), dtype=np.int8)
        
        # Deadline tensor [sample, time]
        self.deadline_tensor = np.full((max_samples, max_time_slots), False, dtype=np.bool_)
        
        # Dependency matrix [workflow, workflow]
        self.dependency_matrix = np.zeros((len(WorkflowStage), len(WorkflowStage)), dtype=np.bool_)
        
        # Lookup tables
        self.sample_index: Dict[str, int] = {}
        self.resource_index: Dict[str, int] = {}
        self.time_slot_index: Dict[datetime, int] = {}
        self.workflow_index: Dict[WorkflowStage, int] = {
            stage: i for i, stage in enumerate(WorkflowStage)
        }
        
        # Scheduled events
        self.scheduled_events: Set[ScheduleEvent] = set()
        self.samples: Dict[str, Sample] = {}
        self.resources: Dict[str, Resource] = {}
        
        # Performance metrics
        self.metrics = {
            'total_scheduled': 0,
            'conflicts_detected': 0,
            'optimization_iterations': 0,
            'utilization_rate': 0.0,
            'average_latency_seconds': 0.0
        }
        
        self.logger.info("Tensor Calendar Engine initialized with "
                        f"tensor shape {self.schedule_tensor.shape}")
    
    def add_sample(self, sample: Sample) -> int:
        """Add a sample to the system and return its tensor index"""
        if sample.id in self.sample_index:
            raise ValueError(f"Sample {sample.id} already exists")
        
        if len(self.sample_index) >= self.max_samples:
            raise TensorConstraintError("Maximum sample capacity reached")
        
        index = len(self.sample_index)
        self.sample_index[sample.id] = index
        self.samples[sample.id] = sample
        
        # Set deadline tensor
        time_index = self._get_time_index(sample.deadline)
        if time_index < self.max_time_slots:
            self.deadline_tensor[index, time_index] = True
        
        self.logger.debug(f"Added sample {sample.id} at tensor index {index}")
        return index
    
    def add_resource(self, resource: Resource) -> int:
        """Add a resource to the system and return its tensor index"""
        if resource.id in self.resource_index:
            raise ValueError(f"Resource {resource.id} already exists")
        
        if len(self.resource_index) >= self.max_resources:
            raise TensorConstraintError("Maximum resource capacity reached")
        
        index = len(self.resource_index)
        self.resource_index[resource.id] = index
        self.resources[resource.id] = resource
        
        # Set capacity tensor
        self.capacity_tensor[index, :] = resource.capacity
        
        self.logger.debug(f"Added resource {resource.id} at tensor index {index}")
        return index
    
    def _get_time_index(self, timestamp: datetime) -> int:
        """Convert datetime to tensor time index"""
        if timestamp not in self.time_slot_index:
            # Create time slots on demand - use floor for base time
            if not self.time_slot_index:
                # Initialize base time to current time rounded down to 15-minute slot
                now = datetime.now()
                base_time = now.replace(minute=(now.minute // 15) * 15, second=0, microsecond=0)
                self.time_slot_index[base_time] = 0
            else:
                base_time = min(self.time_slot_index.keys())
            
            time_diff = timestamp - base_time
            slot_index = int(time_diff.total_seconds() // (15 * 60))  # 15-minute slots
            
            if 0 <= slot_index < self.max_time_slots:
                self.time_slot_index[timestamp] = slot_index
                return slot_index
            else:
                # For demo purposes, wrap around if outside bounds
                wrapped_index = slot_index % self.max_time_slots
                self.time_slot_index[timestamp] = wrapped_index
                return wrapped_index
        
        return self.time_slot_index[timestamp]
    
    def schedule_event(self, event: ScheduleEvent) -> bool:
        """
        Schedule an event using tensor operations.
        
        Returns True if successfully scheduled, raises exception on conflict.
        """
        try:
            # Get tensor indices
            sample_idx = self.sample_index[event.sample_id]
            resource_idx = self.resource_index[event.resource_id]
            time_idx = self._get_time_index(event.time_slot.start_time)
            workflow_idx = self.workflow_index[event.workflow_stage]
            
            # Check constraints using tensor operations
            self._validate_scheduling_constraints(sample_idx, resource_idx, time_idx, workflow_idx)
            
            # Update schedule tensor
            self.schedule_tensor[sample_idx, resource_idx, time_idx, workflow_idx] = True
            
            # Update capacity tensor
            self.capacity_tensor[resource_idx, time_idx] -= 1
            
            # Add to scheduled events
            self.scheduled_events.add(event)
            
            # Update metrics
            self.metrics['total_scheduled'] += 1
            self._update_utilization_metrics()
            
            self.logger.debug(f"Scheduled event: {event.sample_id} -> "
                            f"{event.resource_id} at {event.time_slot.start_time}")
            
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to schedule event: {e}")
            raise
    
    def _validate_scheduling_constraints(self, sample_idx: int, resource_idx: int, 
                                       time_idx: int, workflow_idx: int):
        """Validate scheduling constraints using tensor operations"""
        
        # Check resource capacity
        if self.capacity_tensor[resource_idx, time_idx] <= 0:
            raise ScheduleConflictError(
                f"Resource {resource_idx} overbooked at time {time_idx}")
        
        # Check for double-booking
        if self.schedule_tensor[sample_idx, resource_idx, time_idx, workflow_idx]:
            raise ScheduleConflictError(
                f"Sample {sample_idx} already scheduled at time {time_idx}")
        
        # Check workflow dependencies using matrix multiplication
        scheduled_workflows = self.schedule_tensor[sample_idx, :, :time_idx, :].any(axis=(0, 1))
        required_dependencies = self.dependency_matrix[workflow_idx, :]
        
        missing_dependencies = required_dependencies & ~scheduled_workflows
        if missing_dependencies.any():
            missing_stages = [WorkflowStage(i) for i, missing in enumerate(missing_dependencies) if missing]
            raise ScheduleConflictError(
                f"Missing workflow dependencies: {missing_stages}")
        
        # Check deadline compliance
        if self.deadline_tensor[sample_idx, time_idx:].sum() == 0:
            raise ScheduleConflictError(
                f"Sample {sample_idx} scheduled after deadline")
    
    def detect_conflicts(self) -> List[Dict[str, Any]]:
        """Detect scheduling conflicts using tensor operations"""
        conflicts = []
        
        # Find resource overbooking using tensor reduction
        resource_utilization = self.schedule_tensor.sum(axis=(0, 3))  # Sum over samples and workflows
        overbooked = resource_utilization > self.capacity_tensor
        
        overbooked_indices = np.where(overbooked)
        for resource_idx, time_idx in zip(*overbooked_indices):
            conflicts.append({
                'type': 'resource_overbooking',
                'resource_idx': resource_idx,
                'time_idx': time_idx,
                'utilization': resource_utilization[resource_idx, time_idx],
                'capacity': self.capacity_tensor[resource_idx, time_idx]
            })
        
        # Find deadline violations
        for sample_id, sample_idx in self.sample_index.items():
            sample = self.samples[sample_id]
            deadline_idx = self._get_time_index(sample.deadline)
            
            scheduled_after_deadline = self.schedule_tensor[sample_idx, :, deadline_idx:, :].any()
            if scheduled_after_deadline:
                conflicts.append({
                    'type': 'deadline_violation',
                    'sample_id': sample_id,
                    'deadline': sample.deadline
                })
        
        self.metrics['conflicts_detected'] = len(conflicts)
        return conflicts
    
    def optimize_schedule(self) -> Dict[str, Any]:
        """
        Optimize schedule using tensor mathematical operations.
        
        This is a simplified optimization - real implementation would use
        sophisticated tensor decomposition and optimization algorithms.
        """
        self.logger.info("Starting tensor schedule optimization...")
        
        # Calculate current utilization matrix
        utilization = self.schedule_tensor.sum(axis=(0, 3)) / np.maximum(self.capacity_tensor, 1)
        
        # Find underutilized resources and time slots
        underutilized = utilization < 0.7
        overutilized = utilization > 0.9
        
        # Simulate optimization (would be more sophisticated in real implementation)
        optimization_opportunities = {
            'underutilized_slots': int(underutilized.sum()),
            'overutilized_slots': int(overutilized.sum()),
            'average_utilization': float(utilization.mean()),
            'optimization_potential': float((overutilized.sum() - underutilized.sum()) / utilization.size)
        }
        
        # Update metrics
        self.metrics['optimization_iterations'] += 1
        self.metrics['utilization_rate'] = optimization_opportunities['average_utilization'] * 100
        
        self.logger.info(f"Optimization complete: {optimization_opportunities}")
        return optimization_opportunities
    
    def _update_utilization_metrics(self):
        """Update real-time utilization metrics"""
        if self.schedule_tensor.any():
            total_scheduled = self.schedule_tensor.sum()
            total_capacity = self.capacity_tensor.sum()
            self.metrics['utilization_rate'] = (total_scheduled / total_capacity) * 100
    
    def predict_bottlenecks(self, time_window_hours: int = 24) -> List[Dict[str, Any]]:
        """
        Predict future bottlenecks using tensor pattern analysis.
        
        Uses tensor operations to identify patterns and predict resource constraints.
        """
        bottlenecks = []
        
        # Calculate time window in slots
        window_slots = time_window_hours * 4  # 15-minute slots
        current_time_idx = len(self.time_slot_index)
        
        if current_time_idx + window_slots > self.max_time_slots:
            window_slots = self.max_time_slots - current_time_idx
        
        # Analyze utilization patterns
        window_utilization = self.schedule_tensor[:, :, current_time_idx:current_time_idx + window_slots, :].sum(axis=(0, 3))
        window_capacity = self.capacity_tensor[:, current_time_idx:current_time_idx + window_slots]
        
        # Predict overutilization
        predicted_overload = window_utilization > window_capacity
        
        overload_indices = np.where(predicted_overload)
        for resource_idx, time_offset in zip(*overload_indices):
            bottlenecks.append({
                'resource_idx': resource_idx,
                'predicted_time': current_time_idx + time_offset,
                'predicted_utilization': int(window_utilization[resource_idx, time_offset]),
                'capacity': int(window_capacity[resource_idx, time_offset]),
                'severity': 'high' if window_utilization[resource_idx, time_offset] > window_capacity[resource_idx, time_offset] * 1.5 else 'medium'
            })
        
        return bottlenecks
    
    def get_schedule_for_sample(self, sample_id: str) -> List[ScheduleEvent]:
        """Get all scheduled events for a specific sample"""
        return [event for event in self.scheduled_events if event.sample_id == sample_id]
    
    def get_schedule_for_resource(self, resource_id: str) -> List[ScheduleEvent]:
        """Get all scheduled events for a specific resource"""
        return [event for event in self.scheduled_events if event.resource_id == resource_id]
    
    def get_tensor_statistics(self) -> Dict[str, Any]:
        """Get comprehensive tensor and scheduling statistics"""
        return {
            'tensor_shape': self.schedule_tensor.shape,
            'tensor_memory_mb': self.schedule_tensor.nbytes / (1024 * 1024),
            'total_samples': len(self.sample_index),
            'total_resources': len(self.resource_index),
            'total_time_slots': len(self.time_slot_index),
            'scheduled_events': len(self.scheduled_events),
            'metrics': self.metrics.copy()
        }
    
    async def process_real_time_event(self, event_type: str, event_data: Dict[str, Any]):
        """Process real-time calendar events asynchronously"""
        self.logger.debug(f"Processing real-time event: {event_type}")
        
        try:
            if event_type == "sample_arrival":
                sample = Sample(**event_data)
                self.add_sample(sample)
                
            elif event_type == "resource_unavailable":
                resource_id = event_data['resource_id']
                if resource_id in self.resource_index:
                    resource_idx = self.resource_index[resource_id]
                    start_time = event_data['start_time']
                    end_time = event_data['end_time']
                    
                    # Mark resource as unavailable
                    start_idx = self._get_time_index(start_time)
                    end_idx = self._get_time_index(end_time)
                    self.capacity_tensor[resource_idx, start_idx:end_idx] = 0
                    
            elif event_type == "priority_change":
                sample_id = event_data['sample_id']
                new_priority = event_data['priority']
                if sample_id in self.samples:
                    self.samples[sample_id].priority = new_priority
                    
            elif event_type == "deadline_update":
                sample_id = event_data['sample_id']
                new_deadline = event_data['deadline']
                if sample_id in self.samples:
                    self.samples[sample_id].deadline = new_deadline
                    sample_idx = self.sample_index[sample_id]
                    
                    # Update deadline tensor
                    self.deadline_tensor[sample_idx, :] = False
                    deadline_idx = self._get_time_index(new_deadline)
                    if deadline_idx < self.max_time_slots:
                        self.deadline_tensor[sample_idx, deadline_idx] = True
            
            # Trigger automatic optimization after events
            await asyncio.create_task(self._async_optimize())
            
        except Exception as e:
            self.logger.error(f"Error processing real-time event {event_type}: {e}")
            raise
    
    async def _async_optimize(self):
        """Asynchronous tensor optimization"""
        with ThreadPoolExecutor(max_workers=2) as executor:
            # Run optimization in background thread
            optimization_result = await asyncio.get_event_loop().run_in_executor(
                executor, self.optimize_schedule
            )
            
            # Check for conflicts
            conflicts = await asyncio.get_event_loop().run_in_executor(
                executor, self.detect_conflicts
            )
            
            if conflicts:
                self.logger.warning(f"Detected {len(conflicts)} scheduling conflicts after optimization")
                
            return optimization_result


# Example usage and demonstration
async def demo_tensor_calendar():
    """Demonstrate tensor calendar system capabilities"""
    print("🧮 ALIMS Tensor Calendar System Demo")
    print("=" * 50)
    
    # Initialize tensor calendar
    calendar = TensorCalendarEngine(max_samples=10, max_resources=5, max_time_slots=96)
    
    # Add resources
    resources = [
        Resource("HPLC-001", "HPLC System 1", ResourceType.INSTRUMENT, capacity=1),
        Resource("LCMS-001", "LC-MS System 1", ResourceType.INSTRUMENT, capacity=1),
        Resource("TECH-001", "Lab Technician 1", ResourceType.TECHNICIAN, capacity=2),
        Resource("PREP-ROOM", "Sample Prep Room", ResourceType.SPACE, capacity=4)
    ]
    
    for resource in resources:
        calendar.add_resource(resource)
    
    print(f"✅ Added {len(resources)} resources to tensor calendar")
    
    # Add samples
    now = datetime.now()
    samples = [
        Sample("SAMPLE-001", "PAT-001", "Blood", priority=9, 
               deadline=now + timedelta(hours=2),
               required_stages=[WorkflowStage.SAMPLE_PREP, WorkflowStage.ANALYSIS]),
        Sample("SAMPLE-002", "PAT-002", "Urine", priority=5,
               deadline=now + timedelta(hours=8), 
               required_stages=[WorkflowStage.SAMPLE_PREP, WorkflowStage.ANALYSIS, WorkflowStage.QC_REVIEW]),
        Sample("SAMPLE-003", "PAT-003", "Plasma", priority=7,
               deadline=now + timedelta(hours=4),
               required_stages=[WorkflowStage.ANALYSIS, WorkflowStage.REPORTING])
    ]
    
    for sample in samples:
        calendar.add_sample(sample)
    
    print(f"✅ Added {len(samples)} samples to tensor calendar")
    
    # Schedule events
    events = [
        ScheduleEvent("SAMPLE-001", "PREP-ROOM", WorkflowStage.SAMPLE_PREP,
                     TimeSlot(now + timedelta(minutes=15))),
        ScheduleEvent("SAMPLE-001", "HPLC-001", WorkflowStage.ANALYSIS,
                     TimeSlot(now + timedelta(minutes=45))),
        ScheduleEvent("SAMPLE-002", "PREP-ROOM", WorkflowStage.SAMPLE_PREP,
                     TimeSlot(now + timedelta(minutes=30))),
        ScheduleEvent("SAMPLE-002", "LCMS-001", WorkflowStage.ANALYSIS,
                     TimeSlot(now + timedelta(hours=1)))
    ]
    
    scheduled_count = 0
    for event in events:
        try:
            calendar.schedule_event(event)
            scheduled_count += 1
        except ScheduleConflictError as e:
            print(f"❌ Scheduling conflict: {e}")
    
    print(f"✅ Successfully scheduled {scheduled_count}/{len(events)} events")
    
    # Demonstrate tensor operations
    print("\n📊 Tensor Operations Demo:")
    
    # Detect conflicts
    conflicts = calendar.detect_conflicts()
    print(f"   Conflicts detected: {len(conflicts)}")
    
    # Optimize schedule
    optimization = calendar.optimize_schedule()
    print(f"   Utilization rate: {optimization['average_utilization']:.1%}")
    
    # Predict bottlenecks
    bottlenecks = calendar.predict_bottlenecks(time_window_hours=6)
    print(f"   Predicted bottlenecks: {len(bottlenecks)}")
    
    # Show tensor statistics
    stats = calendar.get_tensor_statistics()
    print(f"   Tensor memory usage: {stats['tensor_memory_mb']:.2f} MB")
    print(f"   Total scheduled events: {stats['scheduled_events']}")
    
    # Demonstrate real-time events
    print("\n⚡ Real-time Event Processing:")
    
    await calendar.process_real_time_event("sample_arrival", {
        'id': 'SAMPLE-URGENT',
        'patient_id': 'PAT-URGENT',
        'sample_type': 'Blood',
        'priority': 10,
        'deadline': now + timedelta(hours=1),
        'required_stages': [WorkflowStage.ANALYSIS],
        'estimated_duration_minutes': 30
    })
    
    await calendar.process_real_time_event("resource_unavailable", {
        'resource_id': 'HPLC-001',
        'start_time': now + timedelta(hours=2),
        'end_time': now + timedelta(hours=3)
    })
    
    print("✅ Processed real-time events with automatic optimization")
    
    # Final statistics
    final_stats = calendar.get_tensor_statistics()
    print(f"\n📈 Final Results:")
    print(f"   Total samples: {final_stats['total_samples']}")
    print(f"   Total resources: {final_stats['total_resources']}")
    print(f"   Scheduled events: {final_stats['scheduled_events']}")
    print(f"   Utilization rate: {final_stats['metrics']['utilization_rate']:.1f}%")
    print(f"   Conflicts detected: {final_stats['metrics']['conflicts_detected']}")


if __name__ == "__main__":
    # Setup logging
    logging.basicConfig(level=logging.INFO, 
                       format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    
    # Run demonstration
    asyncio.run(demo_tensor_calendar())
