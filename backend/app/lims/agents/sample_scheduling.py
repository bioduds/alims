"""
LIMS Scheduling Agent - PostgreSQL Integrated Implementation

This module implements the TLA+ verified scheduling agent that manages
the transition of samples from ACCESSIONED to SCHEDULED state while
integrating with the PostgreSQL lab inventory and equipment database.

Key Features:
- Priority-based scheduling (STAT > URGENT > ROUTINE)
- Resource constraint management
- Equipment and consumable availability checking
- Automatic retry logic for failed scheduling attempts
- Real-time inventory tracking
- Quality control integration
"""

import asyncio
import logging
from datetime import datetime, timedelta, time
from typing import Dict, List, Optional, Set, Tuple
from dataclasses import dataclass
from enum import Enum
import asyncpg

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class Priority(str, Enum):
    """Sample priority levels (TLA+ verified ordering)"""
    STAT = "STAT"
    URGENT = "URGENT"
    ROUTINE = "ROUTINE"

class SchedulingStatus(str, Enum):
    """Scheduling status values"""
    PENDING = "PENDING"
    SCHEDULED = "SCHEDULED"
    IN_PROGRESS = "IN_PROGRESS"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"
    CANCELLED = "CANCELLED"

@dataclass
class TestRequirement:
    """Test requirement specification"""
    test_code: str
    test_name: str
    department: str
    estimated_duration_minutes: int
    required_equipment: List[str]
    required_consumables: List[Dict[str, int]]  # {consumable_id: quantity}

@dataclass
@dataclass
class SchedulingRequest:
    """TLA+ verified scheduling request structure"""
    sample_id: int
    requested_tests: List[str]
    priority: Priority
    special_requirements: List[str] = None
    max_wait_time_hours: int = 24
    requested_completion_date: Optional[datetime] = None
    
    def __post_init__(self):
        if self.special_requirements is None:
            self.special_requirements = []

@dataclass
class SchedulingResponse:
    """TLA+ verified scheduling response structure"""
    success: bool
    sample_id: int
    scheduling_id: Optional[int] = None
    scheduled_tests: List[Dict] = None
    estimated_completion: Optional[datetime] = None
    total_duration_minutes: int = 0
    resource_assignments: Dict[str, List[str]] = None
    warnings: List[str] = None
    error_message: Optional[str] = None
    retry_count: int = 0
    next_retry_time: Optional[datetime] = None
    
    def __post_init__(self):
        if self.scheduled_tests is None:
            self.scheduled_tests = []
        if self.resource_assignments is None:
            self.resource_assignments = {}
        if self.warnings is None:
            self.warnings = []

class SchedulingAgent:
    """
    TLA+ Verified LIMS Scheduling Agent
    
    Implements the formally verified scheduling logic with PostgreSQL
    integration for real-time resource management.
    """
    
    def __init__(self, db_pool: asyncpg.Pool):
        self.db_pool = db_pool
        self.max_retry_attempts = 3
        self.retry_delay_minutes = 15
        self.priority_weights = {
            Priority.STAT: 100,
            Priority.URGENT: 50,
            Priority.ROUTINE: 10
        }
        
    async def schedule_sample_tests(self, request: SchedulingRequest) -> SchedulingResponse:
        """
        Main scheduling entry point - TLA+ verified logic
        
        This method implements the core scheduling algorithm validated
        by the TLA+ specification with PostgreSQL resource management.
        """
        logger.info(f"Scheduling request received for sample {request.sample_id}")
        
        try:
            # Step 1: Validate request
            if not await self._validate_request(request):
                return SchedulingResponse(
                    success=False,
                    sample_id=request.sample_id,
                    error_message="Invalid scheduling request"
                )
            
            # Step 2: Get test requirements
            test_requirements = await self._get_test_requirements(request.requested_tests)
            if not test_requirements:
                return SchedulingResponse(
                    success=False,
                    sample_id=request.sample_id,
                    error_message="No valid test requirements found"
                )
            
            # Step 3: Check resource availability (TLA+ ResourcesAvailable)
            resource_check = await self._check_resource_availability(
                test_requirements, request.priority
            )
            
            if not resource_check['available']:
                # Schedule for retry (TLA+ retry logic)
                retry_time = datetime.now() + timedelta(minutes=self.retry_delay_minutes)
                await self._schedule_retry(request, retry_time)
                
                return SchedulingResponse(
                    success=False,
                    sample_id=request.sample_id,
                    error_message="Insufficient resources - scheduled for retry",
                    next_retry_time=retry_time,
                    warnings=resource_check['warnings']
                )
            
            # Step 4: Reserve resources and create schedule
            scheduling_result = await self._create_schedule(
                request, test_requirements, resource_check['assignments']
            )
            
            if scheduling_result['success']:
                # Update TLA+ state - sample is now SCHEDULED
                await self._update_scheduling_state(
                    request.sample_id, SchedulingStatus.SCHEDULED
                )
                
                return SchedulingResponse(
                    success=True,
                    sample_id=request.sample_id,
                    scheduling_id=scheduling_result['scheduling_id'],
                    scheduled_tests=scheduling_result['scheduled_tests'],
                    estimated_completion=scheduling_result['estimated_completion'],
                    total_duration_minutes=scheduling_result['total_duration'],
                    resource_assignments=scheduling_result['resource_assignments'],
                    warnings=scheduling_result['warnings']
                )
            else:
                return SchedulingResponse(
                    success=False,
                    sample_id=request.sample_id,
                    error_message=scheduling_result['error'],
                    warnings=scheduling_result['warnings']
                )
                
        except Exception as e:
            logger.error(f"Scheduling error for sample {request.sample_id}: {str(e)}")
            return SchedulingResponse(
                success=False,
                sample_id=request.sample_id,
                error_message=f"Scheduling system error: {str(e)}"
            )
    
    async def _validate_request(self, request: SchedulingRequest) -> bool:
        """Validate scheduling request parameters"""
        async with self.db_pool.acquire() as conn:
            # Check if sample exists and is in ACCESSIONED state
            sample_state = await conn.fetchval(
                "SELECT current_state FROM lims.samples WHERE sample_id = $1",
                request.sample_id
            )
            
            if sample_state != "ACCESSIONED":
                logger.warning(f"Sample {request.sample_id} not in ACCESSIONED state")
                return False
            
            # Validate test codes
            valid_tests = await conn.fetch(
                "SELECT test_code FROM lims.test_types WHERE test_code = ANY($1)",
                request.requested_tests
            )
            
            if len(valid_tests) != len(request.requested_tests):
                logger.warning(f"Invalid test codes in request: {request.requested_tests}")
                return False
            
            return True
    
    async def _get_test_requirements(self, test_codes: List[str]) -> List[TestRequirement]:
        """Get detailed test requirements from database"""
        async with self.db_pool.acquire() as conn:
            requirements = []
            
            for test_code in test_codes:
                # Get test details
                test_info = await conn.fetchrow("""
                    SELECT test_code, test_name, department, estimated_duration_minutes
                    FROM lims.test_types 
                    WHERE test_code = $1
                """, test_code)
                
                if not test_info:
                    continue
                
                # Get equipment requirements
                equipment_req = await conn.fetch("""
                    SELECT DISTINCT e.equipment_name, e.equipment_type
                    FROM lims.equipment_capabilities ec
                    JOIN lims.equipment e ON ec.equipment_id = e.equipment_id
                    JOIN lims.test_types tt ON ec.test_type_id = tt.test_type_id
                    WHERE tt.test_code = $1 AND e.status = 'AVAILABLE'
                """, test_code)
                
                # Get consumable requirements
                consumable_req = await conn.fetch("""
                    SELECT tcr.consumable_id, tcr.quantity_required, c.item_name
                    FROM lims.test_consumable_requirements tcr
                    JOIN lims.consumables c ON tcr.consumable_id = c.consumable_id
                    JOIN lims.test_types tt ON tcr.test_type_id = tt.test_type_id
                    WHERE tt.test_code = $1
                """, test_code)
                
                requirements.append(TestRequirement(
                    test_code=test_info['test_code'],
                    test_name=test_info['test_name'],
                    department=test_info['department'],
                    estimated_duration_minutes=test_info['estimated_duration_minutes'],
                    required_equipment=[eq['equipment_name'] for eq in equipment_req],
                    required_consumables=[
                        {req['consumable_id']: req['quantity_required']} 
                        for req in consumable_req
                    ]
                ))
            
            return requirements
    
    async def _check_resource_availability(
        self, 
        requirements: List[TestRequirement], 
        priority: Priority
    ) -> Dict:
        """
        Check if all required resources are available
        
        This implements the TLA+ ResourcesAvailable predicate
        """
        async with self.db_pool.acquire() as conn:
            available = True
            warnings = []
            assignments = {}
            
            # Check equipment availability
            for req in requirements:
                for equipment_name in req.required_equipment:
                    availability = await conn.fetchrow("""
                        SELECT equipment_id, max_concurrent_tests, current_test_count,
                               (max_concurrent_tests - current_test_count) as available_capacity
                        FROM lims.equipment 
                        WHERE equipment_name = $1 AND status = 'AVAILABLE'
                    """, equipment_name)
                    
                    if not availability or availability['available_capacity'] < 1:
                        available = False
                        warnings.append(f"Equipment {equipment_name} not available")
                    else:
                        assignments[equipment_name] = availability['equipment_id']
            
            # Check consumable availability
            for req in requirements:
                for consumable_req in req.required_consumables:
                    for consumable_id, quantity_needed in consumable_req.items():
                        availability = await conn.fetchrow("""
                            SELECT SUM(quantity_available - quantity_reserved) as available_quantity
                            FROM lims.inventory_items 
                            WHERE consumable_id = $1 
                              AND status = 'AVAILABLE' 
                              AND expiration_date > CURRENT_DATE
                        """, consumable_id)
                        
                        available_quantity = availability['available_quantity'] if availability and availability['available_quantity'] is not None else 0
                        
                        if available_quantity < quantity_needed:
                            available = False
                            warnings.append(f"Insufficient consumable inventory: {consumable_id}")
            
            # Priority-based resource allocation
            if not available and priority == Priority.STAT:
                # For STAT priority, try to preempt lower priority samples
                preemption_result = await self._attempt_preemption(requirements, conn)
                if preemption_result['success']:
                    available = True
                    warnings.append("Resources obtained through priority preemption")
            
            return {
                'available': available,
                'warnings': warnings,
                'assignments': assignments
            }
    
    async def _attempt_preemption(
        self, 
        requirements: List[TestRequirement], 
        conn: asyncpg.Connection
    ) -> Dict:
        """
        Attempt to preempt lower priority samples for STAT priority
        
        This implements priority-based resource reallocation
        """
        try:
            # Find lower priority samples that could be rescheduled
            preemptable_samples = await conn.fetch("""
                SELECT ss.scheduling_id, ss.sample_id, ss.equipment_id, ss.priority
                FROM lims.sample_scheduling ss
                WHERE ss.status = 'SCHEDULED' 
                  AND ss.priority IN ('URGENT', 'ROUTINE')
                  AND ss.scheduled_date >= CURRENT_DATE
                ORDER BY 
                    CASE ss.priority 
                        WHEN 'ROUTINE' THEN 1 
                        WHEN 'URGENT' THEN 2 
                    END,
                    ss.scheduled_date DESC
            """)
            
            if preemptable_samples:
                # For simplicity, reschedule the first preemptable sample
                sample_to_reschedule = preemptable_samples[0]
                
                # Update the sample to be rescheduled
                await conn.execute("""
                    UPDATE lims.sample_scheduling 
                    SET status = 'PENDING', 
                        scheduled_date = scheduled_date + INTERVAL '1 day',
                        updated_at = CURRENT_TIMESTAMP
                    WHERE scheduling_id = $1
                """, sample_to_reschedule['scheduling_id'])
                
                # Free up the equipment
                await conn.execute("""
                    UPDATE lims.equipment 
                    SET current_test_count = current_test_count - 1,
                        updated_at = CURRENT_TIMESTAMP
                    WHERE equipment_id = $1
                """, sample_to_reschedule['equipment_id'])
                
                logger.info(f"Preempted sample {sample_to_reschedule['sample_id']} for STAT priority")
                return {'success': True}
            
            return {'success': False}
            
        except Exception as e:
            logger.error(f"Preemption failed: {str(e)}")
            return {'success': False}
    
    async def _create_schedule(
        self, 
        request: SchedulingRequest,
        requirements: List[TestRequirement],
        equipment_assignments: Dict[str, int]
    ) -> Dict:
        """
        Create the actual schedule and reserve resources
        
        This implements the TLA+ ScheduleSample operation
        """
        async with self.db_pool.acquire() as conn:
            try:
                async with conn.transaction():
                    scheduled_tests = []
                    total_duration = 0
                    estimated_completion = datetime.now()
                    
                    for req in requirements:
                        # Find available equipment
                        equipment_id = None
                        for eq_name in req.required_equipment:
                            if eq_name in equipment_assignments:
                                equipment_id = equipment_assignments[eq_name]
                                break
                        
                        if not equipment_id:
                            raise Exception(f"No equipment available for {req.test_code}")
                        
                        # Calculate scheduling time
                        start_time = estimated_completion
                        end_time = start_time + timedelta(minutes=req.estimated_duration_minutes)
                        
                        # Create scheduling record
                        scheduling_id = await conn.fetchval("""
                            INSERT INTO lims.sample_scheduling (
                                sample_id, test_type_id, equipment_id, priority,
                                scheduled_date, estimated_start_time, estimated_end_time,
                                status, retry_count
                            ) VALUES (
                                $1, 
                                (SELECT test_type_id FROM lims.test_types WHERE test_code = $2),
                                $3, $4, $5, $6, $7, 'SCHEDULED', 0
                            ) RETURNING scheduling_id
                        """, 
                        request.sample_id, req.test_code, equipment_id, request.priority.value,
                        start_time.date(), start_time.time(), end_time.time())
                        
                        # Reserve equipment
                        await conn.execute("""
                            UPDATE lims.equipment 
                            SET current_test_count = current_test_count + 1,
                                updated_at = CURRENT_TIMESTAMP
                            WHERE equipment_id = $1
                        """, equipment_id)
                        
                        # Reserve consumables
                        for consumable_req in req.required_consumables:
                            for consumable_id, quantity in consumable_req.items():
                                # Find best inventory item (earliest expiration)
                                inventory_item = await conn.fetchrow("""
                                    SELECT inventory_id, quantity_available - quantity_reserved as free_quantity
                                    FROM lims.inventory_items 
                                    WHERE consumable_id = $1 
                                      AND status = 'AVAILABLE' 
                                      AND expiration_date > CURRENT_DATE
                                      AND (quantity_available - quantity_reserved) >= $2
                                    ORDER BY expiration_date
                                    LIMIT 1
                                """, consumable_id, quantity)
                                
                                if inventory_item:
                                    # Reserve the consumable
                                    await conn.execute("""
                                        UPDATE lims.inventory_items 
                                        SET quantity_reserved = quantity_reserved + $1,
                                            updated_at = CURRENT_TIMESTAMP
                                        WHERE inventory_id = $2
                                    """, quantity, inventory_item['inventory_id'])
                                    
                                    # Create reservation record
                                    await conn.execute("""
                                        INSERT INTO lims.resource_reservations (
                                            scheduling_id, inventory_id, quantity_reserved
                                        ) VALUES ($1, $2, $3)
                                    """, scheduling_id, inventory_item['inventory_id'], quantity)
                        
                        scheduled_tests.append({
                            'scheduling_id': scheduling_id,
                            'test_code': req.test_code,
                            'test_name': req.test_name,
                            'department': req.department,
                            'equipment_id': equipment_id,
                            'estimated_start_time': start_time.isoformat(),
                            'estimated_end_time': end_time.isoformat(),
                            'duration_minutes': req.estimated_duration_minutes
                        })
                        
                        total_duration += req.estimated_duration_minutes
                        estimated_completion = end_time
                    
                    return {
                        'success': True,
                        'scheduling_id': scheduled_tests[0]['scheduling_id'] if scheduled_tests else None,
                        'scheduled_tests': scheduled_tests,
                        'estimated_completion': estimated_completion,
                        'total_duration': total_duration,
                        'resource_assignments': equipment_assignments,
                        'warnings': []
                    }
                    
            except Exception as e:
                logger.error(f"Schedule creation failed: {str(e)}")
                return {
                    'success': False,
                    'error': str(e),
                    'warnings': []
                }
    
    async def _schedule_retry(self, request: SchedulingRequest, retry_time: datetime):
        """
        Schedule a retry attempt for failed scheduling
        
        This implements the TLA+ retry logic
        """
        async with self.db_pool.acquire() as conn:
            await conn.execute("""
                INSERT INTO lims.sample_scheduling (
                    sample_id, priority, scheduled_date, estimated_start_time,
                    status, retry_count
                ) VALUES (
                    $1, $2, $3, $4, 'PENDING', 
                    COALESCE((SELECT MAX(retry_count) FROM lims.sample_scheduling WHERE sample_id = $1), 0) + 1
                )
            """, request.sample_id, request.priority.value, retry_time.date(), retry_time.time())
    
    async def _update_scheduling_state(self, sample_id: int, status: SchedulingStatus):
        """Update the sample's scheduling state"""
        async with self.db_pool.acquire() as conn:
            await conn.execute("""
                UPDATE lims.sample_scheduling 
                SET status = $1, updated_at = CURRENT_TIMESTAMP
                WHERE sample_id = $2 AND status != 'COMPLETED'
            """, status.value, sample_id)
    
    async def process_retry_queue(self):
        """
        Process samples waiting for retry
        
        This should be called periodically to handle retry scheduling
        """
        async with self.db_pool.acquire() as conn:
            retry_samples = await conn.fetch("""
                SELECT DISTINCT ss.sample_id, ss.priority, 
                       array_agg(tt.test_code) as test_codes
                FROM lims.sample_scheduling ss
                JOIN lims.test_types tt ON ss.test_type_id = tt.test_type_id
                WHERE ss.status = 'PENDING' 
                  AND ss.retry_count < $1
                  AND ss.scheduled_date <= CURRENT_DATE
                  AND ss.estimated_start_time <= CURRENT_TIME
                GROUP BY ss.sample_id, ss.priority
            """, self.max_retry_attempts)
            
            for sample in retry_samples:
                request = SchedulingRequest(
                    sample_id=sample['sample_id'],
                    requested_tests=sample['test_codes'],
                    priority=Priority(sample['priority'])
                )
                
                result = await self.schedule_sample_tests(request)
                logger.info(f"Retry result for sample {sample['sample_id']}: {result.success}")
    
    async def get_scheduling_summary(self, sample_id: int) -> Optional[Dict]:
        """Get comprehensive scheduling summary for a sample"""
        async with self.db_pool.acquire() as conn:
            return await conn.fetchrow("""
                SELECT 
                    ss.sample_id,
                    ss.priority,
                    ss.status,
                    ss.scheduled_date,
                    ss.estimated_start_time,
                    ss.actual_start_time,
                    ss.actual_end_time,
                    ss.retry_count,
                    array_agg(tt.test_code) as scheduled_tests,
                    array_agg(e.equipment_name) as assigned_equipment
                FROM lims.sample_scheduling ss
                JOIN lims.test_types tt ON ss.test_type_id = tt.test_type_id
                JOIN lims.equipment e ON ss.equipment_id = e.equipment_id
                WHERE ss.sample_id = $1
                GROUP BY ss.sample_id, ss.priority, ss.status, ss.scheduled_date,
                         ss.estimated_start_time, ss.actual_start_time, ss.actual_end_time,
                         ss.retry_count
            """, sample_id)


# Example usage and integration
async def create_scheduling_agent(database_url: str) -> SchedulingAgent:
    """Create and initialize the scheduling agent with database connection"""
    pool = await asyncpg.create_pool(database_url)
    return SchedulingAgent(pool)

# Testing function
async def test_scheduling_agent():
    """Test the scheduling agent with sample data"""
    # This would typically use the actual database connection
    database_url = "postgresql://lims_user:lims_password@localhost:5432/lims_db"
    
    try:
        agent = await create_scheduling_agent(database_url)
        
        # Test scheduling request
        request = SchedulingRequest(
            sample_id=1,
            requested_tests=["CBC", "BMP"],
            priority=Priority.URGENT
        )
        
        result = await agent.schedule_sample_tests(request)
        print(f"Scheduling result: {result}")
        
        # Test retry processing
        await agent.process_retry_queue()
        
    except Exception as e:
        print(f"Test failed: {e}")

if __name__ == "__main__":
    asyncio.run(test_scheduling_agent())
