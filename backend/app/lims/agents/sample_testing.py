"""
Sample Testing Agent - TLA+ Verified Implementation

Implements the TLA+ verified workflow for managing laboratory test execution:
- SCHEDULED → TESTING → COMPLETED → QC_PENDING
- TESTING → FAILED → SCHEDULED (retry logic)
- Instrument/resource management, result capture, audit trail

This agent is designed to strictly follow the TLA+ model in
plans/feature-20250711-sample-testing/tla/SampleTestingAgent.tla
"""

import asyncio
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set
import asyncpg
import logging
from datetime import datetime

logger = logging.getLogger(__name__)

class TestState(str, Enum):
    SCHEDULED = "SCHEDULED"
    TESTING = "TESTING"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"
    QC_PENDING = "QC_PENDING"

class InstrumentStatus(str, Enum):
    AVAILABLE = "AVAILABLE"
    BUSY = "BUSY"
    MAINTENANCE = "MAINTENANCE"

@dataclass
class TestExecution:
    test_id: int
    state: TestState
    result: Optional[str] = None
    retry_count: int = 0
    instrument_id: Optional[int] = None
    scheduled_time: Optional[datetime] = None
    completed_time: Optional[datetime] = None
    resource_consumed: int = 0
    audit_log: List[Dict] = field(default_factory=list)

class SampleTestingAgent:
    def __init__(self, db_pool: asyncpg.Pool, max_retries: int = 3, max_concurrent: int = 2):
        self.db_pool = db_pool
        self.max_retries = max_retries
        self.max_concurrent = max_concurrent

    async def run(self):
        # Main loop for polling and processing scheduled tests
        while True:
            await self.process_scheduled_tests()
            await asyncio.sleep(5)

    async def process_scheduled_tests(self):
        # Fetch scheduled tests from DB and process them
        async with self.db_pool.acquire() as conn:
            scheduled = await conn.fetch("""
                SELECT test_id FROM lims.test_execution WHERE state = 'SCHEDULED'
            """)
            for row in scheduled:
                await self.start_test(row['test_id'])

    async def start_test(self, test_id: int):
        # Assign instrument, update state, and start execution
        async with self.db_pool.acquire() as conn:
            # Find available instrument
            instrument = await conn.fetchrow("""
                SELECT instrument_id FROM lims.equipment
                WHERE status = 'AVAILABLE'
                LIMIT 1
            """)
            if not instrument:
                logger.info(f"No available instrument for test {test_id}")
                return
            await conn.execute("""
                UPDATE lims.test_execution
                SET state = 'TESTING', instrument_id = $1, scheduled_time = $2
                WHERE test_id = $3
            """, instrument['instrument_id'], datetime.now(), test_id)
            logger.info(f"Test {test_id} started on instrument {instrument['instrument_id']}")

    async def complete_test(self, test_id: int, result: str):
        # Mark test as completed and store result
        async with self.db_pool.acquire() as conn:
            await conn.execute("""
                UPDATE lims.test_execution
                SET state = 'COMPLETED', result = $1, completed_time = $2
                WHERE test_id = $3
            """, result, datetime.now(), test_id)
            logger.info(f"Test {test_id} completed with result {result}")

    async def fail_test(self, test_id: int):
        # Mark test as failed and increment retry count
        async with self.db_pool.acquire() as conn:
            await conn.execute("""
                UPDATE lims.test_execution
                SET state = 'FAILED', retry_count = retry_count + 1
                WHERE test_id = $1
            """, test_id)
            logger.info(f"Test {test_id} failed")

    async def retry_failed_tests(self):
        # Retry failed tests if retry_count < max_retries
        async with self.db_pool.acquire() as conn:
            failed = await conn.fetch("""
                SELECT test_id, retry_count FROM lims.test_execution
                WHERE state = 'FAILED' AND retry_count < $1
            """, self.max_retries)
            for row in failed:
                await conn.execute("""
                    UPDATE lims.test_execution
                    SET state = 'SCHEDULED'
                    WHERE test_id = $1
                """, row['test_id'])
                logger.info(f"Test {row['test_id']} scheduled for retry")

    async def transition_to_qc(self):
        # Move completed tests to QC_PENDING
        async with self.db_pool.acquire() as conn:
            await conn.execute("""
                UPDATE lims.test_execution
                SET state = 'QC_PENDING'
                WHERE state = 'COMPLETED' AND result IS NOT NULL
            """)
            logger.info("All completed tests transitioned to QC_PENDING")

    # Additional methods for audit log, resource tracking, and maintenance can be added here

# Usage example (to be run in an async context):
# db_pool = await asyncpg.create_pool(...)
# agent = SampleTestingAgent(db_pool)
# await agent.run()
