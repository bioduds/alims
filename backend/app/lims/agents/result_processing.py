"""
Result Processing Agent implementation.

This agent processes raw laboratory test results and converts them into
structured data ready for validation. It follows the TLA+ specification
validated in plans/feature-20250712-result-processing/.
"""

import asyncio
import logging
import json
import csv
import io
from typing import Dict, List, Optional, Any, Callable
from datetime import datetime, timedelta
from dataclasses import dataclass

from ..models import (
    SystemState,
    ProcessingState,
    RawResult,
    ProcessedResult,
    ProcessingRecord,
    AgentConfiguration,
    AgentMetrics,
    ProcessingError,
    CapacityExceededError,
    MaxRetriesExceededError,
    InvalidSystemStateError,
)


@dataclass
class ProcessingContext:
    """Context information for result processing."""
    raw_result: RawResult
    processing_record: ProcessingRecord
    start_time: datetime
    attempt_number: int


class ResultProcessingAgent:
    """
    Result Processing Agent implementation following TLA+ specification.
    
    This agent processes raw laboratory test results and converts them into
    structured data ready for validation. It maintains all safety invariants
    and properties proven by the TLA+ model.
    """
    
    def __init__(self, config: AgentConfiguration):
        """Initialize the Result Processing Agent."""
        self.config = config
        self.logger = logging.getLogger(self.__class__.__name__)
        
        # State variables (match TLA+ specification)
        self.system_state = SystemState.INITIALIZING
        self.raw_results: List[RawResult] = []
        self.processed_results: List[ProcessedResult] = []
        self.processing_records: Dict[str, ProcessingRecord] = {}
        
        # Metrics and monitoring
        self.metrics = AgentMetrics()
        self._start_time: Optional[datetime] = None
        
        # Processing handlers for different formats
        self.processing_handlers: Dict[str, Callable] = {
            "JSON": self._process_json_result,
            "CSV": self._process_csv_result,
            "XML": self._process_xml_result,
            "HL7": self._process_hl7_result,
        }
    
    async def initialize(self) -> None:
        """
        Initialize the system.
        Corresponds to InitializeSystem action in TLA+.
        """
        if self.system_state != SystemState.INITIALIZING:
            raise InvalidSystemStateError(f"Cannot initialize from state {self.system_state}")
        
        self._start_time = datetime.utcnow()
        self.system_state = SystemState.READY
        self._log_state_transition("INITIALIZING", "READY")
        
        self.logger.info("Result Processing Agent initialized successfully")
    
    async def receive_raw_result(self, raw_result: RawResult) -> bool:
        """
        Receive a raw result for processing.
        
        Returns True if result was accepted, False if rejected due to capacity.
        Corresponds to ReceiveRawResult action in TLA+.
        """
        # Check system state
        if self.system_state not in [SystemState.READY, SystemState.PROCESSING]:
            if self.system_state == SystemState.OVERLOADED:
                return False
            raise InvalidSystemStateError(f"Cannot receive results in state {self.system_state}")
        
        # Check capacity limits (TLA+ CapacityLimits invariant)
        if len(self.raw_results) >= self.config.max_raw_results:
            self.system_state = SystemState.OVERLOADED
            self._log_state_transition("PROCESSING", "OVERLOADED")
            return False
        
        # Add result to queue
        self.raw_results.append(raw_result)
        
        # Create processing record
        processing_record = ProcessingRecord(
            raw_result_id=raw_result.id,
            current_state=ProcessingState.RAW_RECEIVED
        )
        processing_record.add_state_transition(ProcessingState.RAW_RECEIVED)
        self.processing_records[raw_result.id] = processing_record
        
        # Update system state
        if self.system_state == SystemState.READY:
            self.system_state = SystemState.PROCESSING
            self._log_state_transition("READY", "PROCESSING")
        
        # Update metrics
        self.metrics.total_results_received += 1
        self.metrics.current_queue_size = len(self.raw_results)
        
        # Verify TLA+ invariants
        self._verify_invariants()
        
        return True
    
    async def process_next_result(self) -> Optional[str]:
        """
        Process the next result in the queue.
        
        Returns the result ID if processing was initiated, None if no results to process.
        Corresponds to StartProcessing action in TLA+.
        """
        if self.system_state not in [SystemState.PROCESSING, SystemState.READY]:
            return None
            
        if not self.raw_results:
            return None
        
        # Find next result to process
        for raw_result in self.raw_results:
            processing_record = self.processing_records[raw_result.id]
            
            # Check if this result can be processed
            if processing_record.current_state == ProcessingState.RAW_RECEIVED:
                # Start processing new result
                await self._start_processing(raw_result, processing_record)
                return raw_result.id
            elif (processing_record.current_state == ProcessingState.FAILED and 
                  processing_record.can_retry(self.config.max_retries)):
                # Retry failed result
                await self._start_processing(raw_result, processing_record)
                return raw_result.id
        
        return None
    
    async def _start_processing(self, raw_result: RawResult, processing_record: ProcessingRecord) -> None:
        """Start processing a result - internal method."""
        # Increment retry count if this is a retry
        if processing_record.current_state == ProcessingState.FAILED:
            processing_record.increment_retry()
            self.metrics.total_retries_attempted += 1
        
        processing_record.add_state_transition(ProcessingState.PROCESSING)
        
        self.logger.info(f"Started processing result {raw_result.id} (attempt {processing_record.retry_count + 1})")
        
        # Create processing context
        context = ProcessingContext(
            raw_result=raw_result,
            processing_record=processing_record,
            start_time=datetime.utcnow(),
            attempt_number=processing_record.retry_count + 1
        )
        
        # Process asynchronously
        asyncio.create_task(self._process_result_async(context))
    
    async def _process_result_async(self, context: ProcessingContext) -> None:
        """Process a result asynchronously."""
        try:
            # Get appropriate handler for the data format
            handler = self.processing_handlers.get(context.raw_result.format_type)
            if not handler:
                raise ProcessingError(f"No handler for format type: {context.raw_result.format_type}")
            
            # Process the result
            processed_result = await handler(context.raw_result)
            
            # Handle successful processing
            await self._handle_processing_success(context, processed_result)
            
        except Exception as e:
            # Handle processing failure
            error_message = str(e)
            await self._handle_processing_failure(context, error_message)
    
    async def _handle_processing_success(self, context: ProcessingContext, processed_result: ProcessedResult) -> None:
        """Handle successful processing - corresponds to CompleteProcessing action in TLA+."""
        processing_time = (datetime.utcnow() - context.start_time).total_seconds() * 1000
        
        # Update processing record
        processing_record = context.processing_record
        processing_record.add_state_transition(ProcessingState.PROCESSED)
        
        # Update metrics
        self.metrics.total_results_processed += 1
        self._update_average_processing_time(processing_time)
        
        self.logger.info(f"Completed processing result {context.raw_result.id} in {processing_time:.2f}ms")
        
        # Queue for review
        await self._queue_for_review(context.raw_result.id, processed_result)
        
        # Verify TLA+ invariants
        self._verify_invariants()
    
    async def _handle_processing_failure(self, context: ProcessingContext, error_message: str) -> None:
        """Handle processing failure - corresponds to ProcessingFails action in TLA+."""
        processing_record = context.processing_record
        processing_record.add_state_transition(ProcessingState.FAILED)
        processing_record.add_error(error_message)
        
        # Update metrics
        if not processing_record.can_retry(self.config.max_retries):
            self.metrics.total_results_failed += 1
            self.logger.error(f"Result {context.raw_result.id} failed permanently: {error_message}")
        else:
            self.logger.warning(f"Result {context.raw_result.id} failed (retry {processing_record.retry_count}): {error_message}")
        
        # Verify TLA+ invariants
        self._verify_invariants()
    
    async def _queue_for_review(self, raw_result_id: str, processed_result: ProcessedResult) -> None:
        """Queue a processed result for review - corresponds to QueueForReview action in TLA+."""
        # Check processed results capacity
        if len(self.processed_results) >= self.config.max_processed_results:
            # In a real system, this would trigger downstream processing
            # For now, we'll remove the oldest processed result
            self.processed_results.pop(0)
        
        # Add to processed results queue
        self.processed_results.append(processed_result)
        
        # Update processing record
        processing_record = self.processing_records[raw_result_id]
        processing_record.add_state_transition(ProcessingState.QUEUED_FOR_REVIEW)
        
        # Update metrics
        self.metrics.current_processed_queue_size = len(self.processed_results)
        
        self.logger.info(f"Queued result {raw_result_id} for review")
        
        # Remove from raw results queue
        self.raw_results = [r for r in self.raw_results if r.id != raw_result_id]
        self.metrics.current_queue_size = len(self.raw_results)
        
        # Check if we should transition system state
        if not self.raw_results:
            old_state = self.system_state
            self.system_state = SystemState.READY
            self._log_state_transition(old_state.value, "READY")
        elif self.system_state == SystemState.OVERLOADED and len(self.raw_results) < self.config.max_raw_results:
            # Recovery from overload
            old_state = self.system_state
            self.system_state = SystemState.PROCESSING
            self._log_state_transition(old_state.value, "PROCESSING")
    
    async def shutdown(self) -> None:
        """
        Shutdown the system gracefully.
        Corresponds to ShutdownSystem action in TLA+.
        """
        old_state = self.system_state
        self.system_state = SystemState.SHUTDOWN
        
        # Calculate uptime
        if self._start_time:
            self.metrics.uptime_seconds = (datetime.utcnow() - self._start_time).total_seconds()
        
        self._log_state_transition(old_state.value, "SHUTDOWN")
        self.logger.info(f"System shutdown complete. Uptime: {self.metrics.uptime_seconds:.3f}s")
    
    def get_status(self) -> Dict[str, Any]:
        """Get current system status."""
        return {
            "system_state": self.system_state.value,
            "raw_results_count": len(self.raw_results),
            "processed_results_count": len(self.processed_results),
            "metrics": self.metrics.model_dump(),
            "processing_records": {
                result_id: {
                    "current_state": record.current_state.value,
                    "retry_count": record.retry_count,
                    "error_count": len(record.error_history)
                }
                for result_id, record in self.processing_records.items()
            }
        }
    
    def is_healthy(self) -> bool:
        """Check if the agent is healthy."""
        return self.system_state in [SystemState.READY, SystemState.PROCESSING]
    
    async def stop(self) -> None:
        """
        Stop the agent gracefully.
        Corresponds to Stop action in TLA+.
        """
        if self.system_state == SystemState.SHUTDOWN:
            return
        
        self.logger.info("Stopping Result Processing Agent...")
        
        # Wait for any ongoing processing to complete
        if self.system_state == SystemState.PROCESSING:
            self.logger.info("Waiting for processing to complete...")
            while self.system_state == SystemState.PROCESSING:
                await asyncio.sleep(0.1)
        
        self.system_state = SystemState.SHUTDOWN
        self._log_state_transition(str(self.system_state), "SHUTDOWN")
        
        self.logger.info("Result Processing Agent stopped successfully")
    
    # Processing handlers for different formats
    
    async def _process_json_result(self, raw_result: RawResult) -> ProcessedResult:
        """Process JSON format result."""
        if isinstance(raw_result.raw_data, dict):
            structured_data = raw_result.raw_data
        else:
            structured_data = json.loads(raw_result.raw_data)
        
        return ProcessedResult(
            raw_result_id=raw_result.id,
            structured_data=structured_data,
            quality_metrics={"format_score": 1.0},
            processing_metadata={
                "format": "JSON",
                "processing_time_ms": 0.1,
                "instrument_id": raw_result.instrument_id
            }
        )
    
    async def _process_csv_result(self, raw_result: RawResult) -> ProcessedResult:
        """Process CSV format result."""
        if not raw_result.raw_data:
            structured_data = {}
        else:
            # Simple CSV parsing
            reader = csv.DictReader(io.StringIO(raw_result.raw_data))
            rows = list(reader)
            if rows:
                structured_data = rows[0]  # Take first row for simplicity
            else:
                structured_data = {}
        
        return ProcessedResult(
            raw_result_id=raw_result.id,
            structured_data=structured_data,
            quality_metrics={"format_score": 0.9},
            processing_metadata={
                "format": "CSV",
                "processing_time_ms": 0.2,
                "instrument_id": raw_result.instrument_id
            }
        )
    
    async def _process_xml_result(self, raw_result: RawResult) -> ProcessedResult:
        """Process XML format result."""
        # Basic XML handling (in production would use proper XML parser)
        structured_data = {
            "xml_content": raw_result.raw_data,
            "format": "XML"
        }
        
        return ProcessedResult(
            raw_result_id=raw_result.id,
            structured_data=structured_data,
            quality_metrics={"format_score": 0.8},
            processing_metadata={
                "format": "XML",
                "processing_time_ms": 0.3,
                "instrument_id": raw_result.instrument_id
            }
        )
    
    async def _process_hl7_result(self, raw_result: RawResult) -> ProcessedResult:
        """Process HL7 format result."""
        # Basic HL7 handling (in production would use HL7 parser)
        structured_data = {
            "hl7_content": raw_result.raw_data,
            "format": "HL7"
        }
        
        return ProcessedResult(
            raw_result_id=raw_result.id,
            structured_data=structured_data,
            quality_metrics={"format_score": 0.95},
            processing_metadata={
                "format": "HL7",
                "processing_time_ms": 0.4,
                "instrument_id": raw_result.instrument_id
            }
        )
    
    # Utility methods
    
    def _log_state_transition(self, from_state: str, to_state: str) -> None:
        """Log state transitions."""
        self.logger.info(f"State transition: {from_state} -> {to_state}")
    
    def _update_average_processing_time(self, processing_time_ms: float) -> None:
        """Update average processing time metric."""
        if self.metrics.total_results_processed == 1:
            self.metrics.average_processing_time_ms = processing_time_ms
        else:
            # Running average calculation
            n = self.metrics.total_results_processed
            current_avg = self.metrics.average_processing_time_ms
            self.metrics.average_processing_time_ms = ((current_avg * (n - 1)) + processing_time_ms) / n
    
    def _verify_invariants(self) -> None:
        """Verify TLA+ invariants are maintained."""
        # CapacityLimits: never exceed queue limits
        assert len(self.raw_results) <= self.config.max_raw_results, "Raw results capacity exceeded"
        assert len(self.processed_results) <= self.config.max_processed_results, "Processed results capacity exceeded"
        
        # BoundedRetries: retry count never exceeds maximum
        for record in self.processing_records.values():
            assert record.retry_count <= self.config.max_retries, f"Retry count {record.retry_count} exceeds maximum {self.config.max_retries}"
        
        # StateConsistency: processing records exist for all raw results
        for raw_result in self.raw_results:
            assert raw_result.id in self.processing_records, f"Missing processing record for {raw_result.id}"
