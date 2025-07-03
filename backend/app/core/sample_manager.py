"""
ALIMS Sample Manager
Core component for laboratory sample lifecycle management
"""

import asyncio
import logging
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
from enum import Enum
import uuid


class SampleStatus(Enum):
    """Sample status throughout its lifecycle"""
    RECEIVED = "received"
    REGISTERED = "registered"
    IN_QUEUE = "in_queue"
    IN_PROGRESS = "in_progress"
    ANALYZED = "analyzed"
    REVIEWED = "reviewed"
    APPROVED = "approved"
    COMPLETED = "completed"
    DISPOSED = "disposed"
    ON_HOLD = "on_hold"


class SampleType(Enum):
    """Types of laboratory samples"""
    PHARMACEUTICAL = "pharmaceutical"
    ENVIRONMENTAL = "environmental"
    FOOD_BEVERAGE = "food_beverage"
    CLINICAL = "clinical"
    RESEARCH = "research"
    QC_SAMPLE = "qc_sample"
    BLANK = "blank"
    STANDARD = "standard"


@dataclass
class Sample:
    """Laboratory sample entity"""
    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    barcode: Optional[str] = None
    sample_type: SampleType = SampleType.RESEARCH
    status: SampleStatus = SampleStatus.RECEIVED
    location: Optional[str] = None
    description: Optional[str] = None
    
    # Dates and timing
    received_date: datetime = field(default_factory=datetime.now)
    due_date: Optional[datetime] = None
    completed_date: Optional[datetime] = None
    
    # Sample metadata
    submitter: Optional[str] = None
    project_id: Optional[str] = None
    priority: int = 5  # 1-10 scale, 10 = highest
    
    # Laboratory data
    container_type: Optional[str] = None
    volume: Optional[float] = None
    volume_unit: str = "mL"
    storage_conditions: Optional[str] = None
    
    # Chain of custody
    custody_chain: List[Dict[str, Any]] = field(default_factory=list)
    
    # Test requirements
    requested_tests: List[str] = field(default_factory=list)
    completed_tests: List[str] = field(default_factory=list)
    
    # Quality control
    qc_flags: List[str] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)


class SampleManager:
    """
    Core sample management system for ALIMS
    
    Handles sample lifecycle from intake to disposal with full
    chain of custody tracking and regulatory compliance.
    """
    
    def __init__(self, config: Dict[str, Any]):
        self.logger = logging.getLogger("SampleManager")
        self.config = config
        
        # Sample storage
        self.samples: Dict[str, Sample] = {}
        self.samples_by_barcode: Dict[str, str] = {}  # barcode -> sample_id
        
        # Configuration
        self.max_samples = config.get('max_samples', 1000)
        self.default_retention_days = config.get('retention_days', 2555)  # 7 years
        
        # Statistics
        self.total_received = 0
        self.total_completed = 0
        
        self.logger.info("Sample Manager initialized")
    
    async def register_sample(self, 
                            sample_data: Dict[str, Any]) -> Sample:
        """Register a new sample in the system"""
        try:
            # Create sample from provided data
            sample = Sample(
                sample_type=SampleType(sample_data.get('type', 'research')),
                description=sample_data.get('description', ''),
                submitter=sample_data.get('submitter', ''),
                project_id=sample_data.get('project_id', ''),
                priority=sample_data.get('priority', 5),
                container_type=sample_data.get('container_type', ''),
                volume=sample_data.get('volume'),
                volume_unit=sample_data.get('volume_unit', 'mL'),
                storage_conditions=sample_data.get('storage_conditions', ''),
                requested_tests=sample_data.get('tests', [])
            )
            
            # Generate barcode if not provided
            if 'barcode' in sample_data:
                sample.barcode = sample_data['barcode']
            else:
                sample.barcode = self._generate_barcode(sample)
            
            # Set due date if not provided
            if 'due_date' in sample_data:
                sample.due_date = sample_data['due_date']
            else:
                sample.due_date = sample.received_date + timedelta(days=30)
            
            # Add to custody chain
            self._add_custody_entry(sample, "REGISTERED", "Sample registered in ALIMS")
            
            # Store sample
            self.samples[sample.id] = sample
            self.samples_by_barcode[sample.barcode] = sample.id
            
            # Update statistics
            self.total_received += 1
            
            # Update status
            sample.status = SampleStatus.REGISTERED
            
            self.logger.info(f"Sample registered: {sample.id} ({sample.barcode})")
            
            return sample
            
        except Exception as e:
            self.logger.error(f"Error registering sample: {e}")
            raise
    
    async def get_sample(self, 
                        identifier: str) -> Optional[Sample]:
        """Get sample by ID or barcode"""
        # Try by ID first
        if identifier in self.samples:
            return self.samples[identifier]
        
        # Try by barcode
        if identifier in self.samples_by_barcode:
            sample_id = self.samples_by_barcode[identifier]
            return self.samples[sample_id]
        
        return None
    
    async def update_sample_status(self, 
                                 sample_id: str, 
                                 new_status: SampleStatus,
                                 operator: str = "system",
                                 notes: str = "") -> bool:
        """Update sample status with custody tracking"""
        sample = await self.get_sample(sample_id)
        if not sample:
            return False
        
        old_status = sample.status
        sample.status = new_status
        
        # Add custody entry
        self._add_custody_entry(
            sample, 
            f"STATUS_CHANGE", 
            f"Status changed from {old_status.value} to {new_status.value}",
            operator,
            notes
        )
        
        # Update completion date if completed
        if new_status == SampleStatus.COMPLETED:
            sample.completed_date = datetime.now()
            self.total_completed += 1
        
        self.logger.info(f"Sample {sample_id} status updated: {old_status.value} → {new_status.value}")
        
        return True
    
    async def add_test_result(self, 
                            sample_id: str,
                            test_name: str,
                            result_data: Dict[str, Any],
                            analyst: str) -> bool:
        """Add test result to sample"""
        sample = await self.get_sample(sample_id)
        if not sample:
            return False
        
        # Mark test as completed
        if test_name not in sample.completed_tests:
            sample.completed_tests.append(test_name)
        
        # Add custody entry
        self._add_custody_entry(
            sample,
            "TEST_COMPLETED",
            f"Test '{test_name}' completed by {analyst}",
            analyst
        )
        
        # Check if all tests are complete
        if set(sample.requested_tests).issubset(set(sample.completed_tests)):
            await self.update_sample_status(sample_id, SampleStatus.ANALYZED, analyst)
        
        self.logger.info(f"Test result added for sample {sample_id}: {test_name}")
        
        return True
    
    async def get_samples_by_status(self, 
                                  status: SampleStatus) -> List[Sample]:
        """Get all samples with specific status"""
        return [sample for sample in self.samples.values() 
                if sample.status == status]
    
    async def get_overdue_samples(self) -> List[Sample]:
        """Get samples that are past their due date"""
        now = datetime.now()
        return [sample for sample in self.samples.values()
                if sample.due_date and sample.due_date < now
                and sample.status not in [SampleStatus.COMPLETED, SampleStatus.DISPOSED]]
    
    async def get_high_priority_samples(self) -> List[Sample]:
        """Get high priority samples (priority >= 8)"""
        return [sample for sample in self.samples.values()
                if sample.priority >= 8
                and sample.status not in [SampleStatus.COMPLETED, SampleStatus.DISPOSED]]
    
    def _generate_barcode(self, sample: Sample) -> str:
        """Generate unique barcode for sample"""
        timestamp = datetime.now().strftime("%Y%m%d")
        sequence = str(len(self.samples) + 1).zfill(4)
        type_code = sample.sample_type.value[:3].upper()
        return f"ALIMS-{type_code}-{timestamp}-{sequence}"
    
    def _add_custody_entry(self, 
                          sample: Sample,
                          action: str,
                          description: str,
                          operator: str = "system",
                          notes: str = "") -> None:
        """Add entry to sample custody chain"""
        entry = {
            "timestamp": datetime.now().isoformat(),
            "action": action,
            "description": description,
            "operator": operator,
            "notes": notes
        }
        sample.custody_chain.append(entry)
    
    async def get_statistics(self) -> Dict[str, Any]:
        """Get sample management statistics"""
        active_samples = len([s for s in self.samples.values() 
                            if s.status not in [SampleStatus.COMPLETED, SampleStatus.DISPOSED]])
        
        overdue_count = len(await self.get_overdue_samples())
        high_priority_count = len(await self.get_high_priority_samples())
        
        return {
            "total_samples": len(self.samples),
            "active_samples": active_samples,
            "total_received": self.total_received,
            "total_completed": self.total_completed,
            "overdue_samples": overdue_count,
            "high_priority_samples": high_priority_count,
            "completion_rate": (self.total_completed / max(self.total_received, 1)) * 100
        }
    
    async def cleanup_old_samples(self) -> int:
        """Clean up old completed samples based on retention policy"""
        cutoff_date = datetime.now() - timedelta(days=self.default_retention_days)
        cleaned = 0
        
        to_remove = []
        for sample_id, sample in self.samples.items():
            if (sample.status == SampleStatus.DISPOSED and 
                sample.completed_date and 
                sample.completed_date < cutoff_date):
                to_remove.append(sample_id)
        
        for sample_id in to_remove:
            sample = self.samples[sample_id]
            if sample.barcode in self.samples_by_barcode:
                del self.samples_by_barcode[sample.barcode]
            del self.samples[sample_id]
            cleaned += 1
        
        if cleaned > 0:
            self.logger.info(f"Cleaned up {cleaned} old samples")
        
        return cleaned
    
    def is_healthy(self) -> bool:
        """Check if sample manager is operating within normal parameters"""
        return len(self.samples) < self.max_samples
