"""
Sample QC Review Agent Implementation

This module implements the Sample QC Review Agent following the validated TLA+ specification.
It handles the quality control review process for laboratory samples, ensuring strict
compliance with the formal model and safety properties.

TLA+ Specification: plans/feature-20250711-sample-qc-review/tla/SampleQCReviewAgent.tla
Validation Results: plans/feature-20250711-sample-qc-review/tla-validation-results.md
"""

import logging
from dataclasses import dataclass
from datetime import datetime
from enum import Enum
from typing import Dict, List, Optional, Set

from backend.app.core.agents.base_agent import BaseAgent
from backend.app.core.events import EventBus, Event


class QCDecision(Enum):
    """QC Review decisions matching TLA+ model"""
    APPROVED = "APPROVED"
    REJECTED = "REJECTED"
    ESCALATED = "ESCALATED"


class QCState(Enum):
    """Sample QC states matching TLA+ model"""
    PENDING = "QC_PENDING"
    IN_REVIEW = "QC_IN_REVIEW"
    APPROVED = "QC_APPROVED"
    REJECTED = "QC_REJECTED"
    ESCALATED = "QC_ESCALATED"


@dataclass
class QCDecisionRecord:
    """QC decision record matching TLA+ model"""
    sample_id: str
    decision: QCDecision
    reviewer_id: str
    timestamp: datetime
    reason: Optional[str] = None


@dataclass
class AuditTrailEntry:
    """Audit trail entry matching TLA+ model"""
    sample_id: str
    action: str
    timestamp: datetime
    details: Optional[Dict] = None


@dataclass
class SampleResult:
    """Sample result data matching TLA+ model"""
    value: float
    critical: bool
    reference_min: float = 4.0
    reference_max: float = 12.0


class SampleQCReviewAgent(BaseAgent):
    """
    Sample QC Review Agent Implementation

    Implements the QC review workflow following the validated TLA+ specification:
    - Receives samples for QC review
    - Assigns reviewers based on workload
    - Processes QC decisions (approve/reject/escalate)
    - Maintains audit trail and decision records
    - Enforces safety properties and invariants
    """

    def __init__(self, event_bus: EventBus, max_samples: int = 10, max_reviewers: int = 5):
        super().__init__(
            agent_id="sample-qc-review-agent",
            name="Sample QC Review Agent",
            event_bus=event_bus
        )

        # TLA+ model constants
        self.max_samples = max_samples
        self.max_reviewers = max_reviewers
        self.max_workload_per_reviewer = 3

        # TLA+ model variables
        self.qc_queue: List[str] = []
        self.qc_in_review: Set[str] = set()
        self.qc_approved: Set[str] = set()
        self.qc_rejected: Set[str] = set()
        self.qc_escalated: Set[str] = set()
        self.sample_results: Dict[str, SampleResult] = {}
        self.reviewer_assignments: Dict[str, str] = {}
        self.reviewer_workload: Dict[str, int] = {}
        self.qc_decisions: List[QCDecisionRecord] = []
        self.audit_trail: List[AuditTrailEntry] = []

        # Initialize reviewer workload
        for i in range(1, max_reviewers + 1):
            self.reviewer_workload[f"reviewer_{i}"] = 0

        self.logger = logging.getLogger(__name__)

    async def initialize(self) -> None:
        """Initialize the agent and subscribe to events"""
        await super().initialize()

        # Subscribe to sample events
        await self.event_bus.subscribe("sample.qc_required", self.handle_sample_qc_required)
        await self.event_bus.subscribe("qc.reviewer_assigned", self.handle_reviewer_assigned)
        await self.event_bus.subscribe("qc.review_completed", self.handle_review_completed)

        self.logger.info("Sample QC Review Agent initialized")

    # TLA+ Action: ReceiveForQCReview
    async def receive_for_qc_review(self, sample_id: str, value: float, critical: bool) -> bool:
        """
        Receive a sample for QC review - implements TLA+ ReceiveForQCReview action

        TLA+ Preconditions:
        - sample_id not in processed samples
        - queue length < max_samples

        TLA+ Postconditions:
        - sample added to queue
        - sample_results updated
        - audit trail entry created
        """
        try:
            # Check TLA+ preconditions
            if sample_id in (self.qc_approved | self.qc_rejected | self.qc_escalated):
                self.logger.warning(f"Sample {sample_id} already processed, skipping")
                return False

            if len(self.qc_queue) >= self.max_samples:
                self.logger.warning(f"QC queue full ({self.max_samples}), cannot accept sample {sample_id}")
                return False

            # Update TLA+ variables
            self.qc_queue.append(sample_id)
            self.sample_results[sample_id] = SampleResult(value=value, critical=critical)

            # Add audit trail entry
            audit_entry = AuditTrailEntry(
                sample_id=sample_id,
                action="RECEIVED_FOR_QC",
                timestamp=datetime.now()
            )
            self.audit_trail.append(audit_entry)

            self.logger.info(f"Sample {sample_id} received for QC review (value={value}, critical={critical})")

            # Publish event for next step
            await self.event_bus.publish(Event(
                event_type="qc.sample_received",
                data={"sample_id": sample_id, "value": value, "critical": critical}
            ))

            return True

        except Exception as e:
            self.logger.error(f"Error receiving sample {sample_id} for QC review: {e}")
            return False

    # TLA+ Action: AssignReviewer
    async def assign_reviewer(self, sample_id: str, reviewer_id: str) -> bool:
        """
        Assign a reviewer to a sample - implements TLA+ AssignReviewer action

        TLA+ Preconditions:
        - sample has no assigned reviewer
        - reviewer exists and has capacity

        TLA+ Postconditions:
        - reviewer assigned to sample
        - reviewer workload increased
        - audit trail entry created
        """
        try:
            # Check TLA+ preconditions
            if sample_id in self.reviewer_assignments:
                self.logger.warning(f"Sample {sample_id} already has assigned reviewer")
                return False

            if reviewer_id not in self.reviewer_workload:
                self.logger.warning(f"Reviewer {reviewer_id} not found")
                return False

            if self.reviewer_workload[reviewer_id] >= self.max_workload_per_reviewer:
                self.logger.warning(f"Reviewer {reviewer_id} at maximum workload")
                return False

            # Update TLA+ variables
            self.reviewer_assignments[sample_id] = reviewer_id
            self.reviewer_workload[reviewer_id] += 1

            # Add audit trail entry
            audit_entry = AuditTrailEntry(
                sample_id=sample_id,
                action="REVIEWER_ASSIGNED",
                timestamp=datetime.now(),
                details={"reviewer_id": reviewer_id}
            )
            self.audit_trail.append(audit_entry)

            self.logger.info(f"Reviewer {reviewer_id} assigned to sample {sample_id}")

            # Publish event
            await self.event_bus.publish(Event(
                event_type="qc.reviewer_assigned",
                data={"sample_id": sample_id, "reviewer_id": reviewer_id}
            ))

            return True

        except Exception as e:
            self.logger.error(f"Error assigning reviewer {reviewer_id} to sample {sample_id}: {e}")
            return False

    # TLA+ Action: StartQCReview
    async def start_qc_review(self, sample_id: str) -> bool:
        """
        Start QC review for a sample - implements TLA+ StartQCReview action

        TLA+ Preconditions:
        - sample has assigned reviewer
        - sample not already in review

        TLA+ Postconditions:
        - sample moved to in_review state
        - sample removed from queue
        - audit trail entry created
        """
        try:
            # Check TLA+ preconditions
            if sample_id not in self.reviewer_assignments:
                self.logger.warning(f"Sample {sample_id} has no assigned reviewer")
                return False

            if sample_id in self.qc_in_review:
                self.logger.warning(f"Sample {sample_id} already in review")
                return False

            if sample_id not in self.qc_queue:
                self.logger.warning(f"Sample {sample_id} not in queue")
                return False

            # Update TLA+ variables
            self.qc_in_review.add(sample_id)
            self.qc_queue.remove(sample_id)

            # Add audit trail entry
            audit_entry = AuditTrailEntry(
                sample_id=sample_id,
                action="QC_REVIEW_STARTED",
                timestamp=datetime.now()
            )
            self.audit_trail.append(audit_entry)

            self.logger.info(f"QC review started for sample {sample_id}")

            # Publish event
            await self.event_bus.publish(Event(
                event_type="qc.review_started",
                data={"sample_id": sample_id}
            ))

            return True

        except Exception as e:
            self.logger.error(f"Error starting QC review for sample {sample_id}: {e}")
            return False

    # TLA+ Helper Functions
    def has_critical_values(self, sample_id: str) -> bool:
        """Check if sample has critical values - implements TLA+ HasCriticalValues"""
        if sample_id not in self.sample_results:
            return False
        return self.sample_results[sample_id].critical

    def within_reference_range(self, sample_id: str) -> bool:
        """Check if sample is within reference range - implements TLA+ WithinReferenceRange"""
        if sample_id not in self.sample_results:
            return False
        result = self.sample_results[sample_id]
        return result.reference_min <= result.value <= result.reference_max

    def requires_escalation(self, sample_id: str) -> bool:
        """Check if sample requires escalation - implements TLA+ RequiresEscalation"""
        return self.has_critical_values(sample_id) or not self.within_reference_range(sample_id)

    # TLA+ Action: ApproveQCReview
    async def approve_qc_review(self, sample_id: str, reviewer_id: str, reason: Optional[str] = None) -> bool:
        """
        Approve QC review - implements TLA+ ApproveQCReview action

        TLA+ Preconditions:
        - sample in review
        - within reference range
        - not critical values

        TLA+ Postconditions:
        - sample moved to approved state
        - reviewer workload decreased
        - decision and audit trail recorded
        """
        try:
            # Check TLA+ preconditions
            if sample_id not in self.qc_in_review:
                self.logger.warning(f"Sample {sample_id} not in review")
                return False

            if not self.within_reference_range(sample_id):
                self.logger.warning(f"Sample {sample_id} not within reference range, cannot approve")
                return False

            if self.has_critical_values(sample_id):
                self.logger.warning(f"Sample {sample_id} has critical values, cannot approve")
                return False

            # Update TLA+ variables
            self.qc_in_review.remove(sample_id)
            self.qc_approved.add(sample_id)

            # Decrease reviewer workload
            assigned_reviewer = self.reviewer_assignments[sample_id]
            self.reviewer_workload[assigned_reviewer] -= 1

            # Record decision
            decision = QCDecisionRecord(
                sample_id=sample_id,
                decision=QCDecision.APPROVED,
                reviewer_id=reviewer_id,
                timestamp=datetime.now(),
                reason=reason
            )
            self.qc_decisions.append(decision)

            # Add audit trail entry
            audit_entry = AuditTrailEntry(
                sample_id=sample_id,
                action="QC_APPROVED",
                timestamp=datetime.now(),
                details={"reviewer_id": reviewer_id, "reason": reason}
            )
            self.audit_trail.append(audit_entry)

            self.logger.info(f"Sample {sample_id} approved by reviewer {reviewer_id}")

            # Publish event
            await self.event_bus.publish(Event(
                event_type="qc.sample_approved",
                data={"sample_id": sample_id, "reviewer_id": reviewer_id}
            ))

            return True

        except Exception as e:
            self.logger.error(f"Error approving sample {sample_id}: {e}")
            return False

    # TLA+ Action: RejectQCReview
    async def reject_qc_review(self, sample_id: str, reviewer_id: str, reason: Optional[str] = None) -> bool:
        """
        Reject QC review - implements TLA+ RejectQCReview action

        TLA+ Preconditions:
        - sample in review
        - not within reference range
        - not critical values

        TLA+ Postconditions:
        - sample moved to rejected state
        - reviewer workload decreased
        - decision and audit trail recorded
        """
        try:
            # Check TLA+ preconditions
            if sample_id not in self.qc_in_review:
                self.logger.warning(f"Sample {sample_id} not in review")
                return False

            if self.within_reference_range(sample_id):
                self.logger.warning(f"Sample {sample_id} within reference range, should approve not reject")
                return False

            if self.has_critical_values(sample_id):
                self.logger.warning(f"Sample {sample_id} has critical values, should escalate not reject")
                return False

            # Update TLA+ variables
            self.qc_in_review.remove(sample_id)
            self.qc_rejected.add(sample_id)

            # Decrease reviewer workload
            assigned_reviewer = self.reviewer_assignments[sample_id]
            self.reviewer_workload[assigned_reviewer] -= 1

            # Record decision
            decision = QCDecisionRecord(
                sample_id=sample_id,
                decision=QCDecision.REJECTED,
                reviewer_id=reviewer_id,
                timestamp=datetime.now(),
                reason=reason
            )
            self.qc_decisions.append(decision)

            # Add audit trail entry
            audit_entry = AuditTrailEntry(
                sample_id=sample_id,
                action="QC_REJECTED",
                timestamp=datetime.now(),
                details={"reviewer_id": reviewer_id, "reason": reason}
            )
            self.audit_trail.append(audit_entry)

            self.logger.info(f"Sample {sample_id} rejected by reviewer {reviewer_id}")

            # Publish event
            await self.event_bus.publish(Event(
                event_type="qc.sample_rejected",
                data={"sample_id": sample_id, "reviewer_id": reviewer_id}
            ))

            return True

        except Exception as e:
            self.logger.error(f"Error rejecting sample {sample_id}: {e}")
            return False

    # TLA+ Action: EscalateQCReview
    async def escalate_qc_review(self, sample_id: str, reviewer_id: str, reason: Optional[str] = None) -> bool:
        """
        Escalate QC review - implements TLA+ EscalateQCReview action

        TLA+ Preconditions:
        - sample in review
        - requires escalation (critical values or out of range)

        TLA+ Postconditions:
        - sample moved to escalated state
        - reviewer workload decreased
        - decision and audit trail recorded
        """
        try:
            # Check TLA+ preconditions
            if sample_id not in self.qc_in_review:
                self.logger.warning(f"Sample {sample_id} not in review")
                return False

            if not self.requires_escalation(sample_id):
                self.logger.warning(f"Sample {sample_id} does not require escalation")
                return False

            # Update TLA+ variables
            self.qc_in_review.remove(sample_id)
            self.qc_escalated.add(sample_id)

            # Decrease reviewer workload
            assigned_reviewer = self.reviewer_assignments[sample_id]
            self.reviewer_workload[assigned_reviewer] -= 1

            # Record decision
            decision = QCDecisionRecord(
                sample_id=sample_id,
                decision=QCDecision.ESCALATED,
                reviewer_id=reviewer_id,
                timestamp=datetime.now(),
                reason=reason
            )
            self.qc_decisions.append(decision)

            # Add audit trail entry
            audit_entry = AuditTrailEntry(
                sample_id=sample_id,
                action="QC_ESCALATED",
                timestamp=datetime.now(),
                details={"reviewer_id": reviewer_id, "reason": reason}
            )
            self.audit_trail.append(audit_entry)

            self.logger.info(f"Sample {sample_id} escalated by reviewer {reviewer_id}")

            # Publish event
            await self.event_bus.publish(Event(
                event_type="qc.sample_escalated",
                data={"sample_id": sample_id, "reviewer_id": reviewer_id}
            ))

            return True

        except Exception as e:
            self.logger.error(f"Error escalating sample {sample_id}: {e}")
            return False

    async def handle_event(self, event: Event) -> None:
        """Handle incoming events - required by BaseAgent"""
        # Route to specific handlers based on event type
        if event.event_type == "sample.qc_required":
            await self.handle_sample_qc_required(event)
        elif event.event_type == "qc.reviewer_assigned":
            await self.handle_reviewer_assigned(event)
        elif event.event_type == "qc.review_completed":
            await self.handle_review_completed(event)

    # Event Handlers
    async def handle_sample_qc_required(self, event: Event) -> None:
        """Handle sample QC required event"""
        try:
            sample_id = event.data.get("sample_id")
            value = event.data.get("value", 0.0)
            critical = event.data.get("critical", False)

            await self.receive_for_qc_review(sample_id, value, critical)

            # Auto-assign reviewer if available
            available_reviewer = self.find_available_reviewer()
            if available_reviewer:
                await self.assign_reviewer(sample_id, available_reviewer)
                await self.start_qc_review(sample_id)

        except Exception as e:
            self.logger.error(f"Error handling sample QC required event: {e}")

    async def handle_reviewer_assigned(self, event: Event) -> None:
        """Handle reviewer assigned event"""
        try:
            sample_id = event.data.get("sample_id")
            if sample_id in self.qc_queue:
                await self.start_qc_review(sample_id)
        except Exception as e:
            self.logger.error(f"Error handling reviewer assigned event: {e}")

    async def handle_review_completed(self, event: Event) -> None:
        """Handle review completed event"""
        try:
            sample_id = event.data.get("sample_id")
            reviewer_id = event.data.get("reviewer_id")
            decision = event.data.get("decision")
            reason = event.data.get("reason")

            if decision == "APPROVED":
                await self.approve_qc_review(sample_id, reviewer_id, reason)
            elif decision == "REJECTED":
                await self.reject_qc_review(sample_id, reviewer_id, reason)
            elif decision == "ESCALATED":
                await self.escalate_qc_review(sample_id, reviewer_id, reason)

        except Exception as e:
            self.logger.error(f"Error handling review completed event: {e}")

    # Helper Methods
    def find_available_reviewer(self) -> Optional[str]:
        """Find reviewer with lowest workload"""
        min_workload = float('inf')
        available_reviewer = None

        for reviewer_id, workload in self.reviewer_workload.items():
            if workload < self.max_workload_per_reviewer and workload < min_workload:
                min_workload = workload
                available_reviewer = reviewer_id

        return available_reviewer

    def get_status(self) -> Dict:
        """Get current agent status"""
        return {
            "queue_length": len(self.qc_queue),
            "in_review": len(self.qc_in_review),
            "approved": len(self.qc_approved),
            "rejected": len(self.qc_rejected),
            "escalated": len(self.qc_escalated),
            "reviewer_workload": self.reviewer_workload.copy(),
            "total_decisions": len(self.qc_decisions),
            "audit_entries": len(self.audit_trail)
        }

    # TLA+ Invariant Checking (for testing)
    def check_invariants(self) -> Dict[str, bool]:
        """Check TLA+ invariants - for testing and validation"""
        invariants = {}

        # MutualExclusion - samples in at most one state
        all_samples: Set[str] = set()
        overlaps = []
        for state_set in [self.qc_in_review, self.qc_approved, self.qc_rejected, self.qc_escalated]:
            if all_samples & state_set:
                overlaps.append(all_samples & state_set)
            all_samples |= state_set
        invariants["MutualExclusion"] = len(overlaps) == 0

        # WorkloadLimits - reviewer workload <= max
        invariants["WorkloadLimits"] = all(
            workload <= self.max_workload_per_reviewer
            for workload in self.reviewer_workload.values()
        )

        # QueueLengthLimit
        invariants["QueueLengthLimit"] = len(self.qc_queue) <= self.max_samples

        # ReviewerAssignmentRequired - samples in review have assigned reviewers
        invariants["ReviewerAssignmentRequired"] = all(
            sample_id in self.reviewer_assignments
            for sample_id in self.qc_in_review
        )

        # CriticalValuesEscalated - critical samples properly handled
        critical_samples_ok = True
        for sample_id, result in self.sample_results.items():
            if result.critical:
                in_queue = sample_id in self.qc_queue
                in_review = sample_id in self.qc_in_review
                escalated = sample_id in self.qc_escalated
                if not (in_queue or in_review or escalated):
                    critical_samples_ok = False
                    break
        invariants["CriticalValuesEscalated"] = critical_samples_ok

        return invariants
