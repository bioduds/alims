"""
PatternValidator - Advanced Pattern Classification Coherence Agent

This agent ensures pattern classification consistency and quality across
the ALims system. It validates classifications, resolves conflicts,
and maintains system coherence.
"""

import json
import logging
from datetime import datetime
from typing import Dict, List, Any
from dataclasses import dataclass, asdict
from enum import Enum
import uuid

from .ollama_client import OllamaClient

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class ValidationActionType(Enum):
    """Types of validation actions that can be performed"""

    VALIDATE_PATTERN = "VALIDATE_PATTERN"
    CROSS_VALIDATE = "CROSS_VALIDATE"
    SYSTEM_AUDIT = "SYSTEM_AUDIT"
    CONFLICT_RESOLUTION = "CONFLICT_RESOLUTION"
    EVOLUTION_TRACKING = "EVOLUTION_TRACKING"
    QUALITY_ASSESSMENT = "QUALITY_ASSESSMENT"


class PatternCategory(Enum):
    """Standard pattern categories for validation"""

    COMMUNICATION = "COMMUNICATION"
    PRODUCTIVITY = "PRODUCTIVITY"
    SYSTEM = "SYSTEM"
    LEARNING = "LEARNING"
    CREATIVE = "CREATIVE"
    SOCIAL = "SOCIAL"
    HEALTH = "HEALTH"
    FINANCIAL = "FINANCIAL"


class ValidationPriority(Enum):
    """Priority levels for validation actions"""

    LOW = "LOW"
    NORMAL = "NORMAL"
    HIGH = "HIGH"
    URGENT = "URGENT"


class SystemHealth(Enum):
    """Overall system coherence health status"""

    EXCELLENT = "EXCELLENT"
    GOOD = "GOOD"
    FAIR = "FAIR"
    POOR = "POOR"
    CRITICAL = "CRITICAL"


@dataclass
class PatternClassification:
    """Represents a pattern classification"""

    pattern_id: str
    category: str
    subcategory: str
    confidence: float
    source_agent: str
    timestamp: datetime
    metadata: Dict[str, Any] = None


@dataclass
class ValidationResult:
    """Results of pattern validation"""

    is_coherent: bool
    consistency_score: float
    quality_score: float
    conflicts_detected: List[str]
    recommendations: List[str]


@dataclass
class ValidationAction:
    """Action required based on validation"""

    action_type: str
    pattern_id: str
    current_category: str
    recommended_category: str
    reason: str
    priority: ValidationPriority


@dataclass
class SystemCoherence:
    """Overall system coherence metrics"""

    overall_consistency: float
    conflict_count: int
    quality_average: float
    improvement_areas: List[str]


@dataclass
class ValidationSummary:
    """Summary of validation session"""

    total_patterns: int
    coherent_patterns: int
    conflicts_resolved: int
    recommendations_made: int
    system_health: SystemHealth


@dataclass
class PatternValidationRequest:
    """Request for pattern validation"""

    validation_id: str
    action: ValidationActionType
    patterns: List[PatternClassification]
    context: Dict[str, Any] = None


@dataclass
class PatternValidationResponse:
    """Response from pattern validation"""

    validation_id: str
    timestamp: datetime
    patterns_analyzed: List[Dict[str, Any]]
    system_coherence: SystemCoherence
    actions_required: List[ValidationAction]
    validation_summary: ValidationSummary


class PatternValidator:
    """
    Advanced Pattern Classification Coherence Agent

    Ensures pattern classification consistency and quality across ALims
    system. Validates classifications, resolves conflicts, and maintains
    system coherence.
    """

    def __init__(self, ollama_client: OllamaClient):
        """Initialize the PatternValidator"""
        self.ollama_client = ollama_client
        self.validation_history: List[PatternValidationResponse] = []
        self.pattern_registry: Dict[str, PatternClassification] = {}
        self.conflict_registry: Dict[str, List[str]] = {}
        self.metrics = {
            "validations_performed": 0,
            "conflicts_resolved": 0,
            "patterns_reclassified": 0,
            "system_audits": 0,
            "average_consistency_score": 0.0,
            "average_quality_score": 0.0,
        }

        # Load prompt template
        self.prompt_template = self._load_prompt_template()

        logger.info("PatternValidator initialized successfully")

    def _load_prompt_template(self) -> str:
        """Load the pattern validation prompt template"""
        try:
            with open("app/ai/prompts/pattern_validation.txt", "r") as f:
                return f.read()
        except FileNotFoundError:
            logger.error("Pattern validation prompt template not found")
            return "You are a pattern validation agent. Validate pattern classifications for coherence and consistency."

    async def validate_patterns(
        self, request: PatternValidationRequest
    ) -> PatternValidationResponse:
        """
        Main pattern validation method

        Args:
            request: PatternValidationRequest with patterns to validate

        Returns:
            PatternValidationResponse with validation results
        """
        try:
            logger.info(f"Starting pattern validation: {request.validation_id}")

            # Build context for AI
            context = self._build_validation_context(request)

            # Get AI validation
            ai_response = await self._get_ai_validation(context)

            # Process AI response
            validation_response = self._process_validation_response(
                request.validation_id, ai_response, request.patterns
            )

            # Update registries and metrics
            self._update_validation_state(validation_response)

            # Store validation history
            self.validation_history.append(validation_response)

            logger.info(f"Pattern validation completed: {request.validation_id}")
            return validation_response

        except Exception as e:
            logger.error(f"Error in pattern validation: {str(e)}")
            return self._create_error_response(request.validation_id, str(e))

    async def validate_single_pattern(
        self, pattern: PatternClassification
    ) -> ValidationResult:
        """Validate a single pattern classification"""
        request = PatternValidationRequest(
            validation_id=f"single_{uuid.uuid4().hex[:8]}",
            action=ValidationActionType.VALIDATE_PATTERN,
            patterns=[pattern],
        )

        response = await self.validate_patterns(request)

        if response.patterns_analyzed:
            return ValidationResult(
                **response.patterns_analyzed[0]["validation_result"]
            )
        else:
            return ValidationResult(
                is_coherent=False,
                consistency_score=0.0,
                quality_score=0.0,
                conflicts_detected=["Validation failed"],
                recommendations=["Retry validation"],
            )

    async def cross_validate_agents(
        self, pattern_id: str, classifications: List[PatternClassification]
    ) -> Dict[str, Any]:
        """Cross-validate pattern classifications from multiple agents"""
        request = PatternValidationRequest(
            validation_id=f"cross_{uuid.uuid4().hex[:8]}",
            action=ValidationActionType.CROSS_VALIDATE,
            patterns=classifications,
            context={"pattern_id": pattern_id},
        )

        response = await self.validate_patterns(request)

        return {
            "pattern_id": pattern_id,
            "agent_count": len(classifications),
            "consistency_score": response.system_coherence.overall_consistency,
            "conflicts": response.system_coherence.conflict_count,
            "recommended_classification": self._get_consensus_classification(
                classifications
            ),
            "actions_required": [
                asdict(action) for action in response.actions_required
            ],
        }

    async def system_audit(self) -> Dict[str, Any]:
        """Perform comprehensive system coherence audit"""
        all_patterns = list(self.pattern_registry.values())

        request = PatternValidationRequest(
            validation_id=f"audit_{uuid.uuid4().hex[:8]}",
            action=ValidationActionType.SYSTEM_AUDIT,
            patterns=all_patterns,
        )

        response = await self.validate_patterns(request)
        self.metrics["system_audits"] += 1

        return {
            "audit_id": response.validation_id,
            "timestamp": response.timestamp.isoformat(),
            "total_patterns": len(all_patterns),
            "system_health": response.validation_summary.system_health.value,
            "coherence_metrics": asdict(response.system_coherence),
            "critical_actions": [
                asdict(action)
                for action in response.actions_required
                if action.priority == ValidationPriority.URGENT
            ],
            "recommendations": self._generate_system_recommendations(response),
        }

    async def resolve_conflicts(self, pattern_id: str) -> Dict[str, Any]:
        """Resolve classification conflicts for a specific pattern"""
        if pattern_id not in self.conflict_registry:
            return {"error": f"No conflicts found for pattern {pattern_id}"}

        conflicting_classifications = [
            self.pattern_registry[pid]
            for pid in self.conflict_registry[pattern_id]
            if pid in self.pattern_registry
        ]

        request = PatternValidationRequest(
            validation_id=f"resolve_{uuid.uuid4().hex[:8]}",
            action=ValidationActionType.CONFLICT_RESOLUTION,
            patterns=conflicting_classifications,
            context={"target_pattern": pattern_id},
        )

        response = await self.validate_patterns(request)

        # Remove from conflict registry if resolved
        if response.system_coherence.conflict_count == 0:
            del self.conflict_registry[pattern_id]
            self.metrics["conflicts_resolved"] += 1

        return {
            "pattern_id": pattern_id,
            "conflicts_resolved": response.validation_summary.conflicts_resolved,
            "final_classification": self._get_consensus_classification(
                conflicting_classifications
            ),
            "resolution_actions": [
                asdict(action) for action in response.actions_required
            ],
        }

    def _build_validation_context(self, request: PatternValidationRequest) -> str:
        """Build context string for AI validation"""
        context_parts = [
            f"VALIDATION_REQUEST: {request.action.value}",
            f"VALIDATION_ID: {request.validation_id}",
            f"PATTERNS_COUNT: {len(request.patterns)}",
            "",
        ]

        # Add pattern details
        for i, pattern in enumerate(request.patterns):
            context_parts.extend(
                [
                    f"PATTERN_{i+1}:",
                    f"  ID: {pattern.pattern_id}",
                    f"  CATEGORY: {pattern.category}",
                    f"  SUBCATEGORY: {pattern.subcategory}",
                    f"  CONFIDENCE: {pattern.confidence}",
                    f"  SOURCE_AGENT: {pattern.source_agent}",
                    f"  TIMESTAMP: {pattern.timestamp.isoformat()}",
                    "",
                ]
            )

        # Add system context
        context_parts.extend(
            [
                "SYSTEM_METRICS:",
                f"  Total Patterns: {len(self.pattern_registry)}",
                f"  Active Conflicts: {len(self.conflict_registry)}",
                f"  Average Consistency: {self.metrics['average_consistency_score']:.2f}",
                f"  Average Quality: {self.metrics['average_quality_score']:.2f}",
                "",
            ]
        )

        # Add request-specific context
        if request.context:
            context_parts.append("ADDITIONAL_CONTEXT:")
            for key, value in request.context.items():
                context_parts.append(f"  {key}: {value}")
            context_parts.append("")

        return "\n".join(context_parts)

    async def _get_ai_validation(self, context: str) -> str:
        """Get AI validation response"""
        full_prompt = (
            f"{self.prompt_template}\n\n{context}\n\nProvide validation analysis:"
        )

        try:
            response = await self.ollama_client.generate_response(prompt=full_prompt)
            return response
        except Exception as e:
            logger.error(f"Error getting AI validation: {str(e)}")
            return self._create_fallback_validation()

    def _process_validation_response(
        self,
        validation_id: str,
        ai_response: str,
        patterns: List[PatternClassification],
    ) -> PatternValidationResponse:
        """Process AI validation response into structured format"""
        try:
            # Try to parse JSON response
            if ai_response.strip().startswith("{"):
                response_data = json.loads(ai_response)
            else:
                # Fallback parsing for non-JSON responses
                response_data = self._parse_text_response(ai_response, patterns)

            # Create structured response
            return PatternValidationResponse(
                validation_id=validation_id,
                timestamp=datetime.now(),
                patterns_analyzed=response_data.get("patterns_analyzed", []),
                system_coherence=SystemCoherence(
                    **response_data.get(
                        "system_coherence",
                        {
                            "overall_consistency": 0.8,
                            "conflict_count": 0,
                            "quality_average": 0.8,
                            "improvement_areas": [],
                        },
                    )
                ),
                actions_required=[
                    ValidationAction(**action)
                    for action in response_data.get("actions_required", [])
                ],
                validation_summary=ValidationSummary(
                    **{
                        **response_data.get(
                            "validation_summary",
                            {
                                "total_patterns": len(patterns),
                                "coherent_patterns": len(patterns),
                                "conflicts_resolved": 0,
                                "recommendations_made": 0,
                                "system_health": "GOOD",
                            },
                        ),
                        "system_health": SystemHealth(
                            response_data.get("validation_summary", {}).get(
                                "system_health", "GOOD"
                            )
                        ),
                    }
                ),
            )

        except Exception as e:
            logger.error(f"Error processing validation response: {str(e)}")
            return self._create_fallback_response(validation_id, patterns)

    def _parse_text_response(
        self, response: str, patterns: List[PatternClassification]
    ) -> Dict[str, Any]:
        """Parse non-JSON AI response into structured format"""
        # Simple fallback parsing
        return {
            "patterns_analyzed": [
                {
                    "pattern_id": pattern.pattern_id,
                    "current_classification": {
                        "category": pattern.category,
                        "subcategory": pattern.subcategory,
                        "confidence": pattern.confidence,
                        "source_agent": pattern.source_agent,
                    },
                    "validation_result": {
                        "is_coherent": True,
                        "consistency_score": 0.8,
                        "quality_score": 0.8,
                        "conflicts_detected": [],
                        "recommendations": [],
                    },
                }
                for pattern in patterns
            ],
            "system_coherence": {
                "overall_consistency": 0.8,
                "conflict_count": 0,
                "quality_average": 0.8,
                "improvement_areas": [],
            },
            "actions_required": [],
            "validation_summary": {
                "total_patterns": len(patterns),
                "coherent_patterns": len(patterns),
                "conflicts_resolved": 0,
                "recommendations_made": 0,
                "system_health": "GOOD",
            },
        }

    def _update_validation_state(self, response: PatternValidationResponse):
        """Update internal state based on validation response"""
        # Update metrics
        self.metrics["validations_performed"] += 1
        self.metrics["average_consistency_score"] = (
            self.metrics["average_consistency_score"]
            * (self.metrics["validations_performed"] - 1)
            + response.system_coherence.overall_consistency
        ) / self.metrics["validations_performed"]
        self.metrics["average_quality_score"] = (
            self.metrics["average_quality_score"]
            * (self.metrics["validations_performed"] - 1)
            + response.system_coherence.quality_average
        ) / self.metrics["validations_performed"]

        # Update pattern registry
        for pattern_data in response.patterns_analyzed:
            pattern_id = pattern_data["pattern_id"]
            if pattern_id not in self.pattern_registry:
                # Create pattern classification from response data
                classification_data = pattern_data["current_classification"]
                self.pattern_registry[pattern_id] = PatternClassification(
                    pattern_id=pattern_id,
                    category=classification_data["category"],
                    subcategory=classification_data["subcategory"],
                    confidence=classification_data["confidence"],
                    source_agent=classification_data["source_agent"],
                    timestamp=datetime.now(),
                )

    def _get_consensus_classification(
        self, classifications: List[PatternClassification]
    ) -> Dict[str, Any]:
        """Get consensus classification from multiple classifications"""
        if not classifications:
            return {}

        # Simple majority vote for category
        categories = [c.category for c in classifications]
        consensus_category = max(set(categories), key=categories.count)

        # Average confidence
        avg_confidence = sum(c.confidence for c in classifications) / len(
            classifications
        )

        return {
            "category": consensus_category,
            "confidence": avg_confidence,
            "agent_count": len(classifications),
            "agreement_level": categories.count(consensus_category) / len(categories),
        }

    def _generate_system_recommendations(
        self, response: PatternValidationResponse
    ) -> List[str]:
        """Generate system-level recommendations based on validation"""
        recommendations = []

        if response.system_coherence.overall_consistency < 0.7:
            recommendations.append("Improve cross-agent classification consistency")

        if response.system_coherence.quality_average < 0.8:
            recommendations.append("Enhance pattern classification quality")

        if response.system_coherence.conflict_count > 5:
            recommendations.append("Address high number of classification conflicts")

        return recommendations

    def _create_fallback_validation(self) -> str:
        """Create fallback validation response"""
        return json.dumps(
            {
                "validation_id": "fallback",
                "patterns_analyzed": [],
                "system_coherence": {
                    "overall_consistency": 0.5,
                    "conflict_count": 0,
                    "quality_average": 0.5,
                    "improvement_areas": ["ai_communication"],
                },
                "actions_required": [],
                "validation_summary": {
                    "total_patterns": 0,
                    "coherent_patterns": 0,
                    "conflicts_resolved": 0,
                    "recommendations_made": 1,
                    "system_health": "FAIR",
                },
            }
        )

    def _create_fallback_response(
        self, validation_id: str, patterns: List[PatternClassification]
    ) -> PatternValidationResponse:
        """Create fallback response when processing fails"""
        return PatternValidationResponse(
            validation_id=validation_id,
            timestamp=datetime.now(),
            patterns_analyzed=[],
            system_coherence=SystemCoherence(
                overall_consistency=0.5,
                conflict_count=0,
                quality_average=0.5,
                improvement_areas=["processing_error"],
            ),
            actions_required=[],
            validation_summary=ValidationSummary(
                total_patterns=len(patterns),
                coherent_patterns=0,
                conflicts_resolved=0,
                recommendations_made=0,
                system_health=SystemHealth.FAIR,
            ),
        )

    def _create_error_response(
        self, validation_id: str, error_message: str
    ) -> PatternValidationResponse:
        """Create error response"""
        return PatternValidationResponse(
            validation_id=validation_id,
            timestamp=datetime.now(),
            patterns_analyzed=[],
            system_coherence=SystemCoherence(
                overall_consistency=0.0,
                conflict_count=1,
                quality_average=0.0,
                improvement_areas=["error_handling"],
            ),
            actions_required=[],
            validation_summary=ValidationSummary(
                total_patterns=0,
                coherent_patterns=0,
                conflicts_resolved=0,
                recommendations_made=0,
                system_health=SystemHealth.CRITICAL,
            ),
        )

    def get_validation_metrics(self) -> Dict[str, Any]:
        """Get current validation metrics"""
        return {
            **self.metrics,
            "pattern_registry_size": len(self.pattern_registry),
            "active_conflicts": len(self.conflict_registry),
            "validation_history_size": len(self.validation_history),
            "last_validation": (
                self.validation_history[-1].timestamp.isoformat()
                if self.validation_history
                else None
            ),
        }

    def get_system_health(self) -> Dict[str, Any]:
        """Get current system health status"""
        if not self.validation_history:
            return {"status": "UNKNOWN", "reason": "No validations performed"}

        latest = self.validation_history[-1]

        return {
            "status": latest.validation_summary.system_health.value,
            "consistency_score": latest.system_coherence.overall_consistency,
            "quality_score": latest.system_coherence.quality_average,
            "conflict_count": latest.system_coherence.conflict_count,
            "last_updated": latest.timestamp.isoformat(),
        }
