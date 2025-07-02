"""
ALims Central AI Brain - Embryo Trainer
Intelligent training and validation of AI embryos
"""

import asyncio
import json
import logging
from typing import Dict, Any, List, Optional
from datetime import datetime, timedelta
from pathlib import Path
from enum import Enum

logger = logging.getLogger(__name__)


class TrainingQuality(Enum):
    """Training quality levels"""

    POOR = "poor"
    FAIR = "fair"
    GOOD = "good"
    EXCELLENT = "excellent"


class BirthReadiness(Enum):
    """Embryo birth readiness levels"""

    NOT_READY = "not_ready"
    NEEDS_WORK = "needs_work"
    ALMOST_READY = "almost_ready"
    READY = "ready"
    OVERDUE = "overdue"


class SpecializationCategory(Enum):
    """Agent specialization categories"""

    PRODUCTIVITY = "productivity"
    DEVELOPMENT = "development"
    RESEARCH = "research"
    COMMUNICATION = "communication"
    SYSTEM_MANAGEMENT = "system_management"
    CREATIVE = "creative"
    ANALYTICAL = "analytical"
    SUPPORT = "support"


class EmbryoTrainingReport:
    """Comprehensive training report for an embryo"""

    def __init__(self, embryo_id: str):
        self.embryo_id = embryo_id
        self.timestamp = datetime.now()
        self.pattern_validation = {}
        self.training_quality = {}
        self.specialization_analysis = {}
        self.birth_readiness = {}
        self.training_recommendations = {}
        self.overall_score = 0.0
        self.readiness_level = BirthReadiness.NOT_READY
        self.recommended_specialization = None

    def to_dict(self) -> Dict[str, Any]:
        """Convert report to dictionary"""
        return {
            "embryo_id": self.embryo_id,
            "timestamp": self.timestamp.isoformat(),
            "pattern_validation": self.pattern_validation,
            "training_quality": self.training_quality,
            "specialization_analysis": self.specialization_analysis,
            "birth_readiness": self.birth_readiness,
            "training_recommendations": self.training_recommendations,
            "overall_score": self.overall_score,
            "readiness_level": self.readiness_level.value,
            "recommended_specialization": self.recommended_specialization,
        }


class EmbryoTrainer:
    """Intelligent training and validation of embryos"""

    def __init__(self, central_brain):
        self.central_brain = central_brain
        self.prompt_template = self._load_prompt_template()

        # Training metrics
        self.embryos_evaluated = 0
        self.embryos_approved_for_birth = 0
        self.average_training_score = 0.0
        self.specialization_distribution = {}

        # Training history
        self.training_reports = {}
        self.specialization_recommendations = {}

        logger.info("EmbryoTrainer initialized")

    def _load_prompt_template(self) -> str:
        """Load the embryo training prompt template"""
        try:
            prompt_path = Path("app/ai/prompts/embryo_training.txt")
            if prompt_path.exists():
                return prompt_path.read_text()
            else:
                return self._get_fallback_prompt()
        except Exception as e:
            logger.error(f"Failed to load embryo training prompt template: {e}")
            return self._get_fallback_prompt()

    def _get_fallback_prompt(self) -> str:
        """Fallback embryo training prompt"""
        return """You are the Embryo Trainer for ALims.

Embryo ID: {embryo_id}
Detected Patterns: {detected_patterns}
Training Data: {behavioral_data}

Analyze this embryo's training and provide recommendations for:
1. Pattern validation
2. Training quality assessment
3. Specialization recommendations
4. Birth readiness evaluation

Provide structured feedback to improve embryo development."""

    async def validate_embryo_training(
        self, embryo_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Validate embryo training quality and coherence"""

        try:
            embryo_id = embryo_data.get("id", "unknown")
            logger.info(f"🧬 Validating embryo training: {embryo_id}")

            # Create training report
            report = EmbryoTrainingReport(embryo_id)

            # Build training context
            training_context = self._build_training_context(embryo_data)

            # Generate AI analysis
            analysis = await self._generate_training_analysis(training_context)

            if analysis.get("success", False):
                # Parse and structure the analysis
                structured_analysis = self._parse_training_analysis(
                    analysis.get("analysis", "")
                )

                # Update report with analysis
                self._update_training_report(report, structured_analysis)

                # Store report
                self.training_reports[embryo_id] = report

                # Update metrics
                self._update_training_metrics(report)

                logger.info(f"✅ Embryo training validation completed: {embryo_id}")

                return {
                    "success": True,
                    "embryo_id": embryo_id,
                    "report": report.to_dict(),
                    "overall_score": report.overall_score,
                    "readiness_level": report.readiness_level.value,
                    "recommended_specialization": report.recommended_specialization,
                }
            else:
                return {
                    "success": False,
                    "error": analysis.get("error", "Analysis failed"),
                }

        except Exception as e:
            logger.error(f"Failed to validate embryo training: {e}")
            return {"success": False, "error": str(e)}

    async def generate_training_labels(
        self, events: List[Dict[str, Any]]
    ) -> Dict[str, Any]:
        """Generate intelligent labels for training data"""

        try:
            logger.info(f"🏷️ Generating training labels for {len(events)} events")

            # Analyze events for patterns
            event_analysis = self._analyze_events_for_labeling(events)

            # Generate labels using AI
            labeling_prompt = f"""
            Analyze these behavioral events and generate intelligent training labels:
            
            Events: {event_analysis}
            
            For each event, provide:
            1. Primary behavioral category
            2. Specific action type
            3. Context classification
            4. User intent inference
            5. Specialization relevance
            
            Generate labels that will help train specialized agents effectively.
            """

            labels_response = await self.central_brain.ollama_client.generate_response(
                prompt="Generate intelligent training labels for these behavioral events",
                system_prompt=labeling_prompt,
            )

            # Parse generated labels
            training_labels = self._parse_training_labels(labels_response, events)

            logger.info(f"✅ Generated {len(training_labels)} training labels")

            return {
                "success": True,
                "labels": training_labels,
                "events_processed": len(events),
                "labeling_timestamp": datetime.now().isoformat(),
            }

        except Exception as e:
            logger.error(f"Failed to generate training labels: {e}")
            return {"success": False, "error": str(e)}

    async def assess_birth_readiness(
        self, embryo_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Determine if embryo is ready for agent birth"""

        try:
            embryo_id = embryo_data.get("id", "unknown")
            logger.info(f"🎯 Assessing birth readiness: {embryo_id}")

            # Get or create training report
            if embryo_id in self.training_reports:
                report = self.training_reports[embryo_id]
            else:
                # Generate new validation if not exists
                validation_result = await self.validate_embryo_training(embryo_data)
                if not validation_result.get("success", False):
                    return validation_result
                report = self.training_reports[embryo_id]

            # Assess readiness based on multiple criteria
            readiness_assessment = self._assess_readiness_criteria(report, embryo_data)

            # Update readiness level
            report.readiness_level = readiness_assessment["readiness_level"]

            logger.info(
                f"✅ Birth readiness assessed: {embryo_id} - {report.readiness_level.value}"
            )

            return {
                "success": True,
                "embryo_id": embryo_id,
                "readiness_level": report.readiness_level.value,
                "readiness_score": readiness_assessment["readiness_score"],
                "assessment": readiness_assessment,
                "birth_recommendation": readiness_assessment["birth_recommendation"],
            }

        except Exception as e:
            logger.error(f"Failed to assess birth readiness: {e}")
            return {"success": False, "error": str(e)}

    async def recommend_specialization(
        self, embryo_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Recommend optimal specialization for embryo"""

        try:
            embryo_id = embryo_data.get("id", "unknown")
            logger.info(f"🎨 Recommending specialization: {embryo_id}")

            # Analyze patterns for specialization
            patterns = embryo_data.get("patterns", [])
            behavioral_data = embryo_data.get("behavioral_data", {})
            user_context = embryo_data.get("user_context", {})

            # Generate specialization recommendation using AI
            specialization_prompt = f"""
            Analyze this embryo's patterns and recommend the optimal specialization:
            
            Embryo ID: {embryo_id}
            Detected Patterns: {patterns}
            Behavioral Data: {behavioral_data}
            User Context: {user_context}
            
            Available specialization categories:
            - Productivity: Task management, scheduling, automation
            - Development: Coding, debugging, technical assistance
            - Research: Information gathering, analysis, synthesis
            - Communication: Writing, messaging, presentation
            - System Management: Configuration, monitoring, optimization
            - Creative: Content creation, design, brainstorming
            - Analytical: Data analysis, pattern recognition, insights
            - Support: Help, guidance, troubleshooting
            
            Recommend the best specialization and explain your reasoning.
            """

            recommendation_response = (
                await self.central_brain.ollama_client.generate_response(
                    prompt="Recommend optimal specialization for this embryo",
                    system_prompt=specialization_prompt,
                )
            )

            # Parse recommendation
            specialization_rec = self._parse_specialization_recommendation(
                recommendation_response
            )

            # Store recommendation
            self.specialization_recommendations[embryo_id] = specialization_rec

            logger.info(
                f"✅ Specialization recommended: {embryo_id} - {specialization_rec.get('category', 'Unknown')}"
            )

            return {
                "success": True,
                "embryo_id": embryo_id,
                "recommendation": specialization_rec,
                "timestamp": datetime.now().isoformat(),
            }

        except Exception as e:
            logger.error(f"Failed to recommend specialization: {e}")
            return {"success": False, "error": str(e)}

    def _build_training_context(self, embryo_data: Dict[str, Any]) -> Dict[str, Any]:
        """Build context for training analysis"""
        return {
            "embryo_id": embryo_data.get("id", "unknown"),
            "training_duration": embryo_data.get("training_duration", "unknown"),
            "detected_patterns": embryo_data.get("patterns", []),
            "behavioral_data": embryo_data.get("behavioral_data", {}),
            "user_context": embryo_data.get("user_context", {}),
            "training_history": embryo_data.get("training_history", []),
            "current_specialization": embryo_data.get("specialization", "none"),
        }

    async def _generate_training_analysis(
        self, context: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Generate AI analysis of embryo training"""
        try:
            # Format prompt with context
            formatted_prompt = self._format_training_prompt(context)

            # Generate analysis
            analysis_response = await self.central_brain.ollama_client.generate_response(
                prompt="Analyze this embryo's training and provide comprehensive evaluation",
                system_prompt=formatted_prompt,
            )

            return {"success": True, "analysis": analysis_response}

        except Exception as e:
            logger.error(f"Failed to generate training analysis: {e}")
            return {"success": False, "error": str(e)}

    def _format_training_prompt(self, context: Dict[str, Any]) -> str:
        """Format the training prompt with context"""
        try:
            return self.prompt_template.format(**context)
        except Exception as e:
            logger.error(f"Error formatting training prompt: {e}")
            return (
                f"Analyze embryo {context.get('embryo_id', 'unknown')} training data."
            )

    def _parse_training_analysis(self, analysis: str) -> Dict[str, Any]:
        """Parse structured training analysis from AI response"""
        try:
            # Extract structured sections from analysis
            sections = {
                "pattern_validation": self._extract_section(
                    analysis, "PATTERN VALIDATION"
                ),
                "training_quality": self._extract_section(analysis, "TRAINING QUALITY"),
                "specialization_analysis": self._extract_section(
                    analysis, "SPECIALIZATION ANALYSIS"
                ),
                "birth_readiness": self._extract_section(analysis, "BIRTH READINESS"),
                "training_recommendations": self._extract_section(
                    analysis, "TRAINING RECOMMENDATIONS"
                ),
            }

            return sections

        except Exception as e:
            logger.error(f"Failed to parse training analysis: {e}")
            return {"error": "Failed to parse analysis"}

    def _extract_section(self, text: str, section_name: str) -> Dict[str, Any]:
        """Extract a specific section from structured text"""
        try:
            start_marker = f"**{section_name}:**"
            start_idx = text.find(start_marker)

            if start_idx == -1:
                return {"content": "Section not found", "score": 5.0}

            # Find next section or end of text
            next_section_idx = text.find("**", start_idx + len(start_marker))
            if next_section_idx == -1:
                section_content = text[start_idx + len(start_marker) :].strip()
            else:
                section_content = text[
                    start_idx + len(start_marker) : next_section_idx
                ].strip()

            # Extract score if present
            score = self._extract_score(section_content)

            return {
                "content": section_content,
                "score": score,
                "timestamp": datetime.now().isoformat(),
            }

        except Exception as e:
            logger.error(f"Failed to extract section {section_name}: {e}")
            return {"content": "Extraction failed", "score": 0.0}

    def _extract_score(self, content: str) -> float:
        """Extract numerical score from content"""
        try:
            # Look for patterns like "score (1-10)" or "score: 8"
            import re

            score_patterns = [
                r"score[:\s]+(\d+(?:\.\d+)?)",
                r"(\d+(?:\.\d+)?)[/\s]*10",
                r"rating[:\s]+(\d+(?:\.\d+)?)",
            ]

            for pattern in score_patterns:
                match = re.search(pattern, content.lower())
                if match:
                    return float(match.group(1))

            return 5.0  # Default score

        except Exception:
            return 5.0

    def _update_training_report(
        self, report: EmbryoTrainingReport, analysis: Dict[str, Any]
    ):
        """Update training report with analysis results"""
        report.pattern_validation = analysis.get("pattern_validation", {})
        report.training_quality = analysis.get("training_quality", {})
        report.specialization_analysis = analysis.get("specialization_analysis", {})
        report.birth_readiness = analysis.get("birth_readiness", {})
        report.training_recommendations = analysis.get("training_recommendations", {})

        # Calculate overall score
        scores = [
            report.pattern_validation.get("score", 5.0),
            report.training_quality.get("score", 5.0),
            report.birth_readiness.get("score", 5.0),
        ]
        report.overall_score = sum(scores) / len(scores)

        # Determine readiness level
        if report.overall_score >= 8.0:
            report.readiness_level = BirthReadiness.READY
        elif report.overall_score >= 6.5:
            report.readiness_level = BirthReadiness.ALMOST_READY
        elif report.overall_score >= 4.0:
            report.readiness_level = BirthReadiness.NEEDS_WORK
        else:
            report.readiness_level = BirthReadiness.NOT_READY

    def _analyze_events_for_labeling(
        self, events: List[Dict[str, Any]]
    ) -> Dict[str, Any]:
        """Analyze events to prepare for labeling"""
        try:
            event_summary = {
                "total_events": len(events),
                "event_types": {},
                "time_distribution": {},
                "common_patterns": [],
            }

            for event in events:
                event_type = event.get("type", "unknown")
                event_summary["event_types"][event_type] = (
                    event_summary["event_types"].get(event_type, 0) + 1
                )

            return event_summary

        except Exception as e:
            logger.error(f"Failed to analyze events for labeling: {e}")
            return {"error": str(e)}

    def _parse_training_labels(
        self, response: str, events: List[Dict[str, Any]]
    ) -> List[Dict[str, Any]]:
        """Parse training labels from AI response"""
        try:
            # For now, create basic labels
            # In a full implementation, this would parse structured AI response
            labels = []

            for i, event in enumerate(events):
                label = {
                    "event_id": event.get("id", f"event_{i}"),
                    "primary_category": "behavioral",
                    "action_type": event.get("type", "unknown"),
                    "context": "user_interaction",
                    "specialization_relevance": ["general"],
                    "confidence": 0.8,
                }
                labels.append(label)

            return labels

        except Exception as e:
            logger.error(f"Failed to parse training labels: {e}")
            return []

    def _assess_readiness_criteria(
        self, report: EmbryoTrainingReport, embryo_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Assess embryo readiness based on multiple criteria"""
        try:
            criteria_scores = {
                "pattern_quality": report.pattern_validation.get("score", 5.0),
                "training_quality": report.training_quality.get("score", 5.0),
                "data_completeness": self._assess_data_completeness(embryo_data),
                "specialization_clarity": self._assess_specialization_clarity(report),
                "stability": self._assess_training_stability(embryo_data),
            }

            # Calculate overall readiness score
            readiness_score = sum(criteria_scores.values()) / len(criteria_scores)

            # Determine readiness level
            if readiness_score >= 8.0:
                readiness_level = BirthReadiness.READY
                birth_recommendation = "Embryo is ready for agent birth"
            elif readiness_score >= 6.5:
                readiness_level = BirthReadiness.ALMOST_READY
                birth_recommendation = "Embryo needs minor improvements before birth"
            elif readiness_score >= 4.0:
                readiness_level = BirthReadiness.NEEDS_WORK
                birth_recommendation = "Embryo requires significant additional training"
            else:
                readiness_level = BirthReadiness.NOT_READY
                birth_recommendation = "Embryo is not ready for birth"

            return {
                "readiness_score": readiness_score,
                "readiness_level": readiness_level,
                "criteria_scores": criteria_scores,
                "birth_recommendation": birth_recommendation,
            }

        except Exception as e:
            logger.error(f"Failed to assess readiness criteria: {e}")
            return {"readiness_score": 0.0, "readiness_level": BirthReadiness.NOT_READY}

    def _assess_data_completeness(self, embryo_data: Dict[str, Any]) -> float:
        """Assess completeness of training data"""
        try:
            patterns = embryo_data.get("patterns", [])
            behavioral_data = embryo_data.get("behavioral_data", {})

            completeness_score = 5.0  # Base score

            if len(patterns) >= 5:
                completeness_score += 2.0
            elif len(patterns) >= 3:
                completeness_score += 1.0

            if len(behavioral_data) >= 10:
                completeness_score += 2.0
            elif len(behavioral_data) >= 5:
                completeness_score += 1.0

            return min(completeness_score, 10.0)

        except Exception:
            return 5.0

    def _assess_specialization_clarity(self, report: EmbryoTrainingReport) -> float:
        """Assess clarity of specialization direction"""
        try:
            specialization_content = report.specialization_analysis.get("content", "")

            # Simple heuristic based on content length and keywords
            if len(specialization_content) > 100:
                return 7.0
            elif len(specialization_content) > 50:
                return 5.0
            else:
                return 3.0

        except Exception:
            return 5.0

    def _assess_training_stability(self, embryo_data: Dict[str, Any]) -> float:
        """Assess stability of training over time"""
        try:
            training_history = embryo_data.get("training_history", [])

            if len(training_history) >= 5:
                return 8.0
            elif len(training_history) >= 3:
                return 6.0
            else:
                return 4.0

        except Exception:
            return 5.0

    def _parse_specialization_recommendation(self, response: str) -> Dict[str, Any]:
        """Parse specialization recommendation from AI response"""
        try:
            # Extract key information from response
            recommendation = {
                "category": "general",
                "confidence": 0.7,
                "reasoning": (
                    response[:200] + "..." if len(response) > 200 else response
                ),
                "capabilities": [],
                "use_cases": [],
            }

            # Simple keyword-based categorization
            response_lower = response.lower()

            if any(
                word in response_lower
                for word in ["code", "develop", "program", "debug"]
            ):
                recommendation["category"] = "development"
            elif any(
                word in response_lower
                for word in ["research", "analyze", "study", "investigate"]
            ):
                recommendation["category"] = "research"
            elif any(
                word in response_lower
                for word in ["write", "communicate", "message", "present"]
            ):
                recommendation["category"] = "communication"
            elif any(
                word in response_lower
                for word in ["manage", "organize", "schedule", "task"]
            ):
                recommendation["category"] = "productivity"
            elif any(
                word in response_lower
                for word in ["system", "configure", "monitor", "optimize"]
            ):
                recommendation["category"] = "system_management"
            elif any(
                word in response_lower
                for word in ["create", "design", "art", "creative"]
            ):
                recommendation["category"] = "creative"
            elif any(
                word in response_lower
                for word in ["data", "analyze", "pattern", "insight"]
            ):
                recommendation["category"] = "analytical"
            elif any(
                word in response_lower
                for word in ["help", "support", "assist", "guide"]
            ):
                recommendation["category"] = "support"

            return recommendation

        except Exception as e:
            logger.error(f"Failed to parse specialization recommendation: {e}")
            return {
                "category": "general",
                "confidence": 0.5,
                "reasoning": "Parse failed",
            }

    def _update_training_metrics(self, report: EmbryoTrainingReport):
        """Update training performance metrics"""
        self.embryos_evaluated += 1

        # Update average training score
        if self.average_training_score == 0:
            self.average_training_score = report.overall_score
        else:
            self.average_training_score = (
                self.average_training_score + report.overall_score
            ) / 2

        # Update birth approvals
        if report.readiness_level in [
            BirthReadiness.READY,
            BirthReadiness.ALMOST_READY,
        ]:
            self.embryos_approved_for_birth += 1

        # Update specialization distribution
        if report.recommended_specialization:
            category = report.recommended_specialization
            self.specialization_distribution[category] = (
                self.specialization_distribution.get(category, 0) + 1
            )

    def get_trainer_status(self) -> Dict[str, Any]:
        """Get current status of the Embryo Trainer"""
        return {
            "agent_name": "EmbryoTrainer",
            "embryos_evaluated": self.embryos_evaluated,
            "embryos_approved_for_birth": self.embryos_approved_for_birth,
            "approval_rate": (
                (self.embryos_approved_for_birth / self.embryos_evaluated)
                if self.embryos_evaluated > 0
                else 0.0
            ),
            "average_training_score": self.average_training_score,
            "specialization_distribution": self.specialization_distribution,
            "active_reports": len(self.training_reports),
            "capabilities": [
                "embryo_training_validation",
                "pattern_classification_analysis",
                "birth_readiness_assessment",
                "specialization_recommendation",
                "training_label_generation",
                "quality_assessment",
            ],
        }
