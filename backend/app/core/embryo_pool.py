#!/usr/bin/env python3
"""
ALims Embryo Pool

Manages a pool of agent embryos that compete to detect patterns in user data.
Each embryo is a minimal neural network that specializes in different pattern
types. When an embryo fills its data buffer, it triggers agent birth.
"""

import asyncio
import logging
import time
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple
import json
import uuid

from datetime import datetime
from collections import deque

from .pattern_detector import PatternDetector
from ..privacy.content_filter import ContentFilter

try:
    from ..intelligence.event_clustering import create_intelligent_clustering

    CLUSTERING_AVAILABLE = True
except ImportError:
    CLUSTERING_AVAILABLE = False


@dataclass
class EmbryoStats:
    """Statistics for tracking embryo performance"""
    creation_time: datetime
    patterns_detected: int
    specialization_scores: Dict[str, float]
    data_buffer_size_mb: float
    last_activity: datetime
    fitness_score: float


class AgentEmbryo:
    """
    A minimal AI embryo that detects patterns and competes for specialization.
    Each embryo has a small neural network and data buffer.
    """

    def __init__(self, embryo_id: str, config: dict):
        self.embryo_id = embryo_id
        self.config = config
        self.logger = logging.getLogger(f'Embryo-{embryo_id[:8]}')

        # Neural pattern detector (1M parameters)
        self.pattern_detector = PatternDetector(
            input_dim=512,
            hidden_dim=256,
            output_dim=128,
            max_params=1_000_000
        )

        # Data management
        self.data_buffer = []
        self.data_buffer_size_mb = 0.0
        self.data_limit_mb = config.get('data_buffer_limit_mb', 16)

        # Specialization tracking
        self.specialization_scores = {
            'file_operations': 0.0,
            'app_launches': 0.0,
            'communication': 0.0,
            'creative_work': 0.0,
            'development': 0.0,
            'web_browsing': 0.0,
            'system_maintenance': 0.0,
            'temporal_patterns': 0.0
        }

        # Performance metrics
        self.stats = EmbryoStats(
            creation_time=datetime.now(),
            patterns_detected=0,
            specialization_scores=self.specialization_scores.copy(),
            data_buffer_size_mb=0.0,
            last_activity=datetime.now(),
            fitness_score=0.0
        )

        # Competition state
        self.is_active = True
        self.birth_ready = False

    async def observe(self, data_event: dict) -> Optional[dict]:
        """
        Process a system event and detect patterns.
        Returns pattern info if detected, None otherwise.
        """
        if not self.is_active:
            return None

        try:
            # Filter and process the data
            processed_event = await self._preprocess_event(data_event)
            if not processed_event:
                return None

            # Detect patterns using neural network
            pattern_info = await self.pattern_detector.analyze(processed_event)

            if pattern_info and pattern_info['confidence'] > 0.3:
                # Add to data buffer
                await self._add_to_buffer(processed_event, pattern_info)

                # Update specialization scores
                await self._update_specialization(pattern_info)

                # Update stats
                self.stats.patterns_detected += 1
                self.stats.last_activity = datetime.now()

                # Check if ready for birth
                if self.data_buffer_size_mb >= self.data_limit_mb:
                    self.birth_ready = True
                    self.logger.info(
                        f"Embryo {self.embryo_id} ready for birth! "
                        f"Buffer: {self.data_buffer_size_mb:.1f}MB, "
                        f"Patterns: {self.stats.patterns_detected}"
                    )

                return pattern_info

        except Exception as e:
            self.logger.error(f"Error in observe: {e}")

        return None

    async def _preprocess_event(self, data_event: dict) -> Optional[dict]:
        """Preprocess and validate system event data"""
        try:
            # Basic validation
            if not data_event or 'type' not in data_event:
                return None

            # Add timestamp if missing
            if 'timestamp' not in data_event:
                data_event['timestamp'] = time.time()

            # Add embryo context
            processed = {
                'embryo_id': self.embryo_id,
                'original_event': data_event,
                'processing_time': time.time()
            }

            return processed

        except Exception as e:
            self.logger.error(f"Error preprocessing event: {e}")
            return None

    async def _add_to_buffer(self, event: dict, pattern: dict):
        """Add event and pattern to data buffer"""
        try:
            buffer_entry = {
                'timestamp': time.time(),
                'event': event,
                'pattern': pattern,
                'embryo_id': self.embryo_id
            }

            self.data_buffer.append(buffer_entry)

            # Estimate size (rough calculation)
            entry_size = len(json.dumps(buffer_entry)) / (1024 * 1024)
            self.data_buffer_size_mb += entry_size
            self.stats.data_buffer_size_mb = self.data_buffer_size_mb

            # Limit buffer size to prevent memory issues
            max_entries = 10000
            if len(self.data_buffer) > max_entries:
                removed = self.data_buffer.pop(0)
                removed_size = len(json.dumps(removed)) / (1024 * 1024)
                self.data_buffer_size_mb -= removed_size

        except Exception as e:
            self.logger.error(f"Error adding to buffer: {e}")

    async def _update_specialization(self, pattern_info: dict):
        """Update specialization scores based on detected patterns"""
        try:
            pattern_type = pattern_info.get('type', 'unknown')
            confidence = pattern_info.get('confidence', 0.0)

            # Map pattern types to specialization categories
            type_mapping = {
                'file_create': 'file_operations',
                'file_move': 'file_operations',
                'file_delete': 'file_operations',
                'app_launch': 'app_launches',
                'app_switch': 'app_launches',
                'email_open': 'communication',
                'calendar_event': 'communication',
                'code_edit': 'development',
                'git_commit': 'development',
                'web_navigate': 'web_browsing',
                'web_search': 'web_browsing',
                'design_work': 'creative_work',
                'media_edit': 'creative_work',
                'system_setting': 'system_maintenance',
                'routine_behavior': 'temporal_patterns'
            }

            category = type_mapping.get(pattern_type, 'system_maintenance')

            # Update score with exponential moving average
            alpha = 0.1  # Learning rate
            current_score = self.specialization_scores[category]
            self.specialization_scores[category] = (
                alpha * confidence + (1 - alpha) * current_score
            )

            # Update stats
            self.stats.specialization_scores = self.specialization_scores.copy()

        except Exception as e:
            self.logger.error(f"Error updating specialization: {e}")

    def calculate_fitness(self) -> float:
        """Calculate overall fitness score for natural selection"""
        try:
            # Base fitness on pattern detection capability
            detection_score = min(self.stats.patterns_detected / 100.0, 1.0)

            # Specialization bonus (reward for finding a niche)
            max_specialization = max(self.specialization_scores.values())
            specialization_bonus = max_specialization * 0.5

            # Activity penalty (inactive embryos lose fitness)
            hours_inactive = (datetime.now() - self.stats.last_activity).seconds / 3600
            activity_penalty = min(hours_inactive * 0.1, 0.8)

            # Data collection efficiency
            if self.data_buffer_size_mb > 0:
                efficiency = self.stats.patterns_detected / self.data_buffer_size_mb
                efficiency_bonus = min(efficiency / 10.0, 0.3)
            else:
                efficiency_bonus = 0.0

            # Calculate final fitness
            fitness = (
                detection_score + 
                specialization_bonus + 
                efficiency_bonus - 
                activity_penalty
            )

            self.stats.fitness_score = max(0.0, fitness)
            return self.stats.fitness_score

        except Exception as e:
            self.logger.error(f"Error calculating fitness: {e}")
            return 0.0

    def get_dominant_specialization(self) -> Tuple[str, float]:
        """Get the embryo's strongest specialization"""
        max_category = max(
            self.specialization_scores.items(),
            key=lambda x: x[1]
        )
        return max_category

    def prepare_birth_data(self) -> dict:
        """Prepare data for agent creation"""
        dominant_spec, spec_score = self.get_dominant_specialization()

        return {
            'embryo_id': self.embryo_id,
            'creation_time': self.stats.creation_time.isoformat(),
            'data_buffer': self.data_buffer,
            'specialization_scores': self.specialization_scores,
            'dominant_specialization': dominant_spec,
            'specialization_strength': spec_score,
            'patterns_detected': self.stats.patterns_detected,
            'fitness_score': self.stats.fitness_score,
            'neural_weights': self.pattern_detector.get_weights()
        }

    async def update_pattern_knowledge(self, pattern_summary: dict):
        """Update embryo with pattern insights from clustering analysis"""
        try:
            # Extract useful pattern information
            total_patterns = pattern_summary.get("total_patterns", 0)
            insights = pattern_summary.get("behavioral_insights", [])
            dominant_patterns = pattern_summary.get("dominant_patterns", [])

            # Update specialization based on discovered patterns
            for pattern in dominant_patterns:
                pattern_desc = pattern.get("description", "").lower()

                # Boost relevant specializations based on pattern content
                if "file" in pattern_desc or "cache" in pattern_desc:
                    self.specialization_scores["file_operations"] += 0.1
                elif "app" in pattern_desc or "launch" in pattern_desc:
                    self.specialization_scores["app_launches"] += 0.1
                elif "browser" in pattern_desc or "web" in pattern_desc:
                    self.specialization_scores["web_browsing"] += 0.1
                elif "development" in pattern_desc or "code" in pattern_desc:
                    self.specialization_scores["development"] += 0.1
                elif "temporal" in pattern_desc or "time" in pattern_desc:
                    self.specialization_scores["temporal_patterns"] += 0.1

            # Normalize specialization scores
            max_score = max(self.specialization_scores.values())
            if max_score > 1.0:
                for key in self.specialization_scores:
                    self.specialization_scores[key] /= max_score

            # Update fitness based on pattern relevance
            if total_patterns > 0:
                self.stats.fitness_score += 0.05  # Small boost for pattern awareness

            self.logger.debug(f"Updated with {total_patterns} patterns")

        except Exception as e:
            self.logger.error(f"Error updating pattern knowledge: {e}")


class EmbryoPool:
    """
    Manages a pool of competing agent embryos.
    Handles natural selection, resource allocation, and agent birth triggers.
    """

    def __init__(self, config: dict):
        self.config = config
        self.logger = logging.getLogger('EmbryoPool')

        # Pool configuration
        self.max_embryos = config.get('max_concurrent', 15)
        self.min_survival_threshold = config.get('min_survival_threshold', 0.3)

        # Embryo management
        self.embryos: Dict[str, AgentEmbryo] = {}
        self.birth_queue: List[str] = []

        # Competition metrics
        self.generation = 0
        self.total_births = 0
        self.culling_stats = {
            'total_culled': 0,
            'reasons': {'low_fitness': 0, 'inactivity': 0, 'redundancy': 0}
        }

        # Content filtering
        self.content_filter = ContentFilter(config.get('privacy', {}))

        # Performance tracking
        self.pool_stats = {
            'events_processed': 0,
            'patterns_detected': 0,
            'avg_fitness': 0.0,
            'active_embryos': 0
        }

        # Intelligent clustering system
        self.clustering_system = None
        self.event_buffer = deque(maxlen=10000)  # Event buffer for clustering
        self.last_clustering_time = 0
        self.pattern_insights = []

        if CLUSTERING_AVAILABLE:
            clustering_config = config.get(
                "clustering",
                {
                    "min_events_for_analysis": 500,
                    "analysis_interval": 300,  # 5 minutes
                    "pattern_memory_size": 1000,
                },
            )
            self.clustering_system = create_intelligent_clustering(clustering_config)
            self.logger.info("🧠 Intelligent clustering system enabled")
        else:
            self.logger.warning(
                "Clustering system not available - install scikit-learn"
            )

        # Initialize embryo pool will be done in start() method

    async def start(self):
        """Start the embryo pool system"""
        self.logger.info("🧬 Starting Embryo Pool...")
        await self.initialize()
        self.logger.info("✅ Embryo Pool started successfully")

    async def stop(self):
        """Stop the embryo pool system"""
        self.logger.info("🛑 Stopping Embryo Pool...")
        # In a full implementation, would properly shutdown background tasks
        self.logger.info("✅ Embryo Pool stopped")

    async def initialize(self):
        """Initialize the embryo pool with initial embryos"""
        self.logger.info("Initializing embryo pool...")

        try:
            # Create initial embryos
            for i in range(self.max_embryos):
                embryo_id = str(uuid.uuid4())
                # Pass the data_buffer_limit_mb directly to embryos
                embryo_config = {
                    "data_buffer_limit_mb": self.config.get("data_buffer_limit_mb", 16)
                }
                embryo = AgentEmbryo(embryo_id, embryo_config)
                self.embryos[embryo_id] = embryo

            self.logger.info(f"Created {len(self.embryos)} initial embryos")

            # Start background tasks
            asyncio.create_task(self._natural_selection_loop())
            asyncio.create_task(self._stats_update_loop())

        except Exception as e:
            self.logger.error(f"Error initializing embryo pool: {e}")
            raise

    async def feed_data(self, data_event: dict) -> List[dict]:
        """
        Feed system event data to all active embryos.
        Returns list of detected patterns.
        """
        patterns = []

        try:
            # Filter sensitive content
            filtered_event = await self.content_filter.filter_event(data_event)
            if not filtered_event:
                return patterns

            # Feed to all active embryos
            tasks = []
            for embryo in self.embryos.values():
                if embryo.is_active:
                    tasks.append(embryo.observe(filtered_event))

            # Collect results
            results = await asyncio.gather(*tasks, return_exceptions=True)

            for result in results:
                if isinstance(result, dict):
                    patterns.append(result)
                elif isinstance(result, Exception):
                    self.logger.warning(f"Embryo observation error: {result}")

            # Update pool stats
            self.pool_stats['events_processed'] += 1
            self.pool_stats['patterns_detected'] += len(patterns)

            # Check for birth-ready embryos
            await self._check_birth_readiness()

        except Exception as e:
            self.logger.error(f"Error feeding data to embryos: {e}")

        return patterns

    async def _check_birth_readiness(self):
        """Check if any embryos are ready for agent birth"""
        for embryo_id, embryo in self.embryos.items():
            if embryo.birth_ready and embryo_id not in self.birth_queue:
                self.birth_queue.append(embryo_id)
                self.logger.info(f"Embryo {embryo_id} added to birth queue")

    async def get_birth_ready_embryo(self) -> Optional[AgentEmbryo]:
        """Get next embryo ready for agent birth"""
        if not self.birth_queue:
            return None

        embryo_id = self.birth_queue.pop(0)
        embryo = self.embryos.get(embryo_id)

        if embryo and embryo.birth_ready:
            return embryo

        return None

    async def _natural_selection_loop(self):
        """Background task for natural selection and culling"""
        while True:
            try:
                await asyncio.sleep(3600)  # Run every hour
                await self._perform_natural_selection()

            except Exception as e:
                self.logger.error(f"Error in natural selection: {e}")

    async def _perform_natural_selection(self):
        """Perform natural selection on embryo pool"""
        self.logger.info("Performing natural selection...")

        try:
            # Calculate fitness for all embryos
            fitness_scores = {}
            for embryo_id, embryo in self.embryos.items():
                fitness_scores[embryo_id] = embryo.calculate_fitness()

            # Identify weak embryos for culling
            weak_embryos = [
                embryo_id for embryo_id, fitness in fitness_scores.items()
                if fitness < self.min_survival_threshold
            ]

            # Cull weak embryos (but keep minimum viable population)
            min_population = max(5, self.max_embryos // 3)
            active_count = len([e for e in self.embryos.values() if e.is_active])

            if active_count > min_population:
                culled_count = 0
                for embryo_id in weak_embryos:
                    if active_count - culled_count > min_population:
                        await self._cull_embryo(embryo_id, 'low_fitness')
                        culled_count += 1

            # Create new embryos to replace culled ones
            await self._spawn_new_embryos()

            # Update generation
            self.generation += 1

            self.logger.info(
                f"Natural selection complete. Generation: {self.generation}, "
                f"Active embryos: {len([e for e in self.embryos.values() if e.is_active])}"
            )

        except Exception as e:
            self.logger.error(f"Error in natural selection: {e}")

    async def _cull_embryo(self, embryo_id: str, reason: str):
        """Remove an embryo from the active pool"""
        if embryo_id in self.embryos:
            embryo = self.embryos[embryo_id]
            embryo.is_active = False

            self.culling_stats['total_culled'] += 1
            self.culling_stats['reasons'][reason] += 1

            self.logger.info(f"Culled embryo {embryo_id} - Reason: {reason}")

    async def _spawn_new_embryos(self):
        """Create new embryos to maintain pool size"""
        active_count = len([e for e in self.embryos.values() if e.is_active])

        while active_count < self.max_embryos:
            embryo_id = str(uuid.uuid4())
            # Pass the data_buffer_limit_mb directly to new embryos
            embryo_config = {
                "data_buffer_limit_mb": self.config.get("data_buffer_limit_mb", 16)
            }
            embryo = AgentEmbryo(embryo_id, embryo_config)
            self.embryos[embryo_id] = embryo
            active_count += 1

            self.logger.info(f"Spawned new embryo {embryo_id}")

    async def _stats_update_loop(self):
        """Background task for updating pool statistics"""
        while True:
            try:
                await asyncio.sleep(300)  # Update every 5 minutes
                await self._update_pool_stats()

            except Exception as e:
                self.logger.error(f"Error updating stats: {e}")

    async def _update_pool_stats(self):
        """Update pool-wide statistics"""
        active_embryos = [e for e in self.embryos.values() if e.is_active]

        if active_embryos:
            avg_fitness = sum(e.calculate_fitness() for e in active_embryos) / len(active_embryos)
            self.pool_stats['avg_fitness'] = avg_fitness

        self.pool_stats['active_embryos'] = len(active_embryos)

    def get_pool_status(self) -> dict:
        """Get current pool status for monitoring"""
        active_embryos = [e for e in self.embryos.values() if e.is_active]

        # Prepare embryo data for agent manager
        embryo_data_list = []
        for embryo in active_embryos:
            dominant_spec, spec_strength = embryo.get_dominant_specialization()
            embryo_data_list.append(
                {
                    "embryo_id": embryo.embryo_id,
                    "patterns_detected": embryo.stats.patterns_detected,
                    "fitness_score": embryo.calculate_fitness(),
                    "specialization_scores": embryo.specialization_scores.copy(),
                    "dominant_specialization": dominant_spec,
                    "specialization_strength": spec_strength,
                    "creation_time": embryo.stats.creation_time.isoformat(),
                    "birth_ready": embryo.birth_ready,
                }
            )

        return {
            "total_embryos": len(self.embryos),
            "active_embryos": len(active_embryos),
            "birth_queue_size": len(self.birth_queue),
            "generation": self.generation,
            "total_births": self.total_births,
            "events_processed": self.pool_stats["events_processed"],
            "pool_stats": self.pool_stats,
            "culling_stats": self.culling_stats,
            "top_specializations": self._get_top_specializations(),
            "embryos": embryo_data_list,  # For agent manager
        }

    def _get_top_specializations(self) -> Dict[str, int]:
        """Get count of embryos by their dominant specialization"""
        specializations = {}

        for embryo in self.embryos.values():
            if embryo.is_active:
                dominant, _ = embryo.get_dominant_specialization()
                specializations[dominant] = specializations.get(dominant, 0) + 1

        return specializations

    async def process_event(self, event_data: dict) -> dict:
        """
        Process event through embryo pool with intelligent clustering insights
        """
        try:
            # Add to event buffer for clustering analysis
            self.event_buffer.append(event_data)

            # Periodic clustering analysis for pattern discovery
            if self.clustering_system and self._should_run_clustering():
                await self._perform_clustering_analysis()

            # Enhanced event processing with pattern insights
            enhanced_event = await self._enhance_event_with_patterns(event_data)

            # Process through embryo pool
            results = []
            for embryo in self.embryos.values():
                try:
                    result = await embryo.observe(enhanced_event)
                    if result:
                        results.append(result)
                except Exception as e:
                    self.logger.debug(
                        f"Embryo {embryo.embryo_id} processing error: {e}"
                    )

            # Update statistics
            self.pool_stats["events_processed"] += 1
            self.pool_stats["patterns_detected"] += len(results)

            # Trigger evolution if needed
            if self._should_evolve():
                await self._evolve_pool()

            # Return best result
            if results:
                best_result = max(results, key=lambda x: x.get("confidence", 0))
                return best_result

            return {"status": "processed", "embryo_count": len(self.embryos)}

        except Exception as e:
            self.logger.error(f"Event processing error: {e}")
            return {"status": "error", "error": str(e)}

    def _should_run_clustering(self) -> bool:
        """Determine if clustering analysis should be performed"""
        if not self.clustering_system:
            return False

        current_time = time.time()
        min_events = self.clustering_system.config.get("min_events_for_analysis", 500)
        analysis_interval = self.clustering_system.config.get("analysis_interval", 300)

        return (
            len(self.event_buffer) >= min_events
            and current_time - self.last_clustering_time >= analysis_interval
        )

    async def _perform_clustering_analysis(self):
        """Perform intelligent clustering analysis on recent events"""
        try:
            self.logger.info(
                f"🔍 Analyzing {len(self.event_buffer)} events for patterns..."
            )

            # Convert buffer to list for analysis
            events_to_analyze = list(self.event_buffer)

            # Run clustering analysis
            analysis_result = await self.clustering_system.analyze_events(
                events_to_analyze
            )

            if analysis_result:
                # Extract insights for embryo enhancement
                self.pattern_insights = self.clustering_system.get_latest_insights()

                # Log discovered patterns
                n_patterns = analysis_result.get("n_clusters", 0)
                method_used = analysis_result.get("method_used", "unknown")
                processing_time = analysis_result.get("processing_time", 0)

                self.logger.info(
                    f"✨ Discovered {n_patterns} behavioral patterns using {method_used} "
                    f"in {processing_time:.2f}s"
                )

                # Share insights with embryos
                await self._distribute_pattern_insights(analysis_result)

                self.last_clustering_time = time.time()

        except Exception as e:
            self.logger.error(f"Clustering analysis error: {e}")

    async def _enhance_event_with_patterns(self, event_data: dict) -> dict:
        """Enhance event data with pattern insights for smarter processing"""
        enhanced_event = event_data.copy()

        if self.pattern_insights:
            enhanced_event["pattern_context"] = {
                "insights": self.pattern_insights[:3],  # Top 3 insights
                "analysis_timestamp": self.last_clustering_time,
                "total_patterns_discovered": len(
                    self.clustering_system.latest_analysis.get("patterns", {})
                ),
            }

        return enhanced_event

    async def _distribute_pattern_insights(self, analysis_result: dict):
        """Distribute pattern insights to embryos for enhanced learning"""
        patterns = analysis_result.get("patterns", {})
        insights = analysis_result.get("insights", [])

        # Create pattern summary for embryos
        pattern_summary = {
            "total_patterns": len(patterns),
            "dominant_patterns": [],
            "behavioral_insights": insights,
            "clustering_method": analysis_result.get("method_used", "unknown"),
            "analysis_quality": analysis_result.get("metrics", {}),
        }

        # Extract top patterns
        for pattern_id, pattern in list(patterns.items())[:5]:  # Top 5 patterns
            pattern_summary["dominant_patterns"].append(
                {
                    "id": pattern_id,
                    "size": pattern.get("size", 0),
                    "description": pattern.get("description", ""),
                    "intensity": pattern.get("intensity", 0),
                    "peak_hour": pattern.get("peak_hour", 0),
                }
            )

        # Distribute to embryos for learning enhancement
        for embryo in self.embryos.values():
            try:
                await embryo.update_pattern_knowledge(pattern_summary)
            except Exception as e:
                self.logger.debug(
                    f"Pattern distribution error for embryo {embryo.embryo_id}: {e}"
                )

    def _should_evolve(self) -> bool:
        """Determine if the pool should evolve"""
        # This is a placeholder implementation. In a full implementation,
        # this method would implement the logic to determine if the pool should
        # evolve based on the current state of the pool and the evolution strategy.
        return False

    async def _evolve_pool(self):
        """Perform evolution on the embryo pool"""
        # This is a placeholder implementation. In a full implementation,
        # this method would implement the logic to evolve the pool based on the
        # current state of the pool and the evolution strategy.
        pass

    def get_pool_statistics(self) -> dict:
        """Get comprehensive pool statistics including clustering insights"""
        uptime = time.time() - self.start_time

        stats = {
            "pool_size": len(self.embryos),
            "current_generation": self.generation,
            "total_events_processed": self.pool_stats["events_processed"],
            "events_per_second": (
                self.pool_stats["events_processed"] / uptime if uptime > 0 else 0
            ),
            "uptime_hours": uptime / 3600,
            "evolution_cycles": self.generation,
            "avg_fitness": self.pool_stats["avg_fitness"],
            "best_fitness": (
                max([e.calculate_fitness() for e in self.embryos.values()])
                if self.embryos
                else 0
            ),
            "event_buffer_size": len(self.event_buffer),
            "clustering_enabled": CLUSTERING_AVAILABLE
            and self.clustering_system is not None,
        }

        # Add clustering statistics if available
        if self.clustering_system:
            clustering_stats = self.clustering_system.get_statistics()
            stats.update(
                {
                    "clustering_analyses": clustering_stats.get(
                        "analyses_performed", 0
                    ),
                    "total_events_analyzed": clustering_stats.get(
                        "total_events_analyzed", 0
                    ),
                    "latest_pattern_count": clustering_stats.get(
                        "latest_pattern_count", 0
                    ),
                    "last_clustering_time": clustering_stats.get(
                        "last_analysis_time", 0
                    ),
                    "pattern_insights": len(self.pattern_insights),
                }
            )

        return stats

    def get_latest_insights(self) -> list:
        """Get latest behavioral insights from clustering analysis"""
        if self.clustering_system:
            return self.clustering_system.get_latest_insights()
        return []

    async def remove_embryo(self, embryo_id: str):
        """Remove an embryo from the pool"""
        if embryo_id in self.embryos:
            await self._cull_embryo(embryo_id, "agent_birth")
            self.logger.info(f"Embryo {embryo_id} removed - agent born")
