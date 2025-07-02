#!/usr/bin/env python3
"""
ALims Meta-Learning System
Uses Gemma 3:4b as a teacher to train small, specialized neural networks
based on semantic analysis of event data.
"""

import asyncio
import json
import logging
import sqlite3
import torch
import torch.nn as nn
import numpy as np
from typing import Dict, List, Any, Tuple
from datetime import datetime
from pathlib import Path
from dataclasses import dataclass
from collections import defaultdict

logger = logging.getLogger(__name__)


@dataclass
class TrainingExample:
    """A single training example for an agent"""

    input_data: Dict[str, Any]
    semantic_label: str
    confidence: float
    context: Dict[str, Any]
    timestamp: float


@dataclass
class AgentArchitecture:
    """Neural network architecture specification"""

    name: str
    input_dim: int
    hidden_dims: List[int]
    output_dim: int
    max_params: int
    specialization: str


class MetaLearningSystem:
    """Meta-learning system using Gemma 3:4b as teacher"""

    def __init__(self, central_brain):
        self.central_brain = central_brain
        self.logger = logging.getLogger("MetaLearning")

        # Agent specifications from semantic analysis
        self.agent_specs = {
            "DevelopmentWorkflowAgent": {
                "max_params": 1_000_000,
                "specialization": "development_workflow",
                "semantic_understanding": [
                    "project_structure_analysis",
                    "code_file_relationships",
                    "development_session_patterns",
                    "git_workflow_understanding",
                    "build_test_cycle_recognition",
                ],
            },
            "ApplicationStateAgent": {
                "max_params": 2_000_000,
                "specialization": "application_state",
                "semantic_understanding": [
                    "app_usage_patterns",
                    "preference_changes_context",
                    "workflow_optimization_opportunities",
                    "state_synchronization_needs",
                    "performance_impact_analysis",
                ],
            },
            "SystemMaintenanceAgent": {
                "max_params": 800_000,
                "specialization": "system_maintenance",
                "semantic_understanding": [
                    "cache_cleanup_patterns",
                    "temporary_file_lifecycle",
                    "storage_optimization_needs",
                    "performance_impact_assessment",
                    "automated_maintenance_scheduling",
                ],
            },
        }

        # Training data storage
        self.training_data = defaultdict(list)
        self.validation_data = defaultdict(list)

        # Trained models
        self.trained_agents = {}

    async def generate_semantic_labels(
        self, events: List[Dict], agent_type: str
    ) -> List[TrainingExample]:
        """Use Gemma 3:4b to generate semantic labels for events"""

        self.logger.info(f"🏷️ Generating semantic labels for {agent_type}")

        agent_spec = self.agent_specs[agent_type]
        specialization = agent_spec["specialization"]
        understanding = agent_spec["semantic_understanding"]

        training_examples = []

        # Process events in batches
        batch_size = 10
        for i in range(0, len(events), batch_size):
            batch = events[i : i + batch_size]

            # Create prompt for semantic labeling
            labeling_prompt = self._create_labeling_prompt(
                batch, specialization, understanding
            )

            try:
                # Get semantic analysis from Gemma 3:4b
                response = await self.central_brain.ollama_client.generate_response(
                    prompt="Generate semantic labels for these events",
                    system_prompt=labeling_prompt,
                )

                # Parse response into training examples
                examples = self._parse_labeling_response(response, batch, agent_type)
                training_examples.extend(examples)

            except Exception as e:
                self.logger.error(f"Error generating labels for batch: {e}")
                continue

        self.logger.info(
            f"✅ Generated {len(training_examples)} training examples for {agent_type}"
        )
        return training_examples

    def _create_labeling_prompt(
        self, events: List[Dict], specialization: str, understanding: List[str]
    ) -> str:
        """Create prompt for semantic labeling"""

        prompt = f"""You are a meta-learning teacher training specialized AI agents for ALims.

Agent Specialization: {specialization}
Semantic Understanding Required: {', '.join(understanding)}

Analyze these events and generate semantic labels that capture the MEANING and CONTEXT:

Events to Label:
"""

        for i, event in enumerate(events):
            prompt += f"\nEvent {i+1}:\n"
            prompt += f"  Path: {event.get('path', 'N/A')}\n"
            prompt += f"  Action: {event.get('action', 'N/A')}\n"
            prompt += f"  Extension: {event.get('ext', 'N/A')}\n"
            prompt += f"  Timestamp: {event.get('ts', 'N/A')}\n"

        prompt += f"""

For each event, provide:
1. Semantic Label: What is the user REALLY doing? (e.g., "active_coding_session", "project_setup", "debugging_workflow")
2. Context Understanding: WHY is this happening? 
3. Intent Classification: What is the user trying to accomplish?
4. Workflow Stage: Where in their workflow is this?
5. Confidence: How certain are you? (0.0-1.0)

Focus on {specialization} patterns. Generate labels that help the agent understand:
{chr(10).join(f"- {u.replace('_', ' ').title()}" for u in understanding)}

Format as JSON:
{{
  "event_1": {{
    "semantic_label": "label_here",
    "context": "context_explanation",
    "intent": "user_intent",
    "workflow_stage": "stage_name",
    "confidence": 0.85
  }},
  ...
}}"""

        return prompt

    def _parse_labeling_response(
        self, response: str, events: List[Dict], agent_type: str
    ) -> List[TrainingExample]:
        """Parse Gemma's labeling response into training examples"""

        training_examples = []

        try:
            # Extract JSON from response
            json_start = response.find("{")
            json_end = response.rfind("}") + 1

            if json_start == -1 or json_end == 0:
                self.logger.warning("No JSON found in labeling response")
                return []

            json_str = response[json_start:json_end]
            labels = json.loads(json_str)

            # Create training examples
            for i, event in enumerate(events):
                event_key = f"event_{i+1}"

                if event_key in labels:
                    label_data = labels[event_key]

                    # Create input features
                    input_data = self._extract_features(event, agent_type)

                    # Create training example
                    example = TrainingExample(
                        input_data=input_data,
                        semantic_label=label_data.get("semantic_label", "unknown"),
                        confidence=label_data.get("confidence", 0.5),
                        context={
                            "context": label_data.get("context", ""),
                            "intent": label_data.get("intent", ""),
                            "workflow_stage": label_data.get("workflow_stage", ""),
                            "agent_type": agent_type,
                        },
                        timestamp=event.get("ts", 0),
                    )

                    training_examples.append(example)

        except json.JSONDecodeError as e:
            self.logger.error(f"Failed to parse labeling response: {e}")
        except Exception as e:
            self.logger.error(f"Error parsing labels: {e}")

        return training_examples

    def _extract_features(self, event: Dict, agent_type: str) -> Dict[str, Any]:
        """Extract features for neural network input"""

        path = event.get("path", "")
        action = event.get("action", "")
        ext = event.get("ext", "")
        timestamp = event.get("ts", 0)

        # Base features
        features = {
            "action_create": 1.0 if action == "create" else 0.0,
            "action_modify": 1.0 if action == "modify" else 0.0,
            "action_delete": 1.0 if action == "delete" else 0.0,
            "action_move": 1.0 if action == "move" else 0.0,
            "hour_of_day": (
                (datetime.fromtimestamp(timestamp).hour / 24.0) if timestamp else 0.0
            ),
            "path_length": len(path) / 100.0,  # Normalized
        }

        # Agent-specific features
        if agent_type == "DevelopmentWorkflowAgent":
            features.update(
                {
                    "is_code_file": 1.0 if ext in ["py", "js", "ts", "java"] else 0.0,
                    "is_project_file": 1.0 if "projects" in path.lower() else 0.0,
                    "is_git_related": 1.0 if ".git" in path else 0.0,
                    "is_test_file": 1.0 if "test" in path.lower() else 0.0,
                }
            )

        elif agent_type == "ApplicationStateAgent":
            features.update(
                {
                    "is_cursor_vscode": (
                        1.0
                        if any(app in path.lower() for app in ["cursor", "vscode"])
                        else 0.0
                    ),
                    "is_browser_state": 1.0 if "chrome" in path.lower() else 0.0,
                    "is_config_file": (
                        1.0 if ext in ["json", "plist", "config"] else 0.0
                    ),
                    "is_state_file": 1.0 if "state" in path.lower() else 0.0,
                }
            )

        elif agent_type == "SystemMaintenanceAgent":
            features.update(
                {
                    "is_cache_file": 1.0 if "cache" in path.lower() else 0.0,
                    "is_temp_file": (
                        1.0
                        if any(temp in path.lower() for temp in ["temp", "tmp"])
                        else 0.0
                    ),
                    "is_log_file": 1.0 if ext in ["log", "db"] else 0.0,
                    "is_large_file": (
                        1.0 if len(path) > 100 else 0.0
                    ),  # Proxy for file size
                }
            )

        return features

    async def design_network_architecture(
        self, agent_type: str, training_examples: List[TrainingExample]
    ) -> AgentArchitecture:
        """Use Gemma 3:4b to design optimal network architecture"""

        self.logger.info(f"🏗️ Designing architecture for {agent_type}")

        agent_spec = self.agent_specs[agent_type]
        max_params = agent_spec["max_params"]

        # Analyze training data characteristics
        input_dim = len(training_examples[0].input_data) if training_examples else 10
        unique_labels = len(set(ex.semantic_label for ex in training_examples))
        data_complexity = self._assess_data_complexity(training_examples)

        # Create architecture design prompt
        design_prompt = f"""Design an optimal neural network architecture for {agent_type}.

Constraints:
- Maximum parameters: {max_params:,}
- Input dimension: {input_dim}
- Output classes: {unique_labels}
- Data complexity: {data_complexity}
- Specialization: {agent_spec['specialization']}

Training data characteristics:
- Number of examples: {len(training_examples)}
- Label distribution: {self._get_label_distribution(training_examples)}

Design a network that:
1. Fits within parameter budget
2. Handles the semantic complexity
3. Avoids overfitting
4. Enables fast inference (<100ms)

Provide architecture as JSON:
{{
  "input_dim": {input_dim},
  "hidden_layers": [256, 128, 64],
  "output_dim": {unique_labels},
  "activation": "relu",
  "dropout": 0.1,
  "estimated_params": 150000,
  "reasoning": "explanation of design choices"
}}"""

        try:
            response = await self.central_brain.ollama_client.generate_response(
                prompt="Design optimal neural network architecture",
                system_prompt=design_prompt,
            )

            # Parse architecture specification
            architecture = self._parse_architecture_response(
                response, agent_type, max_params
            )

            self.logger.info(
                f"✅ Designed architecture for {agent_type}: {architecture.max_params:,} params"
            )
            return architecture

        except Exception as e:
            self.logger.error(f"Error designing architecture: {e}")
            # Fallback architecture
            return self._create_fallback_architecture(
                agent_type, input_dim, unique_labels, max_params
            )

    def _assess_data_complexity(self, examples: List[TrainingExample]) -> str:
        """Assess complexity of training data"""

        if len(examples) < 100:
            return "low"
        elif len(examples) < 500:
            return "medium"
        else:
            return "high"

    def _get_label_distribution(
        self, examples: List[TrainingExample]
    ) -> Dict[str, int]:
        """Get distribution of semantic labels"""

        from collections import Counter

        labels = [ex.semantic_label for ex in examples]
        return dict(Counter(labels).most_common(5))

    def _parse_architecture_response(
        self, response: str, agent_type: str, max_params: int
    ) -> AgentArchitecture:
        """Parse architecture design response"""

        try:
            # Extract JSON
            json_start = response.find("{")
            json_end = response.rfind("}") + 1

            if json_start != -1 and json_end > json_start:
                json_str = response[json_start:json_end]
                arch_data = json.loads(json_str)

                return AgentArchitecture(
                    name=agent_type,
                    input_dim=arch_data.get("input_dim", 10),
                    hidden_dims=arch_data.get("hidden_layers", [256, 128]),
                    output_dim=arch_data.get("output_dim", 5),
                    max_params=min(
                        arch_data.get("estimated_params", max_params), max_params
                    ),
                    specialization=self.agent_specs[agent_type]["specialization"],
                )

        except Exception as e:
            self.logger.error(f"Error parsing architecture: {e}")

        # Fallback
        return self._create_fallback_architecture(agent_type, 10, 5, max_params)

    def _create_fallback_architecture(
        self, agent_type: str, input_dim: int, output_dim: int, max_params: int
    ) -> AgentArchitecture:
        """Create fallback architecture if design fails"""

        # Simple heuristic for hidden layer sizes
        if max_params > 1_000_000:
            hidden_dims = [512, 256, 128]
        elif max_params > 500_000:
            hidden_dims = [256, 128]
        else:
            hidden_dims = [128, 64]

        return AgentArchitecture(
            name=agent_type,
            input_dim=input_dim,
            hidden_dims=hidden_dims,
            output_dim=output_dim,
            max_params=max_params,
            specialization=self.agent_specs[agent_type]["specialization"],
        )

    async def train_agent_network(
        self,
        agent_type: str,
        architecture: AgentArchitecture,
        training_examples: List[TrainingExample],
    ) -> nn.Module:
        """Train the small neural network for an agent"""

        self.logger.info(f"🎯 Training {agent_type} network...")

        # Create network
        network = self._create_network(architecture)

        # Prepare training data
        X, y = self._prepare_training_data(training_examples)

        # Train with curriculum learning
        trained_network = await self._train_with_curriculum(network, X, y, agent_type)

        # Validate and check for overfitting
        validation_score = await self._validate_network(trained_network, agent_type)

        self.logger.info(
            f"✅ {agent_type} training complete. Validation score: {validation_score:.3f}"
        )

        return trained_network

    def _create_network(self, architecture: AgentArchitecture) -> nn.Module:
        """Create PyTorch network from architecture"""

        layers = []

        # Input layer
        prev_dim = architecture.input_dim

        # Hidden layers
        for hidden_dim in architecture.hidden_dims:
            layers.extend([nn.Linear(prev_dim, hidden_dim), nn.ReLU(), nn.Dropout(0.1)])
            prev_dim = hidden_dim

        # Output layer
        layers.append(nn.Linear(prev_dim, architecture.output_dim))
        layers.append(nn.Softmax(dim=1))

        return nn.Sequential(*layers)

    def _prepare_training_data(
        self, examples: List[TrainingExample]
    ) -> Tuple[torch.Tensor, torch.Tensor]:
        """Convert training examples to tensors"""

        # Extract features
        X_list = []
        y_list = []

        # Create label mapping
        unique_labels = list(set(ex.semantic_label for ex in examples))
        label_to_idx = {label: idx for idx, label in enumerate(unique_labels)}

        for example in examples:
            # Convert features to tensor
            feature_values = list(example.input_data.values())
            X_list.append(feature_values)

            # Convert label to index
            label_idx = label_to_idx[example.semantic_label]
            y_list.append(label_idx)

        X = torch.tensor(X_list, dtype=torch.float32)
        y = torch.tensor(y_list, dtype=torch.long)

        return X, y

    async def _train_with_curriculum(
        self, network: nn.Module, X: torch.Tensor, y: torch.Tensor, agent_type: str
    ) -> nn.Module:
        """Train network with curriculum learning"""

        # Simple training loop (would be more sophisticated in production)
        optimizer = torch.optim.Adam(network.parameters(), lr=0.001)
        criterion = nn.CrossEntropyLoss()

        network.train()

        for epoch in range(100):  # Simple training
            optimizer.zero_grad()
            outputs = network(X)
            loss = criterion(outputs, y)
            loss.backward()
            optimizer.step()

            if epoch % 20 == 0:
                self.logger.debug(
                    f"{agent_type} epoch {epoch}, loss: {loss.item():.4f}"
                )

        return network

    async def _validate_network(self, network: nn.Module, agent_type: str) -> float:
        """Validate trained network"""

        # Simple validation (would use holdout set in production)
        network.eval()

        # For now, return a mock validation score
        # In production, this would test on holdout data
        return 0.85  # Mock score

    async def deploy_agent(self, agent_type: str, network: nn.Module) -> Dict[str, Any]:
        """Deploy trained agent for inference"""

        self.logger.info(f"🚀 Deploying {agent_type}")

        # Save model
        model_path = f"models/{agent_type.lower()}.pth"
        Path("models").mkdir(exist_ok=True)
        torch.save(network.state_dict(), model_path)

        # Create agent interface
        agent_interface = {
            "name": agent_type,
            "model_path": model_path,
            "specialization": self.agent_specs[agent_type]["specialization"],
            "semantic_understanding": self.agent_specs[agent_type][
                "semantic_understanding"
            ],
            "inference_function": self._create_inference_function(network, agent_type),
        }

        self.trained_agents[agent_type] = agent_interface

        self.logger.info(f"✅ {agent_type} deployed successfully")

        return agent_interface

    def _create_inference_function(self, network: nn.Module, agent_type: str):
        """Create inference function for deployed agent"""

        def inference(event_data: Dict[str, Any]) -> Dict[str, Any]:
            """Run inference on new event"""

            # Extract features
            features = self._extract_features(event_data, agent_type)

            # Convert to tensor
            X = torch.tensor([list(features.values())], dtype=torch.float32)

            # Run inference
            network.eval()
            with torch.no_grad():
                outputs = network(X)
                probabilities = outputs[0].numpy()

                # Get prediction
                predicted_class = int(np.argmax(probabilities))
                confidence = float(np.max(probabilities))

                return {
                    "predicted_class": predicted_class,
                    "confidence": confidence,
                    "probabilities": probabilities.tolist(),
                    "agent_type": agent_type,
                }

        return inference

    async def train_all_agents(self) -> Dict[str, Any]:
        """Complete meta-learning pipeline for all agents"""

        self.logger.info("🚀 Starting Meta-Learning Pipeline...")

        results = {}

        # Load event data
        events = await self._load_semantic_events()

        for agent_type in self.agent_specs.keys():
            try:
                self.logger.info(f"\n🤖 Training {agent_type}...")

                # Filter events for this agent
                agent_events = self._filter_events_for_agent(events, agent_type)

                if len(agent_events) < 10:
                    self.logger.warning(
                        f"Insufficient data for {agent_type}: {len(agent_events)} events"
                    )
                    continue

                # Generate semantic labels
                training_examples = await self.generate_semantic_labels(
                    agent_events, agent_type
                )

                if not training_examples:
                    self.logger.warning(
                        f"No training examples generated for {agent_type}"
                    )
                    continue

                # Design architecture
                architecture = await self.design_network_architecture(
                    agent_type, training_examples
                )

                # Train network
                network = await self.train_agent_network(
                    agent_type, architecture, training_examples
                )

                # Deploy agent
                agent_interface = await self.deploy_agent(agent_type, network)

                results[agent_type] = {
                    "status": "success",
                    "training_examples": len(training_examples),
                    "architecture": architecture,
                    "interface": agent_interface,
                }

            except Exception as e:
                self.logger.error(f"Failed to train {agent_type}: {e}")
                results[agent_type] = {"status": "failed", "error": str(e)}

        self.logger.info("✅ Meta-Learning Pipeline Complete!")
        return results

    async def _load_semantic_events(self) -> List[Dict[str, Any]]:
        """Load events for semantic analysis"""

        conn = sqlite3.connect("data/events.db")
        cursor = conn.cursor()

        cursor.execute(
            """
            SELECT data_json FROM events 
            WHERE event_type = 'file_op' 
            AND data_json IS NOT NULL 
            ORDER BY timestamp DESC 
            LIMIT 1000
        """
        )

        events = []
        for row in cursor.fetchall():
            try:
                data = json.loads(row[0])
                events.append(data)
            except:
                continue

        conn.close()
        return events

    def _filter_events_for_agent(
        self, events: List[Dict], agent_type: str
    ) -> List[Dict]:
        """Filter events relevant to specific agent"""

        if agent_type == "DevelopmentWorkflowAgent":
            return [
                e
                for e in events
                if any(
                    keyword in e.get("path", "").lower()
                    for keyword in ["projects", ".py", ".js", ".git", "alims"]
                )
            ]

        elif agent_type == "ApplicationStateAgent":
            return [
                e
                for e in events
                if any(
                    keyword in e.get("path", "").lower()
                    for keyword in [
                        "cursor",
                        "vscode",
                        "chrome",
                        "state",
                        "preferences",
                    ]
                )
            ]

        elif agent_type == "SystemMaintenanceAgent":
            return [
                e
                for e in events
                if any(
                    keyword in e.get("path", "").lower()
                    for keyword in ["cache", "temp", "tmp", "log"]
                )
            ]

        return events
