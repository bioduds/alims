# Phase 1: Data Analysis & Tray Visualization Plan

## 🎯 Objective
Create a **continuous data collection and analysis pipeline** that:
- **Continuously gathers** user behavior data with intelligent buffering
- **Performs real-time clustering and semantic analysis** when data thresholds are met
- **Automatically triggers meta-learning phases** for micro-agent training
- **Provides tray visualization** to make the continuous learning process transparent
- **Establishes the foundation** for the self-evolving AI ecosystem

## 💡 **NEW: Continuous Learning Integration**
Based on the small model training system concept, Phase 1 will now include:
- **SmolLM-1.7B** as the base for micro-agents (1GB VRAM, Apache-2.0 license)
- **Continuous data capture** with size budgets (64MB per training cycle)
- **Real-time model training** visible in tray interface
- **Multi-armed bandit selection** for model performance evaluation
- **Advanced clustering** beyond k-means for pattern discovery

## 📊 Current State Analysis

### ✅ What We Have
- **130MB events.db** with 130K+ file operations and app events
- **Existing analysis scripts**: `analyze_event_data.py`, `cluster_file_operations.py`, `analyze_semantic_content.py`
- **Working tray system**: `app/system/macos_tray.py` with basic menu structure
- **Data insights**: Memory shows 99.4% file operations, 0.6% app events
- **Natural clusters identified**: GeneralFileAgent (95.2% of data), SystemAgent (4.8% of data)

### 🔧 What We Need
- **Real-time data dashboard** integrated into tray
- **Visual pattern representation** with charts and graphs
- **Interactive data exploration** directly from menu bar
- **Live metrics** showing system learning progress
- **Pattern detection alerts** when new behaviors emerge
- **🆕 Micro-agent training visualization** - watch models being born!
- **🆕 Multi-clustering analysis** using HDBSCAN, Spectral, GMM
- **🆕 Model performance dashboard** with bandit selection metrics

## 🚀 Implementation Plan

### Week 1: Continuous Data Pipeline + Meta-Learning Triggers

#### Day 1-2: Continuous Data Collection Engine
```python
# Create: app/analytics/continuous_data_pipeline.py
class ContinuousDataPipeline:
    def __init__(self):
        self.db_path = "data/events.db"
        self.data_budget = 64 * 1024 * 1024  # 64MB per meta-learning cycle
        self.current_buffer = []
        self.current_buffer_size = 0
        self.meta_learning_trigger = None
        self.is_collecting = True
        
    def continuous_data_collection(self):
        """Main continuous loop - never stops collecting"""
        while True:
            # Collect new events
            new_events = self._collect_recent_events()
            
            # Add to buffer
            for event in new_events:
                self._add_to_buffer(event)
                
            # Check if we have enough data for analysis
            if self._should_trigger_analysis():
                self._trigger_meta_learning_phase()
                
            time.sleep(1)  # Collect every second
    
    def _should_trigger_analysis(self):
        """Evaluate if we have enough quality data for clustering/semantic analysis"""
        return (
            self.current_buffer_size >= (self.data_budget * 0.9) and
            self._has_sufficient_diversity() and
            self._has_meaningful_patterns()
        )
        
    def _trigger_meta_learning_phase(self):
        """Trigger the next phase: clustering -> semantic analysis -> micro-agent training"""
        print("🧬 Triggering Meta-Learning Phase...")
        
        # 1. Perform clustering analysis
        clusters = self._perform_clustering_analysis()
        
        # 2. Semantic analysis of clusters
        semantic_patterns = self._analyze_semantic_patterns(clusters)
        
        # 3. Determine if new micro-agent specializations are needed
        specializations = self._evaluate_specialization_needs(semantic_patterns)
        
        # 4. Trigger micro-agent training if needed
        if specializations:
            self._queue_micro_agent_training(specializations)
            
        # 5. Reset buffer for next cycle
        self._reset_buffer()
        
    def _perform_clustering_analysis(self):
        """Multi-algorithm clustering to find natural patterns"""
        # This is where the advanced clustering happens
        # Returns cluster assignments and confidence scores
        pass
        
    def _analyze_semantic_patterns(self, clusters):
        """Deep semantic analysis of discovered clusters"""
        # Extract meaning from clusters
        # Identify behavior patterns and specialization opportunities
        pass
```

#### Day 3-4: Advanced Clustering Engine
```python
# Create: app/analytics/advanced_clustering.py
import hdbscan
from sklearn.cluster import SpectralClustering
from sklearn.mixture import GaussianMixture
import networkx as nx

class AdvancedClusteringEngine:
    def __init__(self):
        self.clusterers = {
            'hdbscan': hdbscan.HDBSCAN(min_cluster_size=50),
            'spectral': SpectralClustering(n_clusters=8),
            'gmm': GaussianMixture(n_components=8),
            'density': self._density_clustering,
            'hierarchical': self._hierarchical_clustering
        }
    
    def multi_cluster_analysis(self, events):
        """Run multiple clustering algorithms and compare results"""
        results = {}
        feature_matrix = self._extract_features(events)
        
        for name, clusterer in self.clusterers.items():
            try:
                labels = clusterer.fit_predict(feature_matrix)
                results[name] = {
                    'labels': labels,
                    'silhouette_score': self._calculate_silhouette(feature_matrix, labels),
                    'n_clusters': len(set(labels)) - (1 if -1 in labels else 0),
                    'confidence': self._calculate_clustering_confidence(labels)
                }
            except Exception as e:
                results[name] = {'error': str(e)}
                
        return results
    
    def detect_natural_specializations(self, events):
        """Use ensemble clustering to find natural agent specializations"""
        # Combine multiple clustering approaches
        # Identify stable clusters across methods
        # Suggest micro-agent specializations
        pass
```

#### Day 5: Micro-Agent Training System
```python
# Create: app/training/micro_agent_trainer.py
from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
from peft import LoraConfig, get_peft_model, TaskType
import torch

class MicroAgentTrainer:
    def __init__(self):
        self.base_model = "HuggingFaceTB/SmolLM-1.7B-Instruct"
        self.training_queue = []
        self.active_models = {}  # model_id -> {model, score, deployment_time}
        self.max_models = 5  # Keep top 5 performing models
        
    def setup_training_environment(self):
        """Setup 4-bit quantized SmolLM for efficient training"""
        bnb_config = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_compute_dtype=torch.float16,
            bnb_4bit_use_double_quant=True
        )
        
        self.tokenizer = AutoTokenizer.from_pretrained(self.base_model)
        self.base_model_obj = AutoModelForCausalLM.from_pretrained(
            self.base_model,
            quantization_config=bnb_config,
            device_map="auto"
        )
        
    def create_specialized_agent(self, training_data, specialization_name):
        """Train a specialized micro-agent using LoRA"""
        lora_config = LoraConfig(
            task_type=TaskType.CAUSAL_LM,
            r=8,  # Low rank for efficiency
            lora_alpha=16,
            lora_dropout=0.1,
            target_modules=["q_proj", "v_proj"]
        )
        
        # This would run in background thread
        model_id = f"{specialization_name}_{int(time.time())}"
        
        # Training progress will be visible in tray
        self._train_with_progress_tracking(model_id, training_data, lora_config)
```

### Week 2: Enhanced Tray Interface with Training Visualization

#### Day 6-8: Smart Tray Menu System with Live Training
```python
# Enhance: app/system/macos_tray.py
class EnhancedALimsTray(rumps.App):
    def __init__(self):
        super().__init__("🧠 ALims")
        self.data_engine = ALimsDataEngine()
        self.viz_engine = TrayVisualizationEngine()
        self.trainer = MicroAgentTrainer()
        self.setup_smart_menu()
        
    def setup_smart_menu(self):
        """Dynamic menu with live data and training status"""
        self.menu = [
            "📊 Live Dashboard",
            "🔍 Advanced Pattern Explorer", 
            "📈 Today's Activity",
            "🧬 Data Insights",
            "🤖 Micro-Agents (5 active)",  # NEW
            "🏗️ Training Status",  # NEW
            rumps.separator,
            "⚙️ Settings"
        ]
        
    @rumps.timer(30)  # Update every 30 seconds
    def update_live_menu(self, _):
        """Update menu with live data including training progress"""
        metrics = self.data_engine.get_real_time_metrics()
        
        # Update existing metrics
        self.menu["📊 Live Dashboard"].title = f"📊 Dashboard ({metrics['events_today']} events today)"
        
        # NEW: Update training status
        buffer_pct = int(metrics['buffer_fullness'] * 100)
        if buffer_pct >= 90:
            self.menu["🏗️ Training Status"].title = f"🏗️ Training Ready! ({buffer_pct}%)"
        else:
            self.menu["🏗️ Training Status"].title = f"🏗️ Collecting Data ({buffer_pct}%)"
            
        # NEW: Update micro-agents count
        agent_count = metrics['total_micro_agents']
        training_count = metrics['models_training']
        if training_count > 0:
            self.menu["🤖 Micro-Agents"].title = f"🤖 Agents ({agent_count} active, {training_count} training)"
        else:
            self.menu["🤖 Micro-Agents"].title = f"🤖 Micro-Agents ({agent_count} active)"
        
        # Check for training completion
        self._check_training_completions()
```

#### Day 9-10: Training Visualization Dashboard
```python
# Create: app/visualization/training_dashboard.py
class TrainingVisualizationDashboard:
    def show_training_dashboard(self):
        """Show live training progress and model performance"""
        window = tk.Tk()
        window.title("🏗️ ALims Micro-Agent Training Center")
        window.geometry("1000x800")
        
        # Training Queue Panel
        self._create_training_queue_panel(window)
        
        # Active Training Progress
        self._create_training_progress_panel(window)
        
        # Model Performance Comparison
        self._create_model_performance_panel(window)
        
        # Bandit Selection Metrics
        self._create_bandit_metrics_panel(window)
        
    def show_clustering_analysis(self):
        """Advanced clustering visualization"""
        window = tk.Tk()
        window.title("🔍 Advanced Pattern Clustering")
        window.geometry("1200x900")
        
        # Multi-algorithm comparison
        self._create_clustering_comparison(window)
        
        # Interactive cluster exploration
        self._create_cluster_explorer(window)
        
        # Specialization suggestions
        self._create_specialization_suggestions(window)
```

### Week 3: Advanced Analytics + Model Performance Tracking

#### Day 11-13: Multi-Armed Bandit Selection System
```python
# Create: app/analytics/model_selector.py
import numpy as np
from scipy import stats

class ModelBanditSelector:
    def __init__(self, exploration_rate=0.1):
        self.exploration_rate = exploration_rate
        self.model_stats = {}  # model_id -> {successes, attempts, last_update}
        
    def select_model_for_query(self, available_models):
        """Select best model using epsilon-greedy bandit"""
        if np.random.random() < self.exploration_rate:
            # Explore: random selection
            return np.random.choice(available_models)
        else:
            # Exploit: select best performing
            return self._get_best_model(available_models)
            
    def update_model_performance(self, model_id, success, latency_ms):
        """Update model performance metrics"""
        if model_id not in self.model_stats:
            self.model_stats[model_id] = {
                'successes': 0, 'attempts': 0, 'total_latency': 0,
                'confidence_interval': (0, 1), 'last_update': time.time()
            }
            
        stats = self.model_stats[model_id]
        stats['attempts'] += 1
        stats['total_latency'] += latency_ms
        
        if success:
            stats['successes'] += 1
            
        # Update confidence interval using Beta distribution
        alpha = stats['successes'] + 1
        beta = stats['attempts'] - stats['successes'] + 1
        stats['confidence_interval'] = stats.beta.interval(0.95, alpha, beta)
        stats['last_update'] = time.time()
        
    def get_model_rankings(self):
        """Get current model performance rankings"""
        rankings = []
        for model_id, stats in self.model_stats.items():
            success_rate = stats['successes'] / max(stats['attempts'], 1)
            avg_latency = stats['total_latency'] / max(stats['attempts'], 1)
            
            rankings.append({
                'model_id': model_id,
                'success_rate': success_rate,
                'avg_latency_ms': avg_latency,
                'confidence_interval': stats['confidence_interval'],
                'total_queries': stats['attempts']
            })
            
        return sorted(rankings, key=lambda x: x['success_rate'], reverse=True)
```

## 📱 Enhanced Tray Interface Design

### Main Menu Structure (Updated)
```
🧠 ALims
├── 📊 Live Dashboard (2,847 events today)
├── 🔍 Advanced Pattern Explorer (HDBSCAN: 23 patterns)
├── 📈 Today's Activity
│   ├── 🔥 Hot Patterns
│   │   ├── Intensive coding (92% confidence)
│   │   ├── Cache optimization (87% confidence)
│   │   └── Multi-project workflow (81% confidence)
│   ├── 📊 File Operations (2,234 today)
│   ├── 🎯 Focus Time (3h 42m)
│   └── 🔄 Workflow Efficiency (84%)
├── 🤖 Micro-Agents (5 active, 1 training)
│   ├── 🥇 CodeAgent-1.2 (94% success rate)
│   ├── 🥈 FileAgent-2.1 (89% success rate)  
│   ├── 🥉 SystemAgent-1.0 (87% success rate)
│   ├── 🔄 WebAgent-1.5 (training 67%)
│   └── 📊 Performance Dashboard
├── 🏗️ Training Center (Data: 87% full)
│   ├── 📦 Training Queue (2 waiting)
│   ├── 🔬 Cluster Analysis (HDBSCAN/GMM/Spectral)
│   ├── 📈 Model Performance
│   └── ⚙️ Training Settings
├── 🧬 Data Insights
│   ├── 🎓 Learning Progress
│   ├── 🔬 Multi-Cluster Analysis
│   ├── 📈 Trend Detection
│   └── 💡 Optimization Suggestions
├── 🔔 Notifications (3 new)
├── ⚙️ Settings
└── 🔄 Refresh Data
```

### Training Center Dashboard Layout
```
┌─────────────────────────────────────────────────────────┐
│ 🏗️ ALims Training Center - Living AI Evolution       │
├─────────────────────────────────────────────────────────┤
│ 📦 Data Buffer: 87% (56MB/64MB) ⏱️ Training in 2h 15m  │
├─────────────────────────────────────────────────────────┤
│ ┌─────────────────┐ ┌─────────────────┐ ┌─────────────┐ │
│ │ Training Queue  │ │ Active Training │ │ Performance │ │
│ │ • CodeAgent v1.3│ │ WebAgent-1.5    │ │ 🥇 CodeAgent│ │
│ │ • SystemAgent   │ │ [████████░░] 67%│ │    94% ✅   │ │
│ │ • FileAgent v2.2│ │ ETA: 45m        │ │ 🥈 FileAgent│ │
│ └─────────────────┘ └─────────────────┘ │    89% ✅   │ │
├─────────────────────────────────────────┐ └─────────────┘ │
│ 🔬 Multi-Clustering Analysis:           │               │
│ • HDBSCAN: 23 patterns (confidence: 94%)│               │
│ • Spectral: 18 patterns (confidence: 87%)               │
│ • GMM: 15 patterns (confidence: 91%)    │               │
│ • Consensus: 12 stable patterns ✅      │               │
├─────────────────────────────────────────┴───────────────┤
│ 📈 Bandit Selection Stats:                              │
│ • Exploitation: 90% → best models                       │
│ • Exploration: 10% → testing new models                 │
│ • Current best: CodeAgent-1.2 (94% success, 45ms avg)  │
└─────────────────────────────────────────────────────────┘
```

## 🛠️ Technical Implementation

### Required Dependencies (Updated)
```python
# Add to requirements.txt
matplotlib>=3.7.0      # For charts and graphs
tkinter                # GUI framework (built-in)
rumps>=0.4.0          # macOS tray integration
numpy>=1.24.0         # Data processing
pandas>=2.0.0         # Data analysis
plotly>=5.15.0        # Interactive charts
psutil>=5.9.0         # System monitoring

# NEW: Micro-training dependencies
transformers>=4.35.0   # Hugging Face transformers
peft>=0.6.0           # Parameter-efficient fine-tuning
bitsandbytes>=0.41.0  # 4-bit quantization
torch>=2.1.0          # PyTorch for training

# NEW: Advanced clustering
hdbscan>=0.8.29       # Hierarchical density clustering
scikit-learn>=1.3.0   # Spectral, GMM clustering
networkx>=3.2         # Graph-based clustering
umap-learn>=0.5.4     # Dimension reduction + clustering
```

### Enhanced Database Schema
```sql
-- Add pattern tracking table
CREATE TABLE IF NOT EXISTS patterns (
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    pattern_type TEXT NOT NULL,
    confidence REAL NOT NULL,
    event_count INTEGER NOT NULL,
    first_seen TIMESTAMP NOT NULL,
    last_seen TIMESTAMP NOT NULL,
    clustering_method TEXT NOT NULL,  -- NEW
    metadata JSON
);

-- NEW: Micro-agent tracking
CREATE TABLE IF NOT EXISTS micro_agents (
    id INTEGER PRIMARY KEY,
    model_id TEXT UNIQUE NOT NULL,
    specialization TEXT NOT NULL,
    training_data_hash TEXT NOT NULL,
    model_path TEXT NOT NULL,
    created_at TIMESTAMP NOT NULL,
    performance_score REAL DEFAULT 0.0,
    success_rate REAL DEFAULT 0.0,
    avg_latency_ms REAL DEFAULT 0.0,
    total_queries INTEGER DEFAULT 0,
    is_active BOOLEAN DEFAULT 1
);

-- NEW: Training sessions
CREATE TABLE IF NOT EXISTS training_sessions (
    id INTEGER PRIMARY KEY,
    model_id TEXT NOT NULL,
    status TEXT NOT NULL,  -- 'queued', 'training', 'completed', 'failed'
    started_at TIMESTAMP,
    completed_at TIMESTAMP,
    training_data_size INTEGER,
    final_loss REAL,
    metadata JSON
);

-- Add user interactions table
CREATE TABLE IF NOT EXISTS user_interactions (
    id INTEGER PRIMARY KEY,
    interaction_type TEXT NOT NULL,
    timestamp TIMESTAMP NOT NULL,
    model_id TEXT,  -- NEW: track which model was used
    success BOOLEAN,  -- NEW: track interaction success
    latency_ms INTEGER,  -- NEW: track response time
    data JSON
);
```

## 🎯 Success Metrics (Enhanced)

### Technical Metrics
- **Response Time**: Dashboard loads in <2 seconds
- **Memory Usage**: <100MB additional memory overhead
- **Update Frequency**: Live metrics update every 30 seconds
- **Pattern Detection**: New patterns detected within 5 minutes
- **🆕 Training Efficiency**: Models train in <10 minutes on consumer hardware
- **🆕 Model Performance**: >85% success rate on specialized tasks
- **🆕 Clustering Accuracy**: Multi-algorithm consensus >90%

### User Experience Metrics
- **Discoverability**: Users find insights within 30 seconds
- **Engagement**: Dashboard viewed daily by active users
- **Usefulness**: 80% of notifications lead to user action
- **Performance**: No noticeable system slowdown
- **🆕 Training Transparency**: Users understand what's being learned
- **🆕 Model Trust**: Users can see model performance and make informed choices

### Final Outcome
A **continuous learning pipeline** that:
- ✅ **Never stops collecting** user behavior data
- ✅ **Intelligently triggers** meta-learning phases when data is sufficient
- ✅ **Performs advanced clustering** and semantic analysis automatically
- ✅ **Spawns specialized micro-agents** based on discovered patterns
- ✅ **Provides transparent visualization** of the continuous learning process
- ✅ **Creates a self-evolving AI ecosystem** that grows with user behavior

---

*This creates the foundation for a truly autonomous AI system that continuously learns, adapts, and evolves based on real user behavior patterns.* 