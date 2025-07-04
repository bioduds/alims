# ALIMS Project Structure

## 📁 Project Organization

The ALIMS project is organized into clear, functional directories for optimal development workflow and maintainability.

```text
alims/
├── README.md                    # 📖 Main project documentation
├── pyproject.toml              # 🔧 Project configuration and dependencies
├── alims.sh                    # 🚀 Main control script
├── .gitignore                  # 🚫 Git ignore patterns
│
├── backend/                    # 🔙 Backend services and core logic
│   ├── app/                    # 🏗️ Main application code
│   │   ├── ai/                 # 🤖 AI agents and tools
│   │   ├── analytics/          # 📊 Data analytics engines
│   │   ├── core/               # 🔬 LIMS core components
│   │   ├── intelligence/       # 🧠 Web search and analysis
│   │   ├── privacy/            # 🔒 Privacy and security
│   │   ├── system/             # ⚙️ System integration
│   │   ├── web/                # 🌐 Web interfaces
│   │   └── main.py             # 🎯 Application entry point
│   ├── requirements/           # 📦 Python dependencies
│   └── scripts/                # 🔧 Backend utility scripts
│
├── frontend/                   # 🎨 Frontend applications
│   └── desktop/                # 🖥️ Desktop interface (React)
│
├── config/                     # ⚙️ Configuration files
│   ├── ai_config.yaml          # 🤖 AI agent configuration
│   ├── default.yaml            # 🔧 Default settings
│   └── emergent_agents.yaml    # 🌟 Emergent agent patterns
│
├── data/                       # 💾 Data storage
│   ├── context/                # 📚 Context data
│   └── selflow_events.db       # 🗃️ Event database
│
├── docs/                       # 📚 Documentation
│   ├── README.md               # 📖 Documentation index
│   ├── architecture/           # 🏗️ System architecture docs
│   ├── guides/                 # 📖 User and developer guides
│   ├── implementation/         # 🔨 Implementation summaries
│   ├── planning/               # 📋 Planning documents
│   └── testing/                # 🧪 Testing documentation
│
├── plans/                      # 📋 Strategic planning
│   ├── README.md               # 📖 Planning index
│   ├── tla.md                  # 🎯 Top-level architecture
│   └── tla/                    # 📁 TLA+ specifications
│
├── demos/                      # 🎬 Demo and example scripts
│   ├── lims_transformation_demo.py
│   ├── enhanced_agent_demo.py
│   └── debug_chat.py
│
├── scripts/                    # 🔧 Shell scripts and utilities
│   ├── launch_alims.sh
│   ├── launch_desktop.sh
│   └── setup_searxng.sh
│
├── tools/                      # 🛠️ Development and analysis tools
│   ├── alims_dashboard.py      # 📊 System dashboard
│   ├── alims_events.py         # 📝 Event management
│   ├── test_clustering.py      # 🧪 Clustering tests
│   ├── analyze_event_data.py   # 📈 Event data analysis
│   ├── analyze_semantic_content.py # 🔍 Semantic analysis
│   ├── cluster_file_operations.py  # 📁 File clustering
│   └── demo_central_brain.py   # 🧠 Central brain demo
│
├── logs/                       # 📝 Application logs
├── temp/                       # 🗂️ Temporary files
│   ├── *.pid                   # 🔢 Process IDs
│   ├── *.log                   # 📝 Log files
│   └── *.png                   # 🖼️ Generated plots
│
├── docker/                     # 🐳 Docker configurations
│   └── docker-compose.searxng.yml
│
├── searxng/                    # 🔍 Search engine integration
│   ├── docker-compose.yaml
│   └── searxng/
│
└── alims_env/                  # 🐍 Python virtual environment
```

## 🎯 Directory Purpose

### Core Application

- **`backend/app/`** - Main application logic, organized by functional domains
- **`frontend/desktop/`** - Modern React-based desktop interface
- **`config/`** - Centralized configuration management

### Development & Documentation

- **`docs/`** - Comprehensive documentation organized by type
- **`plans/`** - Strategic planning and architecture documents (keep `tla.md` here)
- **`demos/`** - Example scripts and demonstrations
- **`tools/`** - Development utilities and analysis tools

### Operations

- **`scripts/`** - Shell scripts for deployment and management
- **`logs/`** - Runtime logs from all components
- **`temp/`** - Temporary files, process IDs, generated content
- **`docker/`** - Container orchestration files

### Data & Environment

- **`data/`** - Application data and databases
- **`alims_env/`** - Python virtual environment (local development)

## 🧹 File Organization Principles

1. **Functional Separation** - Files grouped by purpose and domain
2. **Clean Root** - Minimal files in project root (README, config, main script)
3. **Documentation Centralization** - All `.md` files in `docs/` (except `plans/tla.md`)
4. **Temporary Isolation** - All temporary files in `temp/`
5. **Script Consolidation** - All shell scripts in `scripts/`
6. **Tool Centralization** - All development tools in `tools/`

## 🔄 Maintenance

### Adding New Components

- **Backend modules** → `backend/app/{domain}/`
- **Documentation** → `docs/{category}/`
- **Tools/utilities** → `tools/`
- **Configuration** → `config/`

### File Naming Conventions

- **Python files** - `snake_case.py`
- **Documentation** - `UPPERCASE_WITH_UNDERSCORES.md`
- **Scripts** - `kebab-case.sh`
- **Configuration** - `lowercase.yaml`

This structure provides a clean, maintainable, and scalable foundation for the ALIMS project.
