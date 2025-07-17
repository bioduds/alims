# ALIMS Project Structure

## 📁 Project Organization (Updated July 2025)

The ALIMS project has been reorganized into clear, functional directories for optimal development workflow and maintainability.

```text
alims/
├── README.md                    # 📖 Main project documentation
├── pyproject.toml              # 🔧 Project configuration and dependencies
├── docker-compose.yml          # 🐳 Docker orchestration
├── .env / .env.example         # ⚙️ Environment configuration
├── .gitignore                  # 🚫 Git ignore patterns
│
├── backend/                    # 🔙 Backend services and core logic
│   ├── app/                    # 🏗️ Main application code
│   │   ├── agents/             # 🤖 LIMS-specific agents
│   │   ├── intelligence/       # 🧠 AI agents and TLA+ verified implementations
│   │   ├── tensor_calendar/    # 🧮 Memory and tensor management
│   │   └── ...                 # Other application modules
│   ├── simple_api_server.py    # 🎯 Main FastAPI server
│   ├── requirements.txt        # 📦 Python dependencies
│   └── Dockerfile.*           # 🐳 Docker build configurations
│
├── frontend/                   # 🎨 Frontend applications
│   └── ...                     # React/Vue/etc. application
│
├── config/                     # ⚙️ Configuration files
│   ├── ai_config.yaml          # 🤖 AI model configuration
│   ├── api_config.yaml         # 🔗 API configuration
│   └── default.yaml            # 🔧 Default system configuration
│
├── data/                       # 💾 Data storage and databases
├── database/                   # 🗃️ Database schemas and migrations
├── docker/                     # 🐳 Docker-related configurations
│
├── docs/                       # 📚 Documentation
│   ├── roadmaps/              # 📋 Project roadmaps and planning
│   ├── implementation-status/ # ✅ Implementation completion status
│   ├── architecture/          # 🏗️ System architecture documentation
│   └── guides/                # 📖 User and developer guides
│
├── demos/                      # 🎪 Demo applications and examples
│   ├── tla-verified/          # ✅ TLA+ verified implementations
│   └── ...                    # Other demo categories
│
├── scripts/                    # 🔧 Utility scripts
│   ├── launch/                # 🚀 Launch and startup scripts
│   │   ├── start-dev.sh       # 🔧 Development environment startup
│   │   ├── launch_backend.sh  # 🔙 Backend service launcher
│   │   ├── launch_main_interface.sh # 🎯 Main interface launcher
│   │   └── alims.sh           # 🚀 Main system launcher
│   └── ...                    # Other script categories
│
├── tests/                      # 🧪 Test suites and debugging scripts
├── runtime/                    # 🏃 Runtime files (PIDs, temp files)
├── logs/                       # 📝 Application logs
├── monitoring/                 # 📊 Monitoring and observability
├── nginx/                      # 🌐 Nginx configuration
├── papers/                     # 📄 Research papers and references
├── plans/                      # 📋 Project plans and specifications
├── requirements/               # 📦 Requirements specifications
├── searxng/                    # 🔍 Search engine configuration
├── tools/                      # 🛠️ Development tools
└── temp/                       # 🗂️ Temporary files
```

## 🎯 Directory Purpose

### Core Application

- **`backend/app/`** - Main application logic, organized by functional domains
- **`frontend/`** - Modern React-based frontend interface
- **`config/`** - Centralized configuration management

### Development & Documentation

- **`docs/`** - Comprehensive documentation organized by type
- **`plans/`** - Strategic planning and architecture documents
- **`demos/`** - Example scripts and demonstrations
- **`tools/`** - Development utilities and analysis tools

### Operations

- **`scripts/`** - Shell scripts for deployment and management
- **`logs/`** - Runtime logs from all components
- **`runtime/`** - Runtime files, process IDs, temporary data
- **`docker/`** - Container orchestration files

### Data & Environment

- **`data/`** - Application data and databases
- **`alims_env/`** - Python virtual environment (local development)

## 🧹 File Organization Principles

1. **Functional Separation** - Files grouped by purpose and domain
2. **Clean Root** - Minimal files in project root (README, config, docker-compose)
3. **Documentation Centralization** - All `.md` files in `docs/` with proper categorization
4. **Runtime Isolation** - All temporary/runtime files in `runtime/` and `temp/`
5. **Script Consolidation** - All shell scripts in `scripts/` with categorization
6. **Tool Centralization** - All development tools in `tools/`

## 🔄 Development Workflow

### 1. Backend Development
- **Location**: `backend/` directory
- **Main Server**: `simple_api_server.py` - FastAPI application
- **Key Modules**:
  - `app/intelligence/` - AI agents and TLA+ verified implementations
  - `app/tensor_calendar/` - Memory and tensor management
  - `app/agents/` - LIMS-specific agents

### 2. Frontend Development
- **Location**: `frontend/` directory
- **Framework**: React/Vue/etc.
- **API Integration**: RESTful API consumption

### 3. Configuration Management
- **Location**: `config/` directory
- **Key Files**:
  - `ai_config.yaml` - AI model configuration
  - `api_config.yaml` - API configuration
  - `default.yaml` - Default system configuration

### 4. Documentation
- **Location**: `docs/` directory
- **Structure**:
  - `roadmaps/` - Project roadmaps and planning
  - `implementation-status/` - Implementation completion status
  - `architecture/` - System architecture documentation
  - `guides/` - User and developer guides

### 5. Testing
- **Location**: `tests/` directory
- **Includes**: Unit tests, integration tests, debug utilities

### 6. Scripts and Automation
- **Location**: `scripts/` directory
- **Launch Scripts**: `scripts/launch/` for system startup
- **Development**: Use `start-dev.sh` for development environment

## 🐳 Docker Services

The system uses Docker Compose with the following services:

- **main-interface** - Main FastAPI application
- **postgres** - PostgreSQL database
- **redis** - Redis cache
- **vector-db** - Qdrant vector database
- **ollama** - AI model service
- **elasticsearch** - Search engine
- **nginx** - Reverse proxy

## 🚀 Quick Start

1. **Development Environment**:
   ```bash
   ./scripts/launch/start-dev.sh
   ```

2. **Production Deployment**:
   ```bash
   docker-compose up -d
   ```

3. **Backend Testing**:
   ```bash
   cd backend && python -m pytest ../tests/
   ```

4. **Frontend Development**:
   ```bash
   cd frontend && npm start
   ```

## 📋 File Organization Guidelines

### ✅ Root Level (Keep Clean)
- Only essential project files (README, configs, docker-compose)
- No development files, logs, or temporary files
- Use `.gitignore` to exclude unnecessary files

### 📚 Documentation
- All `.md` files in `docs/` with proper categorization
- Use subdirectories for different types of documentation
- Keep implementation status separate from roadmaps

### 🔧 Scripts
- All executable scripts in `scripts/` with categorization
- Use `scripts/launch/` for system startup scripts
- Maintain executable permissions

### 🧪 Tests
- All test files in `tests/` directory
- Include debug and testing utilities
- Organize by test type (unit, integration, performance)

### 🏃 Runtime Files
- All temporary/runtime files in `runtime/`
- PID files, temporary data, process management
- Exclude from version control

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

## 📊 Project Reorganization Summary (July 2025)

This organization was implemented to:

- ✅ Clean up root directory clutter
- ✅ Improve development workflow
- ✅ Better organize documentation
- ✅ Standardize script locations
- ✅ Separate runtime from source files

### Files Moved

- **Documentation**: All `.md` files moved to `docs/` subdirectories
  - Roadmaps → `docs/roadmaps/`
  - Implementation status → `docs/implementation-status/`
- **Scripts**: All launch scripts moved to `scripts/launch/`
- **Tests**: All test files moved to `tests/`
- **Runtime**: All `.pid` files moved to `runtime/`
- **Demos**: TLA+ demos moved to `demos/tla-verified/`

### New Structure Benefits

- **Cleaner Root**: Only essential files in project root
- **Better Discovery**: Logical grouping makes files easier to find
- **Improved Maintenance**: Clear separation of concerns
- **Better Git History**: Organized commits and changes

This structure provides a clean, maintainable, and scalable foundation for the ALIMS project.
