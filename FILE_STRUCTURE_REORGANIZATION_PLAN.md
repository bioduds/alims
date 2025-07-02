# ALims File Structure Reorganization Plan

## Current Issues
- **Root Directory Clutter**: 30+ files including tests, scripts, logs, and analysis tools
- **Mixed Concerns**: Test files scattered between root and `/tests/`
- **Log Pollution**: Large log files (1.5MB+) in root directory
- **Multi-Project Confusion**: Python backend + Tauri frontend + Node.js mixing concerns
- **Duplicate Dependencies**: Multiple requirement files for different purposes
- **Scattered Tools**: Analysis scripts split between root and `/tools/`

## Proposed Structure

```
alims/
├── README.md                          # Main project readme
├── .gitignore                         # Git ignore rules
├── pyproject.toml                     # Python project configuration (NEW)
├── setup.py                          # Python package setup (NEW)
│
├── backend/                          # Python backend (RENAMED from root files)
│   ├── app/                         # Main application code (MOVED)
│   │   ├── ai/                      # AI components
│   │   ├── analytics/               # Analytics and clustering
│   │   ├── core/                    # Core business logic
│   │   ├── intelligence/            # Intelligence systems
│   │   ├── privacy/                 # Privacy components
│   │   ├── system/                  # System integration
│   │   ├── web/                     # Web dashboard
│   │   └── main.py                  # Main entry point
│   │
│   ├── scripts/                     # Python scripts (NEW)
│   │   ├── launch_alims.sh        # MOVED from root
│   │   ├── launch_tray.py           # MOVED from root
│   │   ├── run_alims_live.py      # MOVED from root
│   │   ├── run_visual_alims.py    # MOVED from root
│   │   └── alims.py               # MOVED from root
│   │
│   ├── analysis/                    # Data analysis tools (NEW)
│   │   ├── analyze_event_data.py    # MOVED from root
│   │   ├── analyze_semantic_content.py  # MOVED from root
│   │   ├── cluster_file_operations.py   # MOVED from root
│   │   └── demo_central_brain.py    # MOVED from root
│   │
│   ├── requirements/                # Dependency management (NEW)
│   │   ├── base.txt                 # Base requirements
│   │   ├── clustering.txt           # Clustering requirements
│   │   ├── visual.txt               # Visual requirements
│   │   ├── pydantic.txt             # Pydantic requirements
│   │   └── dev.txt                  # Development requirements
│   │
│   └── tests/                       # All Python tests (CONSOLIDATED)
│       ├── unit/                    # Unit tests
│       ├── integration/             # Integration tests
│       ├── system/                  # System tests
│       └── fixtures/                # Test fixtures
│
├── frontend/                        # Frontend applications (NEW)
│   ├── web/                         # Web dashboard (if separate)
│   └── desktop/                     # Tauri desktop app
│       ├── src/                     # React/TS source (MOVED)
│       ├── src-tauri/               # Tauri backend (MOVED)
│       ├── package.json             # MOVED from root
│       ├── package-lock.json        # MOVED from root
│       ├── tsconfig.json            # MOVED from root
│       ├── vite.config.ts           # MOVED from root
│       └── tailwind.config.js       # MOVED from root
│
├── config/                          # Configuration files (KEPT)
│   ├── ai_config.yaml
│   ├── default.yaml
│   └── emergent_agents.yaml
│
├── data/                            # Data storage (KEPT)
│   ├── context/
│   ├── patterns/
│   ├── training/
│   └── alims_events.db
│
├── docs/                            # Documentation (KEPT - already organized)
│   ├── architecture/
│   ├── guides/
│   ├── implementation/
│   ├── planning/
│   ├── testing/
│   └── README.md
│
├── logs/                            # Log files (CLEANED)
│   ├── .gitignore                   # Ignore all logs except structure
│   └── README.md                    # Log documentation
│
├── models/                          # ML models (KEPT)
│   └── embryos/
│
├── tools/                           # Utilities and tools (ENHANCED)
│   ├── dashboard/                   # Dashboard tools
│   ├── analysis/                    # Analysis utilities
│   ├── testing/                     # Testing utilities
│   └── development/                 # Development helpers
│
└── environments/                    # Environment management (NEW)
    ├── alims_env/                 # MOVED from root
    ├── docker/                      # Docker configurations
    └── scripts/                     # Environment setup scripts
```

## Migration Steps

### Phase 1: Backend Reorganization
1. Create `backend/` directory structure
2. Move Python application code from `app/` to `backend/app/`
3. Move standalone Python scripts to `backend/scripts/`
4. Move analysis tools to `backend/analysis/`
5. Consolidate requirements files in `backend/requirements/`
6. Move all test files to `backend/tests/` with proper categorization

### Phase 2: Frontend Separation
1. Create `frontend/` directory structure
2. Move Tauri desktop app to `frontend/desktop/`
3. Move Node.js configuration files
4. Update frontend build processes

### Phase 3: Log and Environment Cleanup
1. Move large log files to `logs/` directory
2. Add proper `.gitignore` for logs
3. Move virtual environment to `environments/`
4. Clean up root directory

### Phase 4: Configuration and Documentation
1. Create `pyproject.toml` for modern Python packaging
2. Update import paths throughout codebase
3. Update documentation references
4. Update CI/CD configurations

## Benefits of This Structure

1. **Clear Separation**: Backend Python code separated from frontend
2. **Reduced Clutter**: Root directory contains only essential project files
3. **Better Organization**: Related files grouped by function
4. **Easier Navigation**: Logical directory structure for different roles
5. **Maintainability**: Easier to find and modify specific components
6. **Scalability**: Structure supports project growth
7. **Standard Compliance**: Follows Python packaging best practices

## Files to Move

### From Root to `backend/scripts/`:
- `launch_alims.sh`
- `launch_tray.py`
- `run_alims_live.py`
- `run_visual_alims.py`
- `alims.py`
- `alims_tray.py`

### From Root to `backend/analysis/`:
- `analyze_event_data.py`
- `analyze_semantic_content.py`
- `cluster_file_operations.py`
- `demo_central_brain.py`

### From Root to `backend/tests/`:
- All `test_*.py` files (17 files)
- `setup_test.py`

### From Root to `frontend/desktop/`:
- `src/`
- `alims-desktop/src-tauri/`
- `package.json`
- `package-lock.json`
- `tsconfig.json`
- `vite.config.ts`
- `tailwind.config.js`
- `postcss.config.js`
- `index.html`

### From Root to `logs/`:
- `*.log` files
- Create `.gitignore` to exclude logs from git

### From Root to `environments/`:
- `alims_env/`

## Implementation Priority

1. **High Priority**: Backend reorganization (most critical for development)
2. **Medium Priority**: Test consolidation (improves development workflow)
3. **Medium Priority**: Frontend separation (cleaner architecture)
4. **Low Priority**: Log cleanup (reduces clutter but not critical)
5. **Low Priority**: Environment organization (nice to have) 