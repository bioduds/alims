# ALims Refactor Plan - SelFlow → ALims

## Overview
Complete refactor from SelFlow to ALims for commercial launch with alims.com domain.

## Refactor Mapping
- `SelFlow` → `ALims` (title case)
- `selflow` → `alims` (lowercase)
- `selFlow` → `aLims` (camelCase)
- `SELFLOW` → `ALIMS` (uppercase)

## Files to Rename
### Root Level
- `launch_selflow.sh` → `launch_alims.sh`

### Backend Scripts
- `backend/scripts/launch_selflow.sh` → `backend/scripts/launch_alims.sh`
- `backend/scripts/run_selflow_live.py` → `backend/scripts/run_alims_live.py`
- `backend/scripts/run_visual_selflow.py` → `backend/scripts/run_visual_alims.py`
- `backend/scripts/selflow.py` → `backend/scripts/alims.py`
- `backend/scripts/selflow_tray.py` → `backend/scripts/alims_tray.py`

### Tools
- `tools/selflow_dashboard.py` → `tools/alims_dashboard.py`
- `tools/selflow_events.py` → `tools/alims_events.py`

### Environment
- `environments/selflow_env/` → `environments/alims_env/`

### Log Files
- `logs/selflow_*.log` → `logs/alims_*.log`
- `logs/selflow_*.pid` → `logs/alims_*.pid`

### Data Files
- `data/selflow_events.db` → `data/alims_events.db`

### TypeScript Types
- `frontend/desktop/src/types/selflow.ts` → `frontend/desktop/src/types/alims.ts`

## Content Changes
### Package Configuration
- `pyproject.toml`: name, URLs, entry points
- `frontend/desktop/package.json`: name, description
- `frontend/desktop/src-tauri/tauri.conf.json`: productName, identifier

### Documentation
- All `.md` files in `docs/`
- `README.md`
- All guide files

### Code Files
- Class names: `SelFlowApp` → `ALimsApp`
- Variable names: `selflow_*` → `alims_*`
- String literals and comments
- Log messages and print statements
- Environment variable names

### Configuration
- YAML config files
- Environment variable references
- Database table names if any

## Execution Order
1. Stop running system
2. Rename files and directories
3. Update file contents
4. Update package configurations
5. Update documentation
6. Test system functionality
7. Update repository name on GitHub

## Critical Files Priority
1. Launch scripts (system entry points)
2. Package configuration files
3. Main application files
4. Documentation files
5. Configuration files

## Post-Refactor Tasks
1. Update GitHub repository name
2. Update domain references to alims.com
3. Update any hardcoded paths
4. Verify all imports still work
5. Test complete system functionality 