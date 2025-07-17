# Sample QC Review Agent

A TLA+-verified Laboratory Information Management System (LIMS) agent for automated sample quality control review.

## Overview

The Sample QC Review Agent is a critical component of the ALIMS workflow system that automates the quality control review process for laboratory samples. This agent has been implemented following a strict TLA+-first methodology to ensure correctness, safety, and reliability.

## Features

- **Automated QC Review**: Performs comprehensive quality control assessments based on configurable criteria
- **Multi-parameter Validation**: Evaluates pH levels, purity percentages, and contamination levels
- **Event-driven Architecture**: Publishes events for seamless integration with the LIMS workflow
- **Type Safety**: Full MyPy compliance with comprehensive type annotations
- **Error Handling**: Robust error handling following TLA+ model specifications
- **Extensible Design**: Plugin-based architecture for custom QC criteria

## Architecture

### Core Components

- **SampleQCReviewAgent**: Main agent class implementing TLA+ verified logic
- **BaseAgent**: Abstract base class providing common agent functionality
- **EventBus**: Event-driven communication system for LIMS integration
- **QCCriteria**: Configurable quality control validation rules

### Integration

- **Event System**: Publishes `SampleQCReviewCompleted` events
- **Database**: Stores sample data and QC results
- **API Gateway**: RESTful endpoints for external integration
- **Workflow Manager**: Seamless integration with LIMS workflows

## Quality Assurance

This implementation has been rigorously validated:

- **TLA+ Verification**: Formal model checked with TLC model checker
- **Code Coverage**: 96% test coverage (exceeds 90% requirement)
- **Static Analysis**: 0 issues (flake8, MyPy compliant)
- **Test Suite**: 108 tests with 100% pass rate
  - TLA+ compliance tests (52 tests)
  - Unit tests (40+ tests)
  - Integration tests (16+ tests)

## Quick Start

### Prerequisites

- Python 3.9+
- Virtual environment (recommended)
- PostgreSQL (for data persistence)
- Redis (for event bus)

### Installation

```bash
# Activate virtual environment
source alims_env/bin/activate

# Install dependencies
pip install -r backend/requirements/base.txt

# Run tests
pytest tests/test_sample_qc_review_agent_*.py
```

### Usage

```python
from backend.app.core.agents.sample_qc_review_agent import SampleQCReviewAgent
from backend.app.core.events import EventBus

# Initialize agent
event_bus = EventBus()
agent = SampleQCReviewAgent(event_bus=event_bus)

# Process sample QC review
sample_data = {
    "sample_id": "SAMPLE-001",
    "ph_level": 7.2,
    "purity_percentage": 95.5,
    "contamination_level": 0.02
}

result = await agent.review_sample_qc(sample_data)
print(f"QC Result: {result.status}")
```

### Configuration

The agent supports configurable QC criteria:

```python
qc_criteria = {
    "ph_min": 6.5,
    "ph_max": 8.0,
    "purity_min": 90.0,
    "contamination_max": 0.05
}

agent = SampleQCReviewAgent(
    event_bus=event_bus,
    qc_criteria=qc_criteria
)
```

## Development

### Docker Environment

For full system integration testing:

```bash
# Start complete ALIMS environment
./start-dev.sh

# Access services:
# - API Gateway: http://localhost:8000
# - Workflow Manager: http://localhost:8002
# - Main Interface: http://localhost:8003
```

### Local Development

For rapid agent development and testing:

```bash
# Start simplified backend
./launch_backend.sh

# Run agent-specific tests
source alims_env/bin/activate
cd backend
python -m pytest tests/test_sample_qc_review_agent_*.py -v
```

### TLA+ Verification

To validate the TLA+ model:

```bash
cd plans/feature-20250711-sample-qc-review/tla
tlc SampleQCReviewAgent.tla
```

## API Reference

### Main Methods

- `review_sample_qc(sample_data: Dict[str, Any]) -> QCReviewResult`
- `validate_qc_criteria(criteria: Dict[str, float]) -> bool`
- `get_agent_status() -> AgentStatus`

### Events

- `SampleQCReviewStarted`: Published when QC review begins
- `SampleQCReviewCompleted`: Published when QC review completes
- `SampleQCReviewFailed`: Published when QC review fails

### Error Handling

The agent follows TLA+ model error states:

- `InvalidSampleDataError`: Invalid or missing sample data
- `QCCriteriaError`: Invalid QC criteria configuration
- `ProcessingError`: Internal processing errors
- `ValidationError`: Data validation failures

## Testing

### Running Tests

```bash
# All tests
pytest tests/test_sample_qc_review_agent_*.py

# TLA+ compliance tests
pytest tests/test_sample_qc_review_agent_tla_compliance.py

# Unit tests
pytest tests/test_sample_qc_review_agent_unit.py

# Integration tests
pytest tests/test_sample_qc_review_agent_integration.py

# Coverage report
pytest --cov=backend.app.core.agents.sample_qc_review_agent tests/
```

### Test Categories

1. **TLA+ Compliance**: Validates implementation matches formal specification
2. **Unit Tests**: Tests individual methods and error handling
3. **Integration Tests**: Tests end-to-end workflows and system integration
4. **Coverage Tests**: Ensures comprehensive code coverage

## Contributing

1. Follow TLA+-first methodology for all changes
2. Ensure 100% test pass rate
3. Maintain >90% code coverage
4. Use flake8 and MyPy for code quality
5. Update TLA+ model before implementation changes

## License

This project is part of the ALIMS Laboratory Information Management System.

## Documentation

- [TLA+ Specification](./tla/SampleQCReviewAgent.tla)
- [Natural Language Summary](./tla-natural-language-summary.md)
- [Validation Results](./tla-validation-results.md)
- [Final Validation](./VALIDATION_SUMMARY.md)

## Support

For issues or questions:

1. Check the test suite for usage examples
2. Review the TLA+ specification for behavior details
3. Refer to the validation summary for implementation details
