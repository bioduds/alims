#!/usr/bin/env python3
"""
Semantic Content Analysis of ALims Events
Analyzes the actual meaning and context of events to understand
what agents should semantically understand and act upon.
"""

import sqlite3
import json
import re
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path


def analyze_semantic_content(db_path="data/events.db", limit=1000):
    """Analyze the semantic content of events"""

    print("🧠 Analyzing Semantic Content of Events...")
    print("=" * 60)

    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()

    # Get diverse sample of events
    cursor.execute(
        """
        SELECT event_type, data_json, timestamp FROM events 
        WHERE data_json IS NOT NULL 
        ORDER BY timestamp DESC 
        LIMIT ?
    """,
        (limit,),
    )

    events = []
    for row in cursor.fetchall():
        try:
            data = json.loads(row[1])
            events.append({"type": row[0], "data": data, "timestamp": row[2]})
        except:
            continue

    conn.close()

    print(f"📊 Analyzing {len(events)} events for semantic patterns...")

    # Analyze by event type
    file_events = [e for e in events if e["type"] == "file_op"]
    app_events = [e for e in events if e["type"] == "app"]

    print(f"\n📁 File Operations: {len(file_events)} events")
    print(f"📱 App Events: {len(app_events)} events")

    return analyze_file_semantics(file_events), analyze_app_semantics(app_events)


def analyze_file_semantics(file_events):
    """Analyze semantic meaning of file operations"""

    print("\n🔍 File Operation Semantic Analysis:")
    print("=" * 50)

    # Categorize by semantic meaning
    semantic_categories = {
        "development_workflow": [],
        "content_creation": [],
        "system_maintenance": [],
        "user_data_management": [],
        "application_state": [],
        "cache_optimization": [],
        "backup_sync": [],
        "configuration_changes": [],
    }

    project_patterns = defaultdict(list)
    workflow_patterns = defaultdict(list)

    for event in file_events:
        data = event["data"]
        path = data.get("path", "")
        action = data.get("action", "")
        name = data.get("name", "")

        # Semantic categorization based on path and context
        path_lower = path.lower()

        # Development workflow detection
        if any(
            keyword in path_lower
            for keyword in ["alims", "projects", ".py", ".js", ".ts", ".git"]
        ):
            semantic_categories["development_workflow"].append(event)

            # Extract project context
            if "projects" in path_lower:
                project_match = re.search(r"/projects/([^/]+)", path_lower)
                if project_match:
                    project_name = project_match.group(1)
                    project_patterns[project_name].append(
                        {
                            "action": action,
                            "file": name,
                            "timestamp": event["timestamp"],
                        }
                    )

        # Content creation
        elif any(
            ext in path_lower for ext in [".md", ".txt", ".doc", ".pdf", ".png", ".jpg"]
        ):
            semantic_categories["content_creation"].append(event)

        # System maintenance
        elif any(
            keyword in path_lower for keyword in ["cache", "temp", "log", "trash"]
        ):
            semantic_categories["system_maintenance"].append(event)

        # Application state
        elif any(
            keyword in path_lower
            for keyword in ["cursor", "vscode", "chrome", "preferences"]
        ):
            semantic_categories["application_state"].append(event)

            # Detect workflow patterns
            if "cursor" in path_lower or "vscode" in path_lower:
                workflow_patterns["coding_session"].append(
                    {"action": action, "file": name, "timestamp": event["timestamp"]}
                )

        # Cache optimization
        elif "cache" in path_lower:
            semantic_categories["cache_optimization"].append(event)

        # Configuration changes
        elif any(
            ext in path_lower for ext in [".plist", ".json", ".config", ".settings"]
        ):
            semantic_categories["configuration_changes"].append(event)

        else:
            semantic_categories["user_data_management"].append(event)

    # Report semantic findings
    print("\n📊 Semantic Categories:")
    total_events = len(file_events)

    for category, events in semantic_categories.items():
        if events:
            count = len(events)
            percentage = (count / total_events) * 100
            print(f"  {category}: {count} events ({percentage:.1f}%)")

            # Show sample semantic context
            if events:
                sample = events[0]["data"]
                sample_path = (
                    sample.get("path", "")[:80] + "..."
                    if len(sample.get("path", "")) > 80
                    else sample.get("path", "")
                )
                print(f"    Sample: {sample.get('action', '')} → {sample_path}")

    # Analyze project workflows
    print(f"\n🚀 Development Project Patterns:")
    for project, activities in project_patterns.items():
        if len(activities) > 5:  # Only show active projects
            print(f"  {project}: {len(activities)} activities")

            # Analyze activity patterns
            actions = Counter(a["action"] for a in activities)
            files = Counter(a["file"] for a in activities if a["file"])

            print(f"    Actions: {dict(actions.most_common(3))}")
            print(f"    Files: {list(files.keys())[:3]}")

    # Analyze workflow patterns
    print(f"\n⚡ Workflow Patterns:")
    for workflow, activities in workflow_patterns.items():
        if len(activities) > 10:
            print(f"  {workflow}: {len(activities)} activities")

            # Time-based analysis
            timestamps = [a["timestamp"] for a in activities]
            if len(timestamps) > 1:
                time_span = max(timestamps) - min(timestamps)
                print(f"    Duration: {time_span:.0f} seconds")
                print(
                    f"    Intensity: {len(activities)/max(time_span/60, 1):.1f} actions/minute"
                )

    return semantic_categories, project_patterns, workflow_patterns


def analyze_app_semantics(app_events):
    """Analyze semantic meaning of app events"""

    print(f"\n📱 Application Semantic Analysis:")
    print("=" * 50)

    if not app_events:
        print("  No app events to analyze")
        return {}, {}, {}

    # Categorize apps by purpose
    app_categories = {
        "development_tools": [],
        "productivity_apps": [],
        "communication": [],
        "entertainment": [],
        "system_utilities": [],
        "creative_tools": [],
    }

    usage_patterns = defaultdict(list)

    for event in app_events:
        data = event["data"]
        app_name = data.get("app", "").lower()
        action = data.get("action", "")

        # Categorize by app purpose
        if any(
            keyword in app_name for keyword in ["cursor", "vscode", "terminal", "git"]
        ):
            app_categories["development_tools"].append(event)
        elif any(keyword in app_name for keyword in ["finder", "notes", "calendar"]):
            app_categories["productivity_apps"].append(event)
        elif any(keyword in app_name for keyword in ["chrome", "safari", "mail"]):
            app_categories["communication"].append(event)
        elif any(keyword in app_name for keyword in ["music", "video", "game"]):
            app_categories["entertainment"].append(event)
        else:
            app_categories["system_utilities"].append(event)

        # Track usage patterns
        usage_patterns[app_name].append(
            {"action": action, "timestamp": event["timestamp"]}
        )

    # Report app semantic findings
    print("\n📊 App Categories:")
    total_events = len(app_events)

    for category, events in app_categories.items():
        if events:
            count = len(events)
            percentage = (count / total_events) * 100
            print(f"  {category}: {count} events ({percentage:.1f}%)")

            # Show apps in this category
            apps = Counter(e["data"].get("app", "") for e in events)
            print(f"    Apps: {list(apps.keys())[:3]}")

    # Analyze usage patterns
    print(f"\n🎯 App Usage Patterns:")
    for app, activities in usage_patterns.items():
        if len(activities) > 2:
            actions = Counter(a["action"] for a in activities)
            print(f"  {app}: {dict(actions)}")

    return app_categories, usage_patterns


def suggest_semantic_agents(file_semantics, app_semantics):
    """Suggest agents based on semantic analysis"""

    print(f"\n🤖 Semantic Agent Suggestions:")
    print("=" * 60)

    semantic_categories, project_patterns, workflow_patterns = file_semantics
    if len(app_semantics) == 2:
        app_categories, usage_patterns = app_semantics
    else:
        app_categories, usage_patterns = {}, {}

    suggested_agents = []

    # Development workflow agent
    dev_events = len(semantic_categories.get("development_workflow", []))
    if dev_events > 50:
        suggested_agents.append(
            {
                "name": "DevelopmentWorkflowAgent",
                "purpose": "Understand coding sessions, project context, file relationships",
                "training_data": dev_events,
                "semantic_understanding": [
                    "Project structure analysis",
                    "Code file relationships",
                    "Development session patterns",
                    "Git workflow understanding",
                    "Build/test cycle recognition",
                ],
                "input_spec": {
                    "file_path": "str",
                    "action": "str",
                    "project_context": "dict",
                    "recent_files": "list",
                },
                "output_spec": {
                    "workflow_stage": "str",  # 'coding', 'testing', 'debugging'
                    "project_intent": "str",  # 'feature_dev', 'bug_fix', 'refactor'
                    "next_likely_actions": "list",
                    "context_summary": "str",
                },
            }
        )

    # Application state agent
    app_state_events = len(semantic_categories.get("application_state", []))
    if app_state_events > 50:
        suggested_agents.append(
            {
                "name": "ApplicationStateAgent",
                "purpose": "Understand app usage patterns, preferences, workflow optimization",
                "training_data": app_state_events,
                "semantic_understanding": [
                    "App usage patterns",
                    "Preference changes context",
                    "Workflow optimization opportunities",
                    "State synchronization needs",
                    "Performance impact analysis",
                ],
                "input_spec": {
                    "app_name": "str",
                    "state_change": "dict",
                    "usage_context": "dict",
                },
                "output_spec": {
                    "usage_pattern": "str",
                    "optimization_suggestions": "list",
                    "workflow_impact": "float",
                    "state_importance": "str",
                },
            }
        )

    # System maintenance agent
    maintenance_events = len(semantic_categories.get("system_maintenance", []))
    if maintenance_events > 20:
        suggested_agents.append(
            {
                "name": "SystemMaintenanceAgent",
                "purpose": "Understand cleanup needs, performance optimization, resource management",
                "training_data": maintenance_events,
                "semantic_understanding": [
                    "Cache cleanup patterns",
                    "Temporary file lifecycle",
                    "Storage optimization needs",
                    "Performance impact assessment",
                    "Automated maintenance scheduling",
                ],
                "input_spec": {
                    "file_path": "str",
                    "file_size": "int",
                    "age": "int",
                    "access_pattern": "dict",
                },
                "output_spec": {
                    "cleanup_priority": "float",
                    "performance_impact": "str",
                    "maintenance_action": "str",
                    "schedule_recommendation": "str",
                },
            }
        )

    # Report suggested agents
    for agent in suggested_agents:
        print(f"\n🤖 {agent['name']}:")
        print(f"   Purpose: {agent['purpose']}")
        print(f"   Training Data: {agent['training_data']} events")
        print(f"   Semantic Understanding:")
        for understanding in agent["semantic_understanding"]:
            print(f"     • {understanding}")
        print(f"   Input: {agent['input_spec']}")
        print(f"   Output: {agent['output_spec']}")

    return suggested_agents


def main():
    """Main semantic analysis"""

    try:
        # Analyze semantic content
        file_semantics, app_semantics = analyze_semantic_content(limit=2000)

        # Suggest semantic agents
        agents = suggest_semantic_agents(file_semantics, app_semantics)

        print(f"\n✅ Semantic Analysis Complete!")
        print(f"🧠 Identified {len(agents)} semantically meaningful agents")

        print(f"\n🎯 Key Insight:")
        print("Agents should understand MEANING and CONTEXT, not just file operations!")
        print(
            "They need to recognize workflows, intentions, and semantic relationships."
        )

    except Exception as e:
        print(f"❌ Error during semantic analysis: {e}")
        import traceback

        traceback.print_exc()


if __name__ == "__main__":
    main()
