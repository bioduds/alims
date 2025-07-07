#!/usr/bin/env python3
"""
Cluster File Operations Data for Agent Training
Analyzes the 130K+ file operation events to identify natural clusters
that will inform the FileOperationAgent training.
"""

import sqlite3
import json
import numpy as np
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path
import re


def load_file_operations(db_path="data/events.db", limit=10000):
    """Load file operation events from database"""

    print(f"📁 Loading file operations from {db_path}...")

    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()

    # Get file operations with data
    cursor.execute(
        """
        SELECT data_json FROM events 
        WHERE event_type = 'file_op' 
        AND data_json IS NOT NULL 
        ORDER BY timestamp DESC 
        LIMIT ?
    """,
        (limit,),
    )

    events = []
    for row in cursor.fetchall():
        try:
            data = json.loads(row[0])
            events.append(data)
        except:
            continue

    conn.close()
    print(f"✅ Loaded {len(events)} file operation events")
    return events


def analyze_file_patterns(events):
    """Analyze patterns in file operations"""

    print("\n🔍 Analyzing File Operation Patterns...")
    print("=" * 50)

    # Action distribution
    actions = [event.get("action", "unknown") for event in events]
    action_counts = Counter(actions)

    print("📊 File Actions:")
    for action, count in action_counts.most_common():
        percentage = (count / len(events)) * 100
        print(f"  {action}: {count:,} ({percentage:.1f}%)")

    # File extension analysis
    extensions = []
    for event in events:
        ext = event.get("ext", "")
        if ext:
            extensions.append(ext.lower())

    ext_counts = Counter(extensions)
    print("\n📄 File Extensions:")
    for ext, count in ext_counts.most_common(15):
        percentage = (count / len(extensions)) * 100 if extensions else 0
        print(f"  .{ext}: {count:,} ({percentage:.1f}%)")

    # Directory analysis
    directories = []
    for event in events:
        path = event.get("path", "")
        if path:
            # Extract directory
            try:
                dir_path = str(Path(path).parent)
                directories.append(dir_path)
            except:
                continue

    dir_counts = Counter(directories)
    print("\n📂 Top Directories:")
    for directory, count in dir_counts.most_common(10):
        percentage = (count / len(directories)) * 100 if directories else 0
        # Truncate long paths
        display_dir = directory if len(directory) < 60 else "..." + directory[-57:]
        print(f"  {display_dir}: {count:,} ({percentage:.1f}%)")

    return {
        "actions": action_counts,
        "extensions": ext_counts,
        "directories": dir_counts,
    }


def identify_file_clusters(events, patterns):
    """Identify natural clusters in file operations"""

    print("\n🧬 Identifying File Operation Clusters...")
    print("=" * 50)

    clusters = defaultdict(list)

    # Cluster by file type and action
    for event in events:
        action = event.get("action", "unknown")
        ext = event.get("ext", "").lower()
        path = event.get("path", "")

        # Determine cluster key
        if ext in ["py", "js", "ts", "java", "cpp", "c", "h"]:
            cluster_key = f"code_{action}"
        elif ext in ["txt", "md", "doc", "docx", "pdf"]:
            cluster_key = f"document_{action}"
        elif ext in ["jpg", "png", "gif", "svg", "jpeg"]:
            cluster_key = f"image_{action}"
        elif ext in ["mp4", "avi", "mov", "mkv"]:
            cluster_key = f"video_{action}"
        elif ext in ["mp3", "wav", "flac", "m4a"]:
            cluster_key = f"audio_{action}"
        elif "temp" in path.lower() or "tmp" in path.lower():
            cluster_key = f"temp_{action}"
        elif ".git" in path:
            cluster_key = f"git_{action}"
        elif "node_modules" in path:
            cluster_key = f"deps_{action}"
        elif ext in ["log", "db", "sqlite"]:
            cluster_key = f"system_{action}"
        else:
            cluster_key = f"general_{action}"

        clusters[cluster_key].append(event)

    # Sort clusters by size
    sorted_clusters = sorted(clusters.items(), key=lambda x: len(x[1]), reverse=True)

    print("📊 File Operation Clusters:")
    total_events = len(events)

    for cluster_name, cluster_events in sorted_clusters:
        count = len(cluster_events)
        percentage = (count / total_events) * 100
        print(f"  {cluster_name}: {count:,} events ({percentage:.1f}%)")

        # Show sample paths for this cluster
        sample_paths = [e.get("path", "") for e in cluster_events[:3]]
        for path in sample_paths:
            if path:
                display_path = path if len(path) < 70 else "..." + path[-67:]
                print(f"    └─ {display_path}")

    return dict(sorted_clusters)


def suggest_agent_specializations(clusters):
    """Suggest agent specializations based on clusters"""

    print("\n🤖 Suggested FileOperationAgent Specializations:")
    print("=" * 50)

    total_events = sum(len(events) for events in clusters.values())

    # Group related clusters
    specializations = {
        "CodeFileAgent": [],
        "DocumentAgent": [],
        "MediaAgent": [],
        "SystemAgent": [],
        "GeneralFileAgent": [],
    }

    for cluster_name, events in clusters.items():
        if cluster_name.startswith("code_"):
            specializations["CodeFileAgent"].extend(events)
        elif cluster_name.startswith("document_"):
            specializations["DocumentAgent"].extend(events)
        elif cluster_name.startswith(("image_", "video_", "audio_")):
            specializations["MediaAgent"].extend(events)
        elif cluster_name.startswith(("system_", "temp_", "git_", "deps_")):
            specializations["SystemAgent"].extend(events)
        else:
            specializations["GeneralFileAgent"].extend(events)

    # Calculate parameters needed for each specialization
    for agent_name, agent_events in specializations.items():
        if not agent_events:
            continue

        count = len(agent_events)
        percentage = (count / total_events) * 100

        # Estimate parameters based on complexity and volume
        if count > 50000:
            params = 3_000_000
        elif count > 20000:
            params = 2_000_000
        elif count > 5000:
            params = 1_000_000
        elif count > 1000:
            params = 500_000
        else:
            params = 200_000

        print(f"\n🤖 {agent_name}:")
        print(f"   Training Data: {count:,} events ({percentage:.1f}%)")
        print(f"   Suggested Size: {params:,} parameters")

        # Analyze input/output patterns
        actions = Counter(e.get("action", "") for e in agent_events)
        extensions = Counter(e.get("ext", "") for e in agent_events if e.get("ext"))

        print(f"   Common Actions: {list(actions.keys())[:5]}")
        print(f"   Common Extensions: {list(extensions.keys())[:5]}")

        # Suggest input/output spec
        print(f"   Input Spec: {{path, action, ext, timestamp, size}}")
        print(f"   Output Spec: {{pattern_type, confidence, next_action_prediction}}")


def generate_training_labels(clusters):
    """Generate training labels for each cluster using patterns"""

    print("\n🏷️ Generating Training Labels...")
    print("=" * 50)

    labels = {}

    for cluster_name, events in clusters.items():
        cluster_labels = []

        for event in events[:100]:  # Sample for labeling
            # Generate label based on patterns
            action = event.get("action", "")
            ext = event.get("ext", "")
            path = event.get("path", "")

            # Pattern-based labeling
            if "create" in action and ext in ["py", "js"]:
                label = "new_code_file"
            elif "modify" in action and ext in ["py", "js"]:
                label = "code_edit"
            elif "create" in action and "test" in path.lower():
                label = "test_file_creation"
            elif "delete" in action and "temp" in path.lower():
                label = "temp_cleanup"
            elif "create" in action and ext in ["txt", "md"]:
                label = "document_creation"
            else:
                label = f"{action}_{ext}" if ext else action

            cluster_labels.append(
                {
                    "event": event,
                    "label": label,
                    "confidence": 0.8,  # Pattern-based confidence
                }
            )

        labels[cluster_name] = cluster_labels
        print(f"  {cluster_name}: {len(cluster_labels)} labeled examples")

    return labels


def main():
    """Main clustering analysis"""

    try:
        # Load file operations
        events = load_file_operations(limit=20000)  # Analyze 20K events

        if not events:
            print("❌ No file operation events found!")
            return

        # Analyze patterns
        patterns = analyze_file_patterns(events)

        # Identify clusters
        clusters = identify_file_clusters(events, patterns)

        # Suggest specializations
        suggest_agent_specializations(clusters)

        # Generate training labels
        labels = generate_training_labels(clusters)

        print("\n✅ File Operations Clustering Complete!")
        print(f"📊 Identified {len(clusters)} distinct clusters")
        print(f"🏷️ Generated {sum(len(l) for l in labels.values())} training labels")

        print("\n🎯 Next Steps for FileOperationAgent:")
        print("1. Use Gemma 3:4b to enhance and validate these labels")
        print("2. Design neural network architectures for each specialization")
        print("3. Train small networks on clustered data")
        print("4. Validate against holdout file operation data")
        print("5. Deploy specialized file operation agents")

    except Exception as e:
        print(f"❌ Error during clustering: {e}")
        import traceback

        traceback.print_exc()


if __name__ == "__main__":
    main()
