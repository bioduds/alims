#!/usr/bin/env python3
"""
Analyze ALims Event Data for Natural Clustering
This script examines the actual event data to understand what patterns exist
and what types of agents should naturally emerge from the data.
"""

import sqlite3
import json
from collections import Counter, defaultdict
from datetime import datetime


def analyze_event_database(db_path="data/events.db"):
    """Analyze the event database to understand natural patterns"""

    print("🔍 Analyzing ALims Event Database...")
    print("=" * 50)

    conn = sqlite3.connect(db_path)

    # Basic statistics
    cursor = conn.cursor()
    cursor.execute("SELECT COUNT(*) FROM events")
    total_events = cursor.fetchone()[0]
    print(f"Total Events: {total_events:,}")

    # Event type distribution
    print("\n📊 Event Type Distribution:")
    cursor.execute(
        "SELECT event_type, COUNT(*) as count FROM events GROUP BY event_type ORDER BY count DESC"
    )
    event_types = cursor.fetchall()

    for event_type, count in event_types:
        percentage = (count / total_events) * 100
        print(f"  {event_type}: {count:,} ({percentage:.1f}%)")

    # Source distribution
    print("\n🎯 Event Sources:")
    cursor.execute(
        "SELECT source, COUNT(*) as count FROM events GROUP BY source ORDER BY count DESC LIMIT 10"
    )
    sources = cursor.fetchall()

    for source, count in sources:
        percentage = (count / total_events) * 100
        print(f"  {source}: {count:,} ({percentage:.1f}%)")

    # Time-based analysis
    print("\n⏰ Temporal Patterns:")
    cursor.execute("SELECT timestamp FROM events ORDER BY timestamp DESC LIMIT 1000")
    recent_timestamps = [row[0] for row in cursor.fetchall()]

    if recent_timestamps:
        latest = datetime.fromtimestamp(recent_timestamps[0])
        oldest = datetime.fromtimestamp(recent_timestamps[-1])
        print(f"  Latest Event: {latest}")
        print(f"  Oldest Recent: {oldest}")
        print(f"  Time Span: {latest - oldest}")

    # Sample event data analysis
    print("\n🔬 Sample Event Data Analysis:")
    cursor.execute(
        "SELECT event_type, data_json FROM events WHERE data_json IS NOT NULL LIMIT 100"
    )
    sample_events = cursor.fetchall()

    event_data_patterns = defaultdict(list)

    for event_type, data_json in sample_events:
        try:
            data = json.loads(data_json)
            event_data_patterns[event_type].append(data)
        except:
            continue

    for event_type, data_list in event_data_patterns.items():
        print(f"\n  {event_type} Events:")
        if data_list:
            # Analyze common keys
            all_keys = []
            for data in data_list:
                if isinstance(data, dict):
                    all_keys.extend(data.keys())

            key_counts = Counter(all_keys)
            common_keys = key_counts.most_common(5)
            print(f"    Common fields: {[k for k, c in common_keys]}")

            # Sample data
            if len(data_list) > 0:
                sample = data_list[0]
                print(f"    Sample: {str(sample)[:100]}...")

    conn.close()

    return {
        "total_events": total_events,
        "event_types": event_types,
        "sources": sources,
        "event_data_patterns": dict(event_data_patterns),
    }


def identify_natural_clusters(analysis_results):
    """Identify natural clusters that should become agents"""

    print("\n🧬 Natural Agent Clusters Analysis:")
    print("=" * 50)

    event_types = analysis_results["event_types"]
    total_events = analysis_results["total_events"]

    # Cluster by volume and characteristics
    high_volume_types = []
    medium_volume_types = []
    low_volume_types = []

    for event_type, count in event_types:
        percentage = (count / total_events) * 100

        if percentage > 20:
            high_volume_types.append((event_type, count, percentage))
        elif percentage > 5:
            medium_volume_types.append((event_type, count, percentage))
        else:
            low_volume_types.append((event_type, count, percentage))

    print("🔥 High Volume Event Types (>20% of data):")
    for event_type, count, pct in high_volume_types:
        print(f"  → {event_type}: {count:,} events ({pct:.1f}%)")
        print(f"    Potential Agent: {event_type.title()}Agent")

    print("\n📈 Medium Volume Event Types (5-20% of data):")
    for event_type, count, pct in medium_volume_types:
        print(f"  → {event_type}: {count:,} events ({pct:.1f}%)")
        print(f"    Potential Agent: {event_type.title()}Agent")

    print("\n📊 Low Volume Event Types (<5% of data):")
    for event_type, count, pct in low_volume_types[:10]:  # Show top 10
        print(f"  → {event_type}: {count:,} events ({pct:.1f}%)")

    if len(low_volume_types) > 10:
        print(f"  ... and {len(low_volume_types) - 10} more low-volume types")

    # Suggest agent architecture based on data
    print("\n🤖 Suggested Agent Architecture (Data-Driven):")
    print("=" * 50)

    suggested_agents = []

    # High-volume types get dedicated agents
    for event_type, count, pct in high_volume_types:
        agent_name = f"{event_type.title()}Agent"
        suggested_agents.append(
            {
                "name": agent_name,
                "specialization": event_type,
                "data_volume": count,
                "data_percentage": pct,
                "suggested_params": estimate_params_needed(count),
                "priority": "HIGH",
            }
        )

    # Medium-volume types might get combined agents
    for event_type, count, pct in medium_volume_types:
        agent_name = f"{event_type.title()}Agent"
        suggested_agents.append(
            {
                "name": agent_name,
                "specialization": event_type,
                "data_volume": count,
                "data_percentage": pct,
                "suggested_params": estimate_params_needed(count),
                "priority": "MEDIUM",
            }
        )

    # Low-volume types get a general agent
    if low_volume_types:
        total_low_volume = sum(count for _, count, _ in low_volume_types)
        suggested_agents.append(
            {
                "name": "GeneralPurposeAgent",
                "specialization": "multiple_low_volume_types",
                "data_volume": total_low_volume,
                "data_percentage": (total_low_volume / total_events) * 100,
                "suggested_params": estimate_params_needed(total_low_volume),
                "priority": "LOW",
            }
        )

    for agent in suggested_agents:
        print(f"\n🤖 {agent['name']}:")
        print(f"   Specialization: {agent['specialization']}")
        print(
            f"   Training Data: {agent['data_volume']:,} events ({agent['data_percentage']:.1f}%)"
        )
        print(f"   Suggested Size: {agent['suggested_params']:,} parameters")
        print(f"   Priority: {agent['priority']}")

    return suggested_agents


def estimate_params_needed(event_count):
    """Estimate neural network parameters needed based on data volume"""

    # Rough heuristic: more data allows for larger networks
    if event_count > 50000:
        return 5_000_000  # 5M params
    elif event_count > 20000:
        return 3_000_000  # 3M params
    elif event_count > 5000:
        return 1_000_000  # 1M params
    elif event_count > 1000:
        return 500_000  # 500K params
    else:
        return 100_000  # 100K params


def main():
    """Main analysis function"""

    try:
        # Analyze the database
        analysis_results = analyze_event_database()

        # Identify natural clusters
        suggested_agents = identify_natural_clusters(analysis_results)

        print("\n✅ Analysis Complete!")
        print(f"📊 Found {len(analysis_results['event_types'])} distinct event types")
        print(f"🤖 Suggested {len(suggested_agents)} specialized agents")

        print("\n🎯 Next Steps:")
        print("1. Implement clustering algorithm for each major event type")
        print("2. Use Gemma 3:4b to generate labels for clustered data")
        print("3. Design and train small neural networks for each agent")
        print("4. Validate agents against holdout data")
        print("5. Deploy agents with clear input/output specifications")

    except Exception as e:
        print(f"❌ Error during analysis: {e}")
        import traceback

        traceback.print_exc()


if __name__ == "__main__":
    main()
