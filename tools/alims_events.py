#!/usr/bin/env python3
"""
ALims Events CLI Tool

Query and analyze persisted events from the ALims database.
"""

import sys
import os
import argparse
import json
from datetime import datetime, timedelta
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from app.system.event_persistence import EventDatabase


def format_timestamp(ts):
    """Format timestamp for display"""
    return datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M:%S")


def display_events(events, limit=None):
    """Display events in a readable format"""
    if not events:
        print("No events found.")
        return

    count = 0
    for event in events:
        if limit and count >= limit:
            break

        print(f"\n--- Event {event['id']} ---")
        print(f"Time: {format_timestamp(event['timestamp'])}")
        print(f"Type: {event['event_type']}")
        print(f"Action: {event.get('action', 'N/A')}")
        print(f"Source: {event['source']}")

        # Display relevant data fields
        data = event["data"]
        if event["event_type"] == "file_op":
            print(f"Path: {data.get('path', 'N/A')}")
            print(f"Name: {data.get('name', 'N/A')}")
        elif event["event_type"] == "app":
            print(f"App: {data.get('app', 'N/A')}")

        count += 1

    if limit and len(events) > limit:
        print(f"\n... and {len(events) - limit} more events")


def main():
    parser = argparse.ArgumentParser(description="ALims Events CLI Tool")
    parser.add_argument(
        "--db", default="data/events.db", help="Database path (default: data/events.db)"
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Stats command
    stats_parser = subparsers.add_parser("stats", help="Show database statistics")

    # List command
    list_parser = subparsers.add_parser("list", help="List events")
    list_parser.add_argument("--type", help="Filter by event type")
    list_parser.add_argument(
        "--hours", type=int, default=1, help="Hours to look back (default: 1)"
    )
    list_parser.add_argument(
        "--limit", type=int, default=20, help="Maximum events to show (default: 20)"
    )

    # Search command
    search_parser = subparsers.add_parser("search", help="Search events")
    search_parser.add_argument("query", help="Search query")
    search_parser.add_argument(
        "--limit", type=int, default=10, help="Maximum results (default: 10)"
    )

    # Export command
    export_parser = subparsers.add_parser("export", help="Export events to JSON")
    export_parser.add_argument("output", help="Output file path")
    export_parser.add_argument(
        "--hours", type=int, default=24, help="Hours to export (default: 24)"
    )

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return

    # Check if database exists
    if not os.path.exists(args.db):
        print(f"Database not found: {args.db}")
        print("Make sure ALims has been running with persistence enabled.")
        return

    try:
        db = EventDatabase(args.db)

        if args.command == "stats":
            stats = db.get_database_stats()
            print("📊 ALims Event Database Statistics")
            print("=" * 40)
            print(f"Total Events: {stats.get('total_events', 0):,}")
            print(f"Total Patterns: {stats.get('total_patterns', 0):,}")
            print(f"Database Size: {stats.get('database_size_mb', 0):.2f} MB")
            print(f"Recent Events (1h): {stats.get('recent_events_1h', 0):,}")
            print(f"Events per Hour: {stats.get('events_per_hour', 0):,}")

        elif args.command == "list":
            start_time = datetime.now() - timedelta(hours=args.hours)
            events = db.get_events(
                start_time=start_time.timestamp(),
                event_type=args.type,
                limit=args.limit * 2,  # Get more to account for filtering
            )

            print(f"📋 Recent Events (last {args.hours} hours)")
            print("=" * 50)
            display_events(events, args.limit)

        elif args.command == "search":
            # Simple search in event data
            all_events = db.get_events(limit=1000)
            matching_events = []

            query_lower = args.query.lower()
            for event in all_events:
                event_str = json.dumps(event["data"]).lower()
                if query_lower in event_str:
                    matching_events.append(event)

            print(f"🔍 Search Results for '{args.query}'")
            print("=" * 50)
            display_events(matching_events[: args.limit])

        elif args.command == "export":
            start_time = datetime.now() - timedelta(hours=args.hours)
            events = db.get_events(
                start_time=start_time.timestamp(), limit=10000  # Large limit for export
            )

            export_data = {
                "export_time": datetime.now().isoformat(),
                "time_range_hours": args.hours,
                "total_events": len(events),
                "events": events,
            }

            with open(args.output, "w") as f:
                json.dump(export_data, f, indent=2, default=str)

            print(f"📤 Exported {len(events)} events to {args.output}")

    except Exception as e:
        print(f"Error: {e}")
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
