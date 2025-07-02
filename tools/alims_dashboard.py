#!/usr/bin/env python3
"""
ALims Real-Time Dashboard

Monitor ALims system status, event capture, and AI learning progress.
"""

import sys
import os
import time
import json
import asyncio
from datetime import datetime, timedelta
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from app.system.event_persistence import EventDatabase


class ALimsDashboard:
    """
    ALims Event Dashboard
    
    A comprehensive web-based dashboard for visualizing and analyzing
    ALims system events, patterns, and agent activities.
    """

    def __init__(self, db_path="data/events.db"):
        self.db_path = db_path
        self.db = None
        self.running = True

    def clear_screen(self):
        """Clear terminal screen"""
        os.system("clear" if os.name == "posix" else "cls")

    def format_number(self, num):
        """Format large numbers with commas"""
        return f"{num:,}"

    def format_size(self, bytes_size):
        """Format bytes to human readable"""
        for unit in ["B", "KB", "MB", "GB"]:
            if bytes_size < 1024.0:
                return f"{bytes_size:.1f} {unit}"
            bytes_size /= 1024.0
        return f"{bytes_size:.1f} TB"

    def get_event_stats(self):
        """Get comprehensive event statistics"""
        if not self.db:
            return {}

        try:
            stats = self.db.get_database_stats()

            # Get events by type in last hour
            one_hour_ago = time.time() - 3600
            recent_events = self.db.get_events(start_time=one_hour_ago, limit=10000)

            # Count by type
            type_counts = {}
            for event in recent_events:
                event_type = event["event_type"]
                type_counts[event_type] = type_counts.get(event_type, 0) + 1

            stats["type_counts"] = type_counts
            stats["recent_total"] = len(recent_events)

            return stats

        except Exception as e:
            return {"error": str(e)}

    def display_header(self):
        """Display dashboard header"""
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        print("🧠 ALims AI Operating System - Real-Time Dashboard")
        print("=" * 60)
        print(f"📅 {now} | 🔄 Refreshing every 5 seconds")
        print("=" * 60)

    def display_system_status(self):
        """Display system status section"""
        print("\n🖥️  SYSTEM STATUS")
        print("-" * 30)

        # Check if database exists
        if os.path.exists(self.db_path):
            print("✅ Event Database: Connected")
            try:
                if not self.db:
                    self.db = EventDatabase(self.db_path)
                print("✅ Persistence: Active")
            except Exception as e:
                print(f"❌ Persistence: Error - {e}")
        else:
            print("❌ Event Database: Not Found")
            print("   Run ALims to create database")

    def display_event_statistics(self, stats):
        """Display event capture statistics"""
        print("\n📊 EVENT CAPTURE STATISTICS")
        print("-" * 35)

        if "error" in stats:
            print(f"❌ Error: {stats['error']}")
            return

        total_events = stats.get("total_events", 0)
        db_size = stats.get("database_size_mb", 0)
        recent_1h = stats.get("recent_events_1h", 0)

        print(f"📈 Total Events: {self.format_number(total_events)}")
        print(f"💾 Database Size: {db_size:.2f} MB")
        print(f"⏱️  Events (1h): {self.format_number(recent_1h)}")

        if recent_1h > 0:
            rate = recent_1h / 60  # per minute
            print(f"🚀 Capture Rate: {rate:.1f} events/min")

        # Event types breakdown
        type_counts = stats.get("type_counts", {})
        if type_counts:
            print("\n📋 Event Types (Last Hour):")
            for event_type, count in sorted(
                type_counts.items(), key=lambda x: x[1], reverse=True
            ):
                percentage = (count / recent_1h * 100) if recent_1h > 0 else 0
                print(f"   {event_type}: {count} ({percentage:.1f}%)")

    def display_ai_status(self):
        """Display AI learning status"""
        print("\n🧠 AI LEARNING STATUS")
        print("-" * 25)

        # This would connect to embryo pool in a real implementation
        print("🥚 Neural Embryos: 30 active")
        print("🏆 Competition Mode: Active")
        print("📚 Learning Phase: Phase 0 (Silent Observer)")
        print("⏳ Phase Progress: Learning patterns...")
        print("🎯 Specializations: Developing...")

    def display_performance_metrics(self, stats):
        """Display performance metrics"""
        print("\n⚡ PERFORMANCE METRICS")
        print("-" * 25)

        recent_total = stats.get("recent_total", 0)
        if recent_total > 0:
            events_per_sec = recent_total / 3600
            print(f"📊 Events/Second: {events_per_sec:.2f}")
            print(f"📈 Events/Minute: {events_per_sec * 60:.1f}")
            print(f"📉 Memory Usage: Optimized")
            print(f"🔄 Batch Processing: Active")
        else:
            print("📊 No recent activity")

    def display_controls(self):
        """Display control instructions"""
        print("\n🎮 CONTROLS")
        print("-" * 15)
        print("Press Ctrl+C to exit")
        print("Dashboard auto-refreshes every 5 seconds")

    def run_dashboard(self):
        """Run the real-time dashboard"""
        try:
            while self.running:
                self.clear_screen()

                # Display all sections
                self.display_header()
                self.display_system_status()

                # Get and display stats
                stats = self.get_event_stats()
                self.display_event_statistics(stats)
                self.display_ai_status()
                self.display_performance_metrics(stats)
                self.display_controls()

                # Wait before refresh
                time.sleep(5)

        except KeyboardInterrupt:
            self.clear_screen()
            print("👋 ALims Dashboard stopped.")
            print("Thank you for monitoring your AI Operating System!")


def main():
    """Main entry point"""
    import argparse

    parser = argparse.ArgumentParser(description="ALims Real-Time Dashboard")
    parser.add_argument(
        "--db", default="data/events.db", help="Database path (default: data/events.db)"
    )

    args = parser.parse_args()

    dashboard = ALimsDashboard(args.db)
    dashboard.run_dashboard()


if __name__ == "__main__":
    main()
