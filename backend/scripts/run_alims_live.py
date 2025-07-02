#!/usr/bin/env python3
"""
ALims Live Agent System

Run the complete ALims system with real-time agent monitoring.
This provides a comprehensive dashboard for monitoring agent births,
system performance, and real-time event processing.
"""

import asyncio
import logging
import signal
import sys
import time
from datetime import datetime
from pathlib import Path

# Add project root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from backend.app.system.system_integration import ALimsSystemIntegration


class ALimsLiveMonitor:
    """Live monitoring and dashboard for ALims agents"""
    
    def __init__(self):
        self.running = False
        self.system_integration = None
        self.start_time = datetime.now()
        
        # Setup signal handlers for graceful shutdown
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)
        
        # Setup logging
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )
        self.logger = logging.getLogger('ALimsLiveMonitor')
    
    async def start_system(self):
        """Start the complete ALims system"""
        try:
            self.logger.info("🚀 Initializing ALims System Integration...")
            
            # Configuration for the system
            config = {
                "max_agents": 50,
                "agent_birth_threshold": 100,
                "pattern_detection_enabled": True,
                "privacy_mode": True,
                "learning_rate": 0.1,
                "event_batch_size": 50,
                "system_monitoring": True,
                "tray_integration": True,
                "web_dashboard": False,  # Disabled for live mode
                "ai_brain_enabled": True,
                "embryo_pool_size": 20
            }
            
            print("🚀 Starting Complete ALims System...")
            print("=" * 60)
            
            # Initialize system integration
            self.system_integration = ALimsSystemIntegration(config)
            
            # Start all system components
            await self.system_integration.start()
            
            self.running = True
            
            print("✅ ALims System Online!")
            print("🎭 Monitoring agent births and system performance...")
            print("🔄 Press Ctrl+C to stop the system")
            print("=" * 60)
            
            # Start the monitoring loop
            await self._monitoring_loop()
            
        except Exception as e:
            self.logger.error(f"Failed to start ALims system: {e}")
            raise
    
    async def _monitoring_loop(self):
        """Main monitoring loop with live dashboard"""
        last_stats_time = time.time()
        stats_interval = 30  # Show stats every 30 seconds
        
        while self.running:
            try:
                current_time = time.time()
                
                # Show periodic stats
                if current_time - last_stats_time >= stats_interval:
                    await self._show_live_dashboard()
                    last_stats_time = current_time
                
                # Brief sleep to prevent CPU spinning
                await asyncio.sleep(1)
                
            except Exception as e:
                self.logger.error(f"Error in monitoring loop: {e}")
                await asyncio.sleep(5)
    
    async def _show_live_dashboard(self):
        """Display live system dashboard"""
        print("\n🎭 ALIMS LIVE AGENT DASHBOARD")
        print("=" * 50)
        
        # System uptime
        uptime = datetime.now() - self.start_time
        print(f"⏱️  System Uptime: {uptime}")
        
        if self.system_integration:
            # Get system stats
            try:
                stats = await self.system_integration.get_system_stats()
                
                print(f"🤖 Active Agents: {stats.get('active_agents', 0)}")
                print(f"🥚 Embryo Pool: {stats.get('embryo_count', 0)}")
                print(f"📊 Events Processed: {stats.get('total_events', 0)}")
                print(f"🔄 Events/Min: {stats.get('events_per_minute', 0):.1f}")
                print(f"💾 Database Size: {stats.get('db_size_mb', 0):.1f} MB")
                print(f"🧠 AI Brain Status: {stats.get('ai_brain_status', 'Unknown')}")
                
                # Recent agent births
                recent_births = stats.get('recent_agent_births', [])
                if recent_births:
                    print(f"🎉 Recent Agent Births: {len(recent_births)}")
                    for birth in recent_births[-3:]:  # Show last 3
                        print(f"   • {birth.get('name', 'Unknown')} - {birth.get('specialization', 'General')}")
                
            except Exception as e:
                print(f"❌ Error getting system stats: {e}")
        
        print("=" * 50)
    
    def _signal_handler(self, signum, frame):
        """Handle shutdown signals gracefully"""
        print("\n🛑 Stopping ALims system...")
        self.running = False
    
    async def stop_system(self):
        """Stop the ALims system gracefully"""
        if self.system_integration:
            try:
                await self.system_integration.stop()
                print("✅ ALims system stopped gracefully")
            except Exception as e:
                self.logger.error(f"Error stopping system: {e}")


def print_banner():
    """Print the ALims banner"""
    banner = """
    ╔══════════════════════════════════════════════════════════════╗
    ║                                                              ║
    ║    🧬 ALims Live Agent System - Real-Time Monitor         ║
    ║                                                              ║
    ║    • Real-time agent birth monitoring                       ║
    ║    • System performance tracking                            ║
    ║    • Event processing statistics                            ║
    ║    • AI brain status monitoring                             ║
    ║                                                              ║
    ╚══════════════════════════════════════════════════════════════╝
    """
    print(banner)


async def main():
    """Main entry point"""
    print_banner()
    
    monitor = ALimsLiveMonitor()
    
    try:
        await monitor.start_system()
    except KeyboardInterrupt:
        print("\n🛑 Received interrupt signal")
    except Exception as e:
        print(f"❌ System error: {e}")
        logging.exception("System error")
    finally:
        await monitor.stop_system()


def stop_alims_system():
    """Stop the ALims system"""
    import os
    import psutil
    
    print("🛑 Shutting down ALims system...")
    
    # Find and terminate ALims processes
    for proc in psutil.process_iter(['pid', 'name', 'cmdline']):
        try:
            cmdline = ' '.join(proc.info['cmdline'] or [])
            if 'alims' in cmdline.lower() or 'run_alims_live' in cmdline:
                print(f"Terminating process {proc.info['pid']}: {proc.info['name']}")
                proc.terminate()
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            pass
    
    print("✅ ALims system stopped")


if __name__ == "__main__":
    # Setup logging
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        handlers=[logging.FileHandler("alims_live.log"), logging.StreamHandler()],
    )
    
    monitor = ALimsLiveMonitor()
    
    try:
        asyncio.run(monitor.start_system())
    except KeyboardInterrupt:
        print("\n🛑 Received interrupt signal")
    except Exception as e:
        print(f"❌ System error: {e}")
        logging.exception("System error")
    finally:
        asyncio.run(monitor.stop_system())
