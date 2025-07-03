#!/usr/bin/env python3
"""
ALims Tauri-Integrated System Tray

Enhanced system tray that launches the beautiful Tauri desktop application
and provides comprehensive system management capabilities.
"""

import logging
import sqlite3
import subprocess
import threading
import time
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Optional

try:
    import rumps
    RUMPS_AVAILABLE = True
except ImportError:
    RUMPS_AVAILABLE = False
    print("Warning: rumps not available. Install with: pip install rumps")

from ..core.agent_manager import AgentManager
from ..ai.central_brain import create_central_brain

logger = logging.getLogger(__name__)


class TauriDesktopLauncher:
    """Handles launching and managing the Tauri desktop application"""
    
    def __init__(self):
        self.desktop_process = None
        self.is_running = False
        self.project_root = Path.cwd()
        # Launch immediately on initialization
        threading.Thread(target=self.launch_desktop_app, daemon=True).start()
        
    def check_tauri_requirements(self) -> Dict[str, bool]:
        """Check if Tauri requirements are met"""
        requirements = {
            'node_modules': (
                self.project_root / 'frontend' / 'desktop' / 'node_modules'
            ).exists(),
            'package_json': (
                self.project_root / 'frontend' / 'desktop' / 'package.json'
            ).exists(),
            'tauri_config': (
                self.project_root / 'frontend' / 'desktop' / 'src-tauri' / 
                'tauri.conf.json'
            ).exists(),
            'rust_installed': self._check_rust_installed(),
            'tauri_cli': self._check_tauri_cli(),
        }
        return requirements
    
    def _check_rust_installed(self) -> bool:
        """Check if Rust is installed"""
        try:
            result = subprocess.run(
                ['rustc', '--version'], 
                capture_output=True, 
                text=True, 
                timeout=5
            )
            return result.returncode == 0
        except (subprocess.TimeoutExpired, FileNotFoundError):
            return False
    
    def _check_tauri_cli(self) -> bool:
        """Check if Tauri CLI is installed"""
        try:
            result = subprocess.run(
                ['cargo', 'tauri', '--version'], 
                capture_output=True, 
                text=True, 
                timeout=5
            )
            return result.returncode == 0
        except (subprocess.TimeoutExpired, FileNotFoundError):
            return False
    
    def launch_desktop_app(self) -> bool:
        """Launch the Tauri desktop application"""
        if self.is_running:
            logger.info("Desktop app is already running")
            return True
            
        try:
            # Check requirements first
            requirements = self.check_tauri_requirements()
            missing = [k for k, v in requirements.items() if not v]
            
            if missing:
                logger.error(f"Missing requirements for desktop app: {missing}")
                return False
            
            # Launch the desktop app
            logger.info("Launching Tauri desktop application...")
            
            # Use npm run tauri:dev for development mode with --no-watch to start immediately
            desktop_dir = self.project_root / 'frontend' / 'desktop'
            self.desktop_process = subprocess.Popen(
                ['npm', 'run', 'tauri:dev', '--', '--no-watch'],
                cwd=str(desktop_dir),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            
            self.is_running = True
            logger.info(f"Desktop app launched with PID: {self.desktop_process.pid}")
            
            # Start monitoring thread
            threading.Thread(
                target=self._monitor_desktop_app, 
                daemon=True
            ).start()
            
            return True
            
        except Exception as e:
            logger.error(f"Failed to launch desktop app: {e}")
            return False
    
    def _monitor_desktop_app(self):
        """Monitor the desktop app process"""
        if not self.desktop_process:
            return
            
        try:
            # Wait for process to complete
            self.desktop_process.wait()
            self.is_running = False
            logger.info("Desktop app process ended")
        except Exception as e:
            logger.error(f"Error monitoring desktop app: {e}")
            self.is_running = False
    
    def stop_desktop_app(self):
        """Stop the desktop application"""
        if self.desktop_process and self.is_running:
            try:
                self.desktop_process.terminate()
                self.desktop_process.wait(timeout=5)
                logger.info("Desktop app stopped gracefully")
            except subprocess.TimeoutExpired:
                self.desktop_process.kill()
                logger.info("Desktop app force killed")
            except Exception as e:
                logger.error(f"Error stopping desktop app: {e}")
            finally:
                self.is_running = False
                self.desktop_process = None


class SystemMonitor:
    """Monitors system statistics and performance"""
    
    def __init__(self):
        self.stats = {
            'events_today': 0,
            'total_events': 0,
            'active_agents': 0,
            'system_health': 'Good',
            'db_size': '0 MB',
            'uptime': '0m',
        }
        self.start_time = datetime.now()
        
    def update_stats(self):
        """Update system statistics"""
        try:
            # Database stats
            db_path = Path('data/events.db')
            if db_path.exists():
                # Get database size
                size_bytes = db_path.stat().st_size
                self.stats['db_size'] = f"{size_bytes / (1024*1024):.1f} MB"
                
                # Get event counts
                conn = sqlite3.connect(str(db_path))
                cursor = conn.cursor()
                
                # Total events
                cursor.execute("SELECT COUNT(*) FROM events")
                self.stats['total_events'] = cursor.fetchone()[0]
                
                # Events today
                today = datetime.now().strftime("%Y-%m-%d")
                cursor.execute(
                    "SELECT COUNT(*) FROM events "
                    "WHERE date(datetime(timestamp, 'unixepoch')) = ?",
                    (today,)
                )
                self.stats['events_today'] = cursor.fetchone()[0]
                
                conn.close()
            
            # Calculate uptime
            uptime_delta = datetime.now() - self.start_time
            hours = uptime_delta.seconds // 3600
            minutes = (uptime_delta.seconds % 3600) // 60
            
            if hours > 0:
                self.stats['uptime'] = f"{hours}h {minutes}m"
            else:
                self.stats['uptime'] = f"{minutes}m"
                
        except Exception as e:
            logger.error(f"Error updating system stats: {e}")


class TauriIntegratedTray(rumps.App):
    """Enhanced system tray with Tauri desktop app integration"""
    
    def __init__(
        self, 
        agent_manager: Optional[AgentManager] = None, 
        config: Optional[Dict[str, Any]] = None
    ):
        super().__init__("🧬", quit_button=None)
        
        self.agent_manager = agent_manager
        self.config = config or {}
        self.central_brain = None
        self.system_monitor = SystemMonitor()
        self.desktop_launcher = TauriDesktopLauncher()
        
        # Initialize menu
        self._setup_menu()
        
        # Initialize AI brain in background
        self._initialize_ai_brain()
        
        # Start monitoring
        self._start_monitoring()
        
        # Launch desktop app directly (don't wait for auto-launch)
        self._launch_desktop_directly()
    
    def _launch_desktop_directly(self):
        """Launch desktop app directly using subprocess"""
        try:
            logger.info("Directly launching desktop app...")
            desktop_dir = Path.cwd() / 'frontend' / 'desktop'
            
            # Use a direct command to launch the desktop app
            subprocess.Popen(
                ['npm', 'run', 'tauri:dev', '--', '--no-watch'],
                cwd=str(desktop_dir),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            
            logger.info("Desktop app launch command executed")
        except Exception as e:
            logger.error(f"Error directly launching desktop app: {e}")
    
    def _setup_menu(self):
        """Set up the menu structure"""
        self.menu = [
            rumps.MenuItem("🖥️ Launch Desktop App", callback=self.launch_desktop_app),
            None,  # Separator
            rumps.MenuItem("📊 System Status", callback=self.show_system_status),
            rumps.MenuItem("🤖 Agent Status", callback=self.show_agent_status),
            rumps.MenuItem("🥚 Embryo Pool", callback=self.show_embryo_pool),
            rumps.MenuItem("📈 Performance", callback=self.show_performance),
            None,  # Separator
            rumps.MenuItem("🔄 Force Agent Birth", callback=self.force_agent_birth),
            rumps.MenuItem("⚙️ Settings", callback=self.show_settings),
            rumps.MenuItem("❓ About", callback=self.show_about),
            None,  # Separator
            rumps.MenuItem("🔄 Restart System", callback=self.restart_system),
            rumps.MenuItem("🛑 Stop System", callback=self.stop_system)
        ]
    
    def _initialize_ai_brain(self):
        """Initialize the central AI brain in a background thread"""
        def init_brain():
            try:
                self.central_brain = create_central_brain()
                logger.info("Central AI brain initialized successfully")
            except Exception as e:
                logger.error(f"Failed to initialize central brain: {e}")
        
        # Start initialization in background
        threading.Thread(target=init_brain, daemon=True).start()
    
    def _start_monitoring(self):
        """Start system monitoring in background"""
        def monitor_loop():
            while True:
                try:
                    self.system_monitor.update_stats()
                    self._update_title()
                except Exception as e:
                    logger.error(f"Error in monitor loop: {e}")
                time.sleep(30)  # Update every 30 seconds
        
        # Start monitoring in background
        threading.Thread(target=monitor_loop, daemon=True).start()
    
    def _update_title(self):
        """Update the menu bar title with current stats"""
        try:
            events_today = self.system_monitor.stats['events_today']
            active_agents = self.system_monitor.stats['active_agents']
            self.title = f"🧬 {events_today}↑ {active_agents}🤖"
        except Exception as e:
            logger.error(f"Error updating title: {e}")
            self.title = "🧬"
    
    @rumps.clicked("🖥️ Launch Desktop App")
    def launch_desktop_app(self, _):
        """Launch the Tauri desktop application"""
        try:
            if self.desktop_launcher.launch_desktop_app():
            rumps.notification(
                    title="ALims Desktop",
                    subtitle="Desktop App Launched",
                    message="The ALims desktop application is starting..."
                )
            else:
                rumps.notification(
                    title="ALims Desktop",
                    subtitle="Launch Failed",
                    message="Failed to launch desktop app. Check requirements."
                )
        except Exception as e:
            logger.error(f"Error launching desktop app: {e}")
            rumps.notification(
                title="ALims Desktop",
                subtitle="Error",
                message=f"Error launching desktop app: {e}"
            )
    
    @rumps.clicked("📊 System Status")
    def show_system_status(self, _):
        """Show system status window"""
        try:
        stats = self.system_monitor.stats
            window = rumps.Window(
                title="ALims System Status",
                message=(
                    f"Events Today: {stats['events_today']}\n"
                    f"Total Events: {stats['total_events']}\n"
                    f"Active Agents: {stats['active_agents']}\n"
                    f"System Health: {stats['system_health']}\n"
                    f"Database Size: {stats['db_size']}\n"
                    f"Uptime: {stats['uptime']}"
                ),
                dimensions=(300, 200)
            )
            window.run()
        except Exception as e:
            logger.error(f"Error showing system status: {e}")
    
    @rumps.clicked("🤖 Agent Status")
    def show_agent_status(self, _):
        """Show agent status window"""
        try:
            if not self.agent_manager:
                rumps.notification(
                    title="ALims",
                    subtitle="Agent Status",
                    message="Agent manager not initialized"
                )
                return
                
            agents = self.agent_manager.list_agents()
            if not agents:
                message = "No active agents found"
            else:
                message = "Active Agents:\n\n"
                for agent in agents:
                    message += (
                        f"Agent: {agent.name}\n"
                        f"Type: {agent.agent_type}\n"
                        f"Status: {agent.status}\n"
                        f"Events Handled: {agent.events_handled}\n"
                        f"Success Rate: {agent.success_rate:.2f}%\n\n"
                    )
            
            window = rumps.Window(
                title="ALims Agent Status",
                message=message,
                dimensions=(400, 300)
                )
            window.run()
            except Exception as e:
            logger.error(f"Error showing agent status: {e}")
    
    @rumps.clicked("🥚 Embryo Pool")
    def show_embryo_pool(self, _):
        """Show embryo pool status"""
        try:
            if not self.agent_manager:
                rumps.notification(
                    title="ALims",
                    subtitle="Embryo Pool",
                    message="Agent manager not initialized"
                )
                return
                
            embryos = self.agent_manager.list_embryos()
            message = f"Embryos in Pool: {len(embryos)}\n\n"
            
            for embryo in embryos:
                message += (
                    f"Type: {embryo.embryo_type}\n"
                    f"Fitness: {embryo.fitness_score:.2f}\n"
                    f"Age: {embryo.age} cycles\n\n"
                )
            
            window = rumps.Window(
                title="ALims Embryo Pool",
                message=message,
                dimensions=(300, 200)
            )
            window.run()
        except Exception as e:
            logger.error(f"Error showing embryo pool: {e}")
    
    @rumps.clicked("📈 Performance")
    def show_performance(self, _):
        """Show performance metrics"""
        try:
        stats = self.system_monitor.stats
            message = (
                f"System Performance:\n\n"
                f"Events/Hour: {stats.get('events_per_hour', 0)}\n"
                f"CPU Usage: {stats.get('cpu_usage', 0):.1f}%\n"
                f"Memory Usage: {stats.get('memory_usage', 0):.1f} MB\n"
                f"Database Size: {stats['db_size']}\n"
                f"Active Agents: {stats['active_agents']}"
            )
            
            window = rumps.Window(
                title="ALims Performance",
                message=message,
                dimensions=(300, 200)
            )
            window.run()
        except Exception as e:
            logger.error(f"Error showing performance: {e}")
    
    @rumps.clicked("🔄 Force Agent Birth")
    def force_agent_birth(self, _):
        """Force the birth of a new agent"""
            try:
            if not self.agent_manager:
                rumps.notification(
                    title="ALims",
                    subtitle="Agent Birth",
                    message="Agent manager not initialized"
                )
                return
                
            # Attempt to birth a new agent
            success = self.agent_manager.force_birth()
            
            if success:
                rumps.notification(
                    title="ALims",
                    subtitle="Agent Birth",
                    message="New agent successfully birthed!"
                )
            else:
                rumps.notification(
                    title="ALims",
                    subtitle="Agent Birth Failed",
                    message="Failed to birth new agent"
                )
            except Exception as e:
                logger.error(f"Error forcing agent birth: {e}")
    
    @rumps.clicked("⚙️ Settings")
    def show_settings(self, _):
        """Show settings window"""
        try:
            message = (
                "ALims Settings\n\n"
                "Current Configuration:\n"
                f"Max Agents: {self.config.get('max_agents', 5)}\n"
                f"Birth Rate: {self.config.get('birth_rate', 0.1):.2f}\n"
                f"Learning Rate: {self.config.get('learning_rate', 0.01):.3f}\n"
                f"Auto-Evolution: {'Enabled' if self.config.get('auto_evolution', True) else 'Disabled'}"
            )
            
            window = rumps.Window(
                title="ALims Settings",
                message=message,
                dimensions=(300, 200)
            )
            window.run()
        except Exception as e:
            logger.error(f"Error showing settings: {e}")
    
    @rumps.clicked("❓ About")
    def show_about(self, _):
        """Show about window"""
        try:
            message = (
                "ALims - Self-Creating AI Operating System\n\n"
                "Version: 0.1.0\n"
                "Status: Development\n\n"
                "A revolutionary AI system that:\n"
                "• Creates specialized AI agents\n"
                "• Evolves through continuous learning\n"
                "• Adapts to your workflow patterns\n"
                "• Operates with complete privacy\n\n"
                "© 2024 ALims"
            )
            
            window = rumps.Window(
            title="About ALims",
                message=message,
                dimensions=(400, 300)
        )
            window.run()
        except Exception as e:
            logger.error(f"Error showing about: {e}")
    
    @rumps.clicked("🔄 Restart System")
    def restart_system(self, _):
        """Restart the entire ALims system"""
        try:
            # Confirm restart
            window = rumps.Window(
                title="Restart ALims?",
                message="This will restart all ALims components.\nAre you sure?",
                dimensions=(300, 100),
            ok="Restart",
            cancel="Cancel"
        )
        
            if not window.run().clicked:
                return
                
                # Stop desktop app if running
                    self.desktop_launcher.stop_desktop_app()
                
            # Use the launch script to restart
            script_path = Path("launch_alims.sh")
            if script_path.exists():
                subprocess.run(["./launch_alims.sh", "restart"])
            else:
                logger.error("Launch script not found")
                rumps.notification(
                    title="ALims",
                    subtitle="Restart Failed",
                    message="Launch script not found"
                )
            except Exception as e:
                logger.error(f"Error restarting system: {e}")
    
    @rumps.clicked("🛑 Stop System")
    def stop_system(self, _):
        """Stop the ALims system"""
        try:
            # Confirm stop
            window = rumps.Window(
                title="Stop ALims?",
                message="This will stop all ALims components.\nAre you sure?",
                dimensions=(300, 100),
            ok="Stop",
            cancel="Cancel"
        )
        
            if not window.run().clicked:
                return
            
                # Stop desktop app if running
                    self.desktop_launcher.stop_desktop_app()
                
            # Use the launch script to stop
            script_path = Path("launch_alims.sh")
            if script_path.exists():
                subprocess.run(["./launch_alims.sh", "stop"])
            else:
                logger.error("Launch script not found")
                rumps.notification(
                    title="ALims",
                    subtitle="Stop Failed",
                    message="Launch script not found"
                )
                
            # Quit the tray app
                rumps.quit_application()
            except Exception as e:
                logger.error(f"Error stopping system: {e}")


def create_tauri_integrated_tray(
    agent_manager: Optional[AgentManager] = None, 
    config: Optional[Dict[str, Any]] = None
) -> Optional[TauriIntegratedTray]:
    """Create and configure the Tauri-integrated system tray"""
    
    if not RUMPS_AVAILABLE:
        logger.error("Cannot create tray - rumps not available")
        return None
    
    try:
        tray = TauriIntegratedTray(agent_manager, config)
        logger.info("Tauri-integrated tray created successfully")
        return tray
    except Exception as e:
        logger.error(f"Failed to create Tauri-integrated tray: {e}")
        return None


def main():
    """Main entry point"""
    if not RUMPS_AVAILABLE:
        print("Error: rumps not available. Install with: pip install rumps")
        return
        
    tray = create_tauri_integrated_tray()
    if tray:
        tray.run()
    else:
        print("Error: Failed to create tray application")


if __name__ == "__main__":
    main() 