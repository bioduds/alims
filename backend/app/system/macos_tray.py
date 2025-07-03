#!/usr/bin/env python3
"""
ALims System Tray for macOS

This module provides the system tray functionality for ALims on macOS.
"""

import logging
import subprocess
import threading
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


class MacOSTray(rumps.App):
    """ALims system tray for macOS"""
    
    def __init__(
        self, 
        agent_manager: Optional[AgentManager] = None, 
        config: Optional[Dict[str, Any]] = None
    ):
        super().__init__("🧬", quit_button=None)

        self.agent_manager = agent_manager
        self.config = config or {}
        self.central_brain = None
        
        # Initialize menu
        self._setup_menu()
        
        # Initialize AI brain in background
        self._initialize_ai_brain()

        logger.info("MacOS tray initialized")
    
    def _setup_menu(self) -> None:
        """Set up the menu structure"""
        self.menu = [
            rumps.MenuItem(
                "📊 System Status", 
                callback=self.show_system_status
            ),
            rumps.MenuItem(
                "🤖 Agent Status", 
                callback=self.show_agent_status
            ),
            rumps.MenuItem(
                "🥚 Embryo Pool", 
                callback=self.show_embryo_pool
            ),
            rumps.MenuItem(
                "📈 Performance", 
                callback=self.show_performance
            ),
            None,  # Separator
            rumps.MenuItem(
                "🔄 Force Agent Birth", 
                callback=self.force_agent_birth
            ),
            rumps.MenuItem(
                "⚙️ Settings", 
                callback=self.show_settings
            ),
            rumps.MenuItem(
                "❓ About", 
                callback=self.show_about
            ),
            None,  # Separator
            rumps.MenuItem(
                "🔄 Restart System", 
                callback=self.restart_system
            ),
            rumps.MenuItem(
                "🛑 Stop System", 
                callback=self.stop_system
            )
        ]
    
    def _initialize_ai_brain(self) -> None:
        """Initialize the central AI brain in a background thread"""
        def init_brain():
            try:
                config = {'ai': {'model': 'gemma3:4b'}}  # Basic config
                self.central_brain = create_central_brain(config)
                logger.info("Central AI brain initialized successfully")
            except Exception as e:
                logger.error(f"Failed to initialize central brain: {e}")

        # Start initialization in background
        threading.Thread(target=init_brain, daemon=True).start()

    @rumps.clicked("📊 System Status")
    def show_system_status(self, _):
        """Show system status window"""
        try:
            message = (
                "System Status:\n\n"
                "• Events Today: 0\n"
                "• Total Events: 0\n"
                "• Active Agents: 0\n"
                "• System Health: Good\n"
                "• Database Size: 0 MB\n"
                "• Uptime: 0m"
            )
            
            window = rumps.Window(
                title="ALims System Status",
                message=message,
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
            message = (
                "System Performance:\n\n"
                "• Events/Hour: 0\n"
                "• CPU Usage: 0.0%\n"
                "• Memory Usage: 0.0 MB\n"
                "• Database Size: 0 MB\n"
                "• Active Agents: 0"
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


def create_macos_tray(
    agent_manager: Optional[AgentManager] = None, 
    config: Optional[Dict[str, Any]] = None
) -> Optional[MacOSTray]:
    """Create and configure the macOS system tray"""
    
    if not RUMPS_AVAILABLE:
        logger.error("Cannot create tray - rumps not available")
        return None

    try:
        tray = MacOSTray(agent_manager, config)
        logger.info("MacOS tray created successfully")
        return tray
    except Exception as e:
        logger.error(f"Failed to create MacOS tray: {e}")
        return None


def main():
    """Main entry point"""
    if not RUMPS_AVAILABLE:
        print("Error: rumps not available. Install with: pip install rumps")
        return
        
    tray = create_macos_tray()
    if tray:
        tray.run()
    else:
        print("Error: Failed to create tray application")
