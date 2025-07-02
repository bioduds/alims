#!/usr/bin/env python3
"""
ALims System Tray Icon

macOS system tray integration with evolving menu that shows the status
of the embryo pool and agent ecosystem as it develops.
"""

import asyncio
import logging
from typing import Optional, Dict, Any
from PyQt6.QtWidgets import (QSystemTrayIcon, QMenu, QApplication, 
                           QAction, QWidget, QVBoxLayout, QLabel, 
                           QProgressBar, QDialog)
from PyQt6.QtCore import QTimer, pyqtSignal, QThread
from PyQt6.QtGui import QIcon, QPixmap, QFont


class EmbryoStatusDialog(QDialog):
    """Dialog showing detailed embryo pool status"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("ALims - Embryo Pool Status")
        self.setFixedSize(400, 300)
        self.setup_ui()

    def setup_ui(self):
        """Setup the status dialog UI"""
        layout = QVBoxLayout()

        # Title
        title = QLabel("🧬 ALims Learning Status")
        title_font = QFont()
        title_font.setPointSize(14)
        title_font.setBold(True)
        title.setFont(title_font)
        layout.addWidget(title)

        # Status labels
        self.status_label = QLabel("Initializing...")
        self.embryo_count_label = QLabel("Active Embryos: 0")
        self.patterns_label = QLabel("Patterns Detected: 0")
        self.specialization_label = QLabel("Specializations: None")
        self.birth_queue_label = QLabel("Birth Queue: 0")

        # Progress bar
        self.learning_progress = QProgressBar()
        self.learning_progress.setMaximum(100)
        self.learning_progress.setValue(0)

        layout.addWidget(self.status_label)
        layout.addWidget(self.embryo_count_label)
        layout.addWidget(self.patterns_label)
        layout.addWidget(QLabel("Learning Progress:"))
        layout.addWidget(self.learning_progress)
        layout.addWidget(self.specialization_label)
        layout.addWidget(self.birth_queue_label)

        self.setLayout(layout)

    def update_status(self, pool_status: Dict[str, Any]):
        """Update the dialog with current pool status"""
        try:
            active_embryos = pool_status.get('active_embryos', 0)
            patterns_detected = pool_status.get('pool_stats', {}).get('patterns_detected', 0)
            birth_queue = pool_status.get('birth_queue_size', 0)
            specializations = pool_status.get('top_specializations', {})

            # Update labels
            self.embryo_count_label.setText(f"Active Embryos: {active_embryos}")
            self.patterns_label.setText(f"Patterns Detected: {patterns_detected}")
            self.birth_queue_label.setText(f"Birth Queue: {birth_queue}")

            # Update progress (based on patterns detected)
            progress = min(patterns_detected // 10, 100)
            self.learning_progress.setValue(progress)

            # Update specializations
            if specializations:
                spec_text = ", ".join([f"{k}: {v}" for k, v in specializations.items()])
                self.specialization_label.setText(f"Specializations: {spec_text}")
            else:
                self.specialization_label.setText("Specializations: Developing...")

            # Update main status
            if birth_queue > 0:
                self.status_label.setText("🎯 Agent ready for birth!")
            elif patterns_detected > 50:
                self.status_label.setText("🧠 Learning patterns actively")
            elif active_embryos > 0:
                self.status_label.setText("👁️ Observing silently...")
            else:
                self.status_label.setText("💤 Waiting to start...")

        except Exception as e:
            self.status_label.setText(f"Error: {e}")


class AlimsTrayIcon(QSystemTrayIcon):
    """
    ALIMS System Tray Icon with comprehensive system integration.

    Provides:
    - Real-time system status
    - Agent management controls
    - Quick access to system functions
    - Visual feedback and notifications
    """

    # Signals
    show_status_requested = pyqtSignal()
    toggle_learning_requested = pyqtSignal()
    open_settings_requested = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.logger = logging.getLogger('TrayIcon')

        # Current system state
        self.current_phase = 0  # 0=silent, 1=hints, 2=assistant, 3=integrated
        self.pool_status = {}
        self.learning_enabled = True

        # UI components
        self.status_dialog = None

        # Setup icon and menu
        self.setup_icon()
        self.setup_menu()

        # Update timer
        self.update_timer = QTimer()
        self.update_timer.timeout.connect(self.update_display)
        self.update_timer.start(5000)  # Update every 5 seconds

    def setup_icon(self):
        """Setup the system tray icon"""
        # Create a simple colored circle icon
        # In a real implementation, you'd load actual icon files
        pixmap = QPixmap(32, 32)
        pixmap.fill()  # Creates a colored icon
        icon = QIcon(pixmap)
        self.setIcon(icon)

        # Set tooltip
        self.setToolTip("ALims - Learning your patterns")

        # Handle clicks
        self.activated.connect(self.handle_activation)

    def setup_menu(self):
        """Setup the context menu (evolves based on phase)"""
        self.menu = QMenu()
        self.update_menu_for_phase()
        self.setContextMenu(self.menu)

    def update_menu_for_phase(self):
        """Update menu items based on current learning phase"""
        self.menu.clear()

        if self.current_phase == 0:  # Silent observation phase
            self.menu.addAction("👁️ Observing silently...", self.show_status)
            self.menu.addSeparator()
            self.menu.addAction("📊 View Learning Status", self.show_detailed_status)
            self.menu.addAction("⚙️ Settings", self.open_settings)
            self.menu.addSeparator()
            self.menu.addAction("⏸️ Pause Learning", self.toggle_learning)
            self.menu.addAction("❌ Quit ALims", self.quit_application)

        elif self.current_phase == 1:  # Gentle hints phase
            self.menu.addAction("💡 Learning your patterns", self.show_status)
            self.menu.addSeparator()
            self.menu.addAction("🧬 View Embryo Status", self.show_detailed_status)
            self.menu.addAction("🎯 Agents Ready", self.show_birth_queue)
            self.menu.addAction("⚙️ Settings", self.open_settings)
            self.menu.addSeparator()
            self.menu.addAction("⏸️ Pause Learning", self.toggle_learning)
            self.menu.addAction("❌ Quit ALims", self.quit_application)

        elif self.current_phase >= 2:  # Active assistant phase
            self.menu.addAction("🤖 Active Agents", self.show_agent_status)
            self.menu.addSeparator()
            self.menu.addAction("💬 Talk to Agent", self.open_voice_interface)
            self.menu.addAction("🧬 Embryo Pool", self.show_detailed_status)
            self.menu.addAction("📊 Performance", self.show_performance)
            self.menu.addAction("⚙️ Settings", self.open_settings)
            self.menu.addSeparator()
            self.menu.addAction("⏸️ Pause System", self.toggle_learning)
            self.menu.addAction("❌ Quit ALims", self.quit_application)

    def handle_activation(self, reason):
        """Handle tray icon activation"""
        if reason == QSystemTrayIcon.ActivationReason.DoubleClick:
            self.show_detailed_status()
        elif reason == QSystemTrayIcon.ActivationReason.Trigger:
            # Single click - show quick status
            self.show_quick_status()

    def show_quick_status(self):
        """Show quick status tooltip or notification"""
        if self.pool_status:
            active_embryos = self.pool_status.get('active_embryos', 0)
            patterns = self.pool_status.get('pool_stats', {}).get('patterns_detected', 0)
            birth_queue = self.pool_status.get('birth_queue_size', 0)

            if birth_queue > 0:
                message = f"🎯 {birth_queue} agent(s) ready for birth!"
            elif patterns > 0:
                message = f"🧠 Learning actively - {patterns} patterns found"
            else:
                message = f"👁️ {active_embryos} embryos observing..."

            self.showMessage("ALims Status", message, 
                           QSystemTrayIcon.MessageIcon.Information, 3000)

    def show_detailed_status(self):
        """Show detailed status dialog"""
        if not self.status_dialog:
            self.status_dialog = EmbryoStatusDialog()

        if self.pool_status:
            self.status_dialog.update_status(self.pool_status)

        self.status_dialog.show()
        self.status_dialog.raise_()
        self.status_dialog.activateWindow()

    def show_status(self):
        """Emit signal to show main status"""
        self.show_status_requested.emit()

    def show_birth_queue(self):
        """Show agents ready for birth"""
        birth_queue = self.pool_status.get('birth_queue_size', 0)
        if birth_queue > 0:
            self.showMessage("Agent Birth Ready", 
                           f"{birth_queue} embryo(s) ready to become specialized agents!",
                           QSystemTrayIcon.MessageIcon.Information, 5000)
        else:
            self.showMessage("No Births Ready", 
                           "No embryos are ready for agent birth yet.",
                           QSystemTrayIcon.MessageIcon.Information, 3000)

    def show_agent_status(self):
        """Show active agent status (phase 2+)"""
        # This would show actual agent status in later phases
        self.showMessage("Active Agents", 
                       "Agent status will be shown here once agents are born.",
                       QSystemTrayIcon.MessageIcon.Information, 3000)

    def open_voice_interface(self):
        """Open voice interface (phase 2+)"""
        # This would open the voice interface in later phases
        self.showMessage("Voice Interface", 
                       "Voice interface will be available after first agent birth.",
                       QSystemTrayIcon.MessageIcon.Information, 3000)

    def show_performance(self):
        """Show performance metrics"""
        # This would show detailed performance metrics
        self.showMessage("Performance", 
                       "Performance metrics coming soon.",
                       QSystemTrayIcon.MessageIcon.Information, 3000)

    def open_settings(self):
        """Open settings dialog"""
        self.open_settings_requested.emit()

    def toggle_learning(self):
        """Toggle learning on/off"""
        self.learning_enabled = not self.learning_enabled
        self.toggle_learning_requested.emit()

        status = "resumed" if self.learning_enabled else "paused"
        self.showMessage("Learning Status", 
                       f"Learning has been {status}.",
                       QSystemTrayIcon.MessageIcon.Information, 2000)

    def quit_application(self):
        """Quit the application"""
        QApplication.quit()

    def update_display(self):
        """Update display elements periodically"""
        # Update tooltip based on current status
        if self.pool_status:
            active_embryos = self.pool_status.get('active_embryos', 0)
            patterns = self.pool_status.get('pool_stats', {}).get('patterns_detected', 0)

            if self.current_phase == 0:
                tooltip = f"ALims - Observing ({active_embryos} embryos, {patterns} patterns)"
            elif self.current_phase == 1:
                tooltip = f"ALims - Learning patterns ({patterns} detected)"
            else:
                tooltip = f"ALims - Active ({active_embryos} embryos active)"

            self.setToolTip(tooltip)

    def update_pool_status(self, status: Dict[str, Any]):
        """Update with latest pool status"""
        self.pool_status = status

        # Check if we should advance to next phase
        birth_queue = status.get('birth_queue_size', 0)
        if birth_queue > 0 and self.current_phase == 0:
            self.advance_to_phase(1)

    def advance_to_phase(self, new_phase: int):
        """Advance to the next learning phase"""
        if new_phase > self.current_phase:
            self.current_phase = new_phase
            self.update_menu_for_phase()

            phase_names = {
                1: "Pattern Recognition",
                2: "Active Assistant",
                3: "Integrated Intelligence"
            }

            phase_name = phase_names.get(new_phase, f"Phase {new_phase}")
            self.showMessage("ALims Evolution", 
                           f"Advancing to {phase_name} phase!",
                           QSystemTrayIcon.MessageIcon.Information, 5000)

    def show_agent_birth_notification(self, agent_info: Dict[str, Any]):
        """Show notification when a new agent is born"""
        agent_type = agent_info.get('specialization', 'Unknown')
        agent_name = agent_info.get('name', 'New Agent')

        self.showMessage("🎉 Agent Born!", 
                       f"{agent_name} ({agent_type}) is ready to help!",
                       QSystemTrayIcon.MessageIcon.Information, 8000)

        # Advance phase if this is first agent
        if self.current_phase < 2:
            self.advance_to_phase(2) 
