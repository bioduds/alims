#!/usr/bin/env python3
"""
ALims Permission Manager

Handles macOS permission requests for system monitoring.
"""

import asyncio
import logging
import subprocess
import os
from typing import Dict, List, Optional


class PermissionManager:
    """
    Simple permission manager for macOS system access.
    In a real implementation, this would use macOS APIs.
    """

    def __init__(self):
        self.logger = logging.getLogger('PermissionManager')

    async def check_all_permissions(self) -> bool:
        """Check if all required permissions are granted"""
        self.logger.info("Checking system permissions...")

        # For this demo, we'll assume permissions are granted
        # In a real implementation, this would check:
        # - Accessibility permissions
        # - Screen recording permissions
        # - File system access

        return True


def check_system_permissions() -> Dict[str, bool]:
    """
    Check current system permissions status

    Returns:
        Dict with permission status for each required permission
    """
    logger = logging.getLogger("PermissionChecker")

    permissions = {
        "accessibility": False,
        "full_disk_access": False,
        "screen_recording": False,
        "automation": False,
    }

    try:
        # Check accessibility permissions
        permissions["accessibility"] = _check_accessibility_permission()

        # Check full disk access (simplified check)
        permissions["full_disk_access"] = _check_full_disk_access()

        # Check screen recording permissions
        permissions["screen_recording"] = _check_screen_recording_permission()

        # Check automation permissions
        permissions["automation"] = _check_automation_permission()

        logger.info(f"Permission status: {permissions}")

    except Exception as e:
        logger.error(f"Error checking permissions: {e}")

    return permissions


def _check_accessibility_permission() -> bool:
    """Check if accessibility permission is granted"""
    try:
        # Try to use AppleScript to check accessibility
        script = """
        tell application "System Events"
            return true
        end tell
        """

        result = subprocess.run(
            ["osascript", "-e", script], capture_output=True, text=True, timeout=5
        )

        return result.returncode == 0

    except Exception:
        return False


def _check_full_disk_access() -> bool:
    """Check if full disk access is granted"""
    try:
        # Try to access a protected directory
        protected_paths = [
            os.path.expanduser("~/Library/Mail"),
            os.path.expanduser("~/Library/Safari"),
            "/Library/Application Support",
        ]

        for path in protected_paths:
            if os.path.exists(path):
                try:
                    os.listdir(path)
                    return True
                except PermissionError:
                    continue

        return False

    except Exception:
        return False


def _check_screen_recording_permission() -> bool:
    """Check if screen recording permission is granted"""
    try:
        # This is a simplified check
        # In a real implementation, would use CGDisplayStream or similar
        return True  # Assume granted for demo

    except Exception:
        return False


def _check_automation_permission() -> bool:
    """Check if automation permission is granted"""
    try:
        # Try to get information about running applications
        script = """
        tell application "System Events"
            get name of every application process
        end tell
        """

        result = subprocess.run(
            ["osascript", "-e", script], capture_output=True, text=True, timeout=5
        )

        return result.returncode == 0

    except Exception:
        return False


async def request_permissions(missing_permissions: List[str]) -> bool:
    """
    Request missing system permissions from user

    Args:
        missing_permissions: List of permission names that are missing

    Returns:
        True if permissions were granted, False otherwise
    """
    logger = logging.getLogger("PermissionRequester")

    if not missing_permissions:
        return True

    logger.info(f"Requesting permissions: {missing_permissions}")

    try:
        # Show permission request dialog
        permission_messages = {
            "accessibility": "ALims needs Accessibility permission to monitor system events.",
            "full_disk_access": "ALims needs Full Disk Access to monitor file operations.",
            "screen_recording": "ALims needs Screen Recording permission for advanced monitoring.",
            "automation": "ALims needs Automation permission to interact with applications.",
        }

        for permission in missing_permissions:
            message = permission_messages.get(
                permission, f"ALims needs {permission} permission."
            )

            # Show dialog using AppleScript
            script = f"""
            display dialog "{message}

Please grant this permission in System Preferences > Security & Privacy > Privacy > {permission.replace('_', ' ').title()}.

Would you like to open System Preferences now?" buttons {{"Cancel", "Open System Preferences"}} default button "Open System Preferences"
            """

            try:
                result = subprocess.run(
                    ["osascript", "-e", script],
                    capture_output=True,
                    text=True,
                    timeout=30,
                )

                if (
                    result.returncode == 0
                    and "Open System Preferences" in result.stdout
                ):
                    # Open System Preferences
                    subprocess.run(
                        [
                            "open",
                            "x-apple.systempreferences:com.apple.preference.security?Privacy",
                        ]
                    )

                    # Wait for user to grant permission
                    await _wait_for_permission_grant(permission)

            except subprocess.TimeoutExpired:
                logger.warning(f"Permission request dialog timed out for {permission}")
                return False
            except Exception as e:
                logger.error(f"Error showing permission dialog for {permission}: {e}")
                return False

        # Check if permissions were granted
        final_permissions = check_system_permissions()
        granted = all(
            final_permissions.get(perm, False) for perm in missing_permissions
        )

        if granted:
            logger.info("✅ All requested permissions granted")
        else:
            logger.warning("❌ Some permissions were not granted")

        return granted

    except Exception as e:
        logger.error(f"Error requesting permissions: {e}")
        return False


async def _wait_for_permission_grant(permission: str, max_wait: int = 60) -> bool:
    """
    Wait for user to grant a specific permission

    Args:
        permission: Permission name to wait for
        max_wait: Maximum time to wait in seconds

    Returns:
        True if permission was granted within timeout
    """
    logger = logging.getLogger("PermissionWaiter")

    logger.info(f"Waiting for {permission} permission to be granted...")

    for i in range(max_wait):
        await asyncio.sleep(1)

        permissions = check_system_permissions()
        if permissions.get(permission, False):
            logger.info(f"✅ {permission} permission granted")
            return True

        if i % 10 == 0:  # Log every 10 seconds
            logger.info(
                f"Still waiting for {permission} permission... ({i}/{max_wait}s)"
            )

    logger.warning(f"❌ Timeout waiting for {permission} permission")
    return False


def get_permission_instructions() -> Dict[str, str]:
    """
    Get instructions for manually granting permissions

    Returns:
        Dict mapping permission names to instruction strings
    """
    return {
        "accessibility": """
To grant Accessibility permission:
1. Open System Preferences > Security & Privacy > Privacy
2. Click on "Accessibility" in the left sidebar
3. Click the lock icon and enter your password
4. Find ALims in the list and check the box next to it
5. If ALims is not in the list, click the "+" button and add it
        """.strip(),
        "full_disk_access": """
To grant Full Disk Access permission:
1. Open System Preferences > Security & Privacy > Privacy
2. Click on "Full Disk Access" in the left sidebar
3. Click the lock icon and enter your password
4. Find ALims in the list and check the box next to it
5. If ALims is not in the list, click the "+" button and add it
        """.strip(),
        "screen_recording": """
To grant Screen Recording permission:
1. Open System Preferences > Security & Privacy > Privacy
2. Click on "Screen Recording" in the left sidebar
3. Click the lock icon and enter your password
4. Find ALims in the list and check the box next to it
5. If ALims is not in the list, click the "+" button and add it
        """.strip(),
        "automation": """
To grant Automation permission:
1. Open System Preferences > Security & Privacy > Privacy
2. Click on "Automation" in the left sidebar
3. Find ALims in the list and expand it
4. Check the boxes for applications you want ALims to control
        """.strip(),
    }
