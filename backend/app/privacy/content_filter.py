#!/usr/bin/env python3
"""
ALims Content Filter

Privacy-first content filtering system that removes sensitive information
from system events before they reach the embryos.
"""

import re
import asyncio
import logging
from typing import Dict, List, Optional, Any, Set
import hashlib


class ContentFilter:
    """
    Privacy-focused content filter that removes sensitive information
    from system events before pattern detection.
    """
    
    def __init__(self, config: dict):
        self.config = config
        self.logger = logging.getLogger('ContentFilter')
        
        # Sensitive patterns to filter
        self._init_filter_patterns()
        
        # Sensitive applications to avoid
        self.sensitive_apps = set(config.get('filter_sensitive_apps', [
            'Banking', 'Password Manager', 'VPN', 'KeyChain Access',
            'Wallet', 'Crypto', 'Finance'
        ]))
        
        # Content filtering settings
        self.filter_passwords = config.get('filter_passwords', True)
        self.filter_credit_cards = config.get('filter_credit_cards', True)
        self.filter_personal_info = config.get('filter_personal_info', True)
        
    def _init_filter_patterns(self):
        """Initialize regex patterns for sensitive content detection"""
        self.sensitive_patterns = {
            # Credit card numbers
            'credit_card': [
                re.compile(r'\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b'),
                re.compile(r'\b\d{13,19}\b')  # General card number format
            ],
            
            # Email addresses
            'email': [
                re.compile(r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b')
            ],
            
            # Phone numbers
            'phone': [
                re.compile(r'\b\d{3}[-.]?\d{3}[-.]?\d{4}\b'),
                re.compile(r'\(\d{3}\)\s?\d{3}[-.]?\d{4}'),
                re.compile(r'\+\d{1,3}[-.\s]?\d{1,14}')
            ],
            
            # Social Security Numbers (US)
            'ssn': [
                re.compile(r'\b\d{3}-\d{2}-\d{4}\b'),
                re.compile(r'\b\d{9}\b')
            ],
            
            # Common password indicators
            'password': [
                re.compile(r'password[:=]\s*\S+', re.IGNORECASE),
                re.compile(r'pass[:=]\s*\S+', re.IGNORECASE),
                re.compile(r'pwd[:=]\s*\S+', re.IGNORECASE),
                re.compile(r'token[:=]\s*\S+', re.IGNORECASE),
                re.compile(r'key[:=]\s*\S+', re.IGNORECASE)
            ],
            
            # IP addresses
            'ip_address': [
                re.compile(r'\b\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\b')
            ],
            
            # API keys and tokens
            'api_key': [
                re.compile(r'[A-Za-z0-9]{32,}'),  # Long alphanumeric strings
                re.compile(r'sk_[A-Za-z0-9]{24,}'),  # Stripe-style keys
                re.compile(r'pk_[A-Za-z0-9]{24,}')   # Public keys
            ]
        }
        
    async def filter_event(self, event_data: dict) -> Optional[dict]:
        """
        Filter sensitive content from system event.
        Returns filtered event or None if event should be blocked.
        """
        try:
            # Check if app is sensitive
            app_name = event_data.get('app_name', '')
            if self._is_sensitive_app(app_name):
                self.logger.debug(f"Blocking event from sensitive app: {app_name}")
                return None
                
            # Create filtered copy
            filtered_event = self._deep_copy_dict(event_data)
            
            # Filter text content
            if 'text_content' in filtered_event:
                filtered_event['text_content'] = await self._filter_text(
                    filtered_event['text_content']
                )
                
            # Filter window title
            if 'window_title' in filtered_event:
                filtered_event['window_title'] = await self._filter_text(
                    filtered_event['window_title']
                )
                
            # Filter file paths (remove personal directories)
            if 'file_path' in filtered_event:
                filtered_event['file_path'] = self._anonymize_file_path(
                    filtered_event['file_path']
                )
                
            # Remove or hash sensitive fields
            sensitive_fields = ['user_name', 'real_name', 'email', 'device_id']
            for field in sensitive_fields:
                if field in filtered_event:
                    if self.filter_personal_info:
                        filtered_event[field] = self._hash_sensitive_data(
                            str(filtered_event[field])
                        )
                        
            return filtered_event
            
        except Exception as e:
            self.logger.error(f"Error filtering event: {e}")
            return None
            
    def _is_sensitive_app(self, app_name: str) -> bool:
        """Check if application is marked as sensitive"""
        app_lower = app_name.lower()
        return any(sensitive.lower() in app_lower 
                  for sensitive in self.sensitive_apps)
                  
    async def _filter_text(self, text: str) -> str:
        """Filter sensitive patterns from text content"""
        if not text or not isinstance(text, str):
            return text
            
        filtered_text = text
        
        # Apply each filter pattern
        for category, patterns in self.sensitive_patterns.items():
            if self._should_filter_category(category):
                for pattern in patterns:
                    filtered_text = pattern.sub('[FILTERED]', filtered_text)
                    
        return filtered_text
        
    def _should_filter_category(self, category: str) -> bool:
        """Check if a category should be filtered based on config"""
        category_settings = {
            'password': self.filter_passwords,
            'credit_card': self.filter_credit_cards,
            'email': self.filter_personal_info,
            'phone': self.filter_personal_info,
            'ssn': self.filter_personal_info,
            'ip_address': self.filter_personal_info,
            'api_key': self.filter_passwords
        }
        
        return category_settings.get(category, True)
        
    def _anonymize_file_path(self, file_path: str) -> str:
        """Anonymize file paths to remove personal information"""
        if not file_path:
            return file_path
            
        # Replace user home directory
        if file_path.startswith('/Users/'):
            parts = file_path.split('/')
            if len(parts) > 2:
                parts[2] = '[USER]'
                return '/'.join(parts)
                
        # Replace common personal directories
        personal_dirs = {
            'Desktop': '[DESKTOP]',
            'Documents': '[DOCS]',
            'Downloads': '[DOWNLOADS]',
            'Pictures': '[PICS]',
            'Movies': '[MOVIES]',
            'Music': '[MUSIC]'
        }
        
        for personal, replacement in personal_dirs.items():
            file_path = file_path.replace(f'/{personal}/', f'/{replacement}/')
            
        return file_path
        
    def _hash_sensitive_data(self, data: str) -> str:
        """Create a consistent hash of sensitive data for anonymization"""
        return hashlib.sha256(data.encode()).hexdigest()[:8]
        
    def _deep_copy_dict(self, original: dict) -> dict:
        """Create a deep copy of a dictionary"""
        result = {}
        for key, value in original.items():
            if isinstance(value, dict):
                result[key] = self._deep_copy_dict(value)
            elif isinstance(value, list):
                result[key] = [item for item in value]
            else:
                result[key] = value
        return result
        
    def add_sensitive_app(self, app_name: str):
        """Add an application to the sensitive apps list"""
        self.sensitive_apps.add(app_name)
        self.logger.info(f"Added {app_name} to sensitive apps list")
        
    def remove_sensitive_app(self, app_name: str):
        """Remove an application from the sensitive apps list"""
        self.sensitive_apps.discard(app_name)
        self.logger.info(f"Removed {app_name} from sensitive apps list")
        
    def get_filter_stats(self) -> Dict[str, int]:
        """Get statistics about filtering activity"""
        # This would track filtering statistics in a real implementation
        return {
            'events_filtered': 0,
            'sensitive_apps_blocked': 0,
            'patterns_filtered': 0
        } 