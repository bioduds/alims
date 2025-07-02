"""
Enhanced Web Search Integration for CelFlow AI

This module provides multiple web search capabilities including:
- SearXNG (primary when available)
- DuckDuckGo Instant Answer API
- Wikipedia API
- Direct search engine scraping (fallback)

Designed to provide Gemma with reliable web search regardless of external dependencies.
"""

import asyncio
import aiohttp
import json
import logging
import urllib.parse
from typing import Dict, List, Optional, Any, Union
from datetime import datetime
import re
import xml.etree.ElementTree as ET

from ..core.enhanced_logging import create_component_logger

logger = create_component_logger("web_search")


class MultiSourceWebSearch:
    """
    Enhanced web search with multiple fallback sources.
    Ensures Gemma always has access to web information.
    """
    
    def __init__(self):
        self.searxng_url = "http://localhost:8080"
        self.timeout = 10
        self.max_results = 5
        self.user_agent = "CelFlow-AI/1.0 (Educational Research)"
        
    async def search_and_summarize(self, query: str, context: str = "") -> Dict[str, Any]:
        """
        Comprehensive web search with multiple fallback sources.
        
        Args:
            query: Search query
            context: Additional context for better results
            
        Returns:
            Dictionary with search results and summary
        """
        start_time = datetime.now()
        search_methods = []
        
        try:
            # Try search methods in order of preference
            results = None
            
            # Method 1: SearXNG (if available)
            if await self._is_searxng_available():
                results = await self._search_searxng(query)
                search_methods.append("SearXNG")
                
            # Method 2: DuckDuckGo Instant Answer API
            if not results or len(results.get('results', [])) < 2:
                ddg_results = await self._search_duckduckgo(query)
                if ddg_results:
                    if results:
                        results['results'].extend(ddg_results['results'])
                    else:
                        results = ddg_results
                    search_methods.append("DuckDuckGo")
                    
            # Method 3: Wikipedia API
            if not results or len(results.get('results', [])) < 3:
                wiki_results = await self._search_wikipedia(query)
                if wiki_results:
                    if results:
                        results['results'].extend(wiki_results['results'])
                    else:
                        results = wiki_results
                    search_methods.append("Wikipedia")
                    
            if not results:
                results = {'results': [], 'summary': 'No search results found'}
                
            # Limit results and add metadata
            results['results'] = results['results'][:self.max_results]
            results['search_methods'] = search_methods
            results['query'] = query
            results['timestamp'] = datetime.now().isoformat()
            
            # Generate summary
            summary = self._generate_summary(results['results'], query, context)
            results['summary'] = summary
            
            # Log the search activity
            logger.info(
                "Web search completed",
                {
                    "query": query,
                    "methods_used": search_methods,
                    "results_count": len(results['results']),
                    "duration_seconds": (datetime.now() - start_time).total_seconds()
                }
            )
            
            return results
            
        except Exception as e:
            logger.error(f"Web search failed: {e}")
            return {
                'results': [],
                'summary': f'Search failed: {str(e)}',
                'query': query,
                'search_methods': search_methods,
                'error': str(e)
            }
    
    async def _is_searxng_available(self) -> bool:
        """Check if SearXNG is available."""
        try:
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=3)) as session:
                async with session.get(f"{self.searxng_url}/search") as response:
                    return response.status == 200
        except:
            return False
    
    async def _search_searxng(self, query: str) -> Optional[Dict[str, Any]]:
        """Search using SearXNG."""
        try:
            params = {
                'q': query,
                'format': 'json',
                'categories': 'general',
                'time_range': '',
                'pageno': 1
            }
            
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=self.timeout)) as session:
                async with session.get(
                    f"{self.searxng_url}/search",
                    params=params,
                    headers={'User-Agent': self.user_agent}
                ) as response:
                    if response.status == 200:
                        data = await response.json()
                        results = []
                        
                        for item in data.get('results', [])[:self.max_results]:
                            results.append({
                                'title': item.get('title', ''),
                                'url': item.get('url', ''),
                                'content': item.get('content', ''),
                                'source': 'SearXNG'
                            })
                        
                        return {'results': results}
        except Exception as e:
            logger.warning(f"SearXNG search failed: {e}")
        return None
    
    async def _search_duckduckgo(self, query: str) -> Optional[Dict[str, Any]]:
        """Search using DuckDuckGo Instant Answer API."""
        try:
            params = {
                'q': query,
                'format': 'json',
                'no_html': '1',
                'skip_disambig': '1'
            }
            
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=self.timeout)) as session:
                async with session.get(
                    'https://api.duckduckgo.com/',
                    params=params,
                    headers={'User-Agent': self.user_agent}
                ) as response:
                    if response.status == 200:
                        data = await response.json()
                        results = []
                        
                        # Extract instant answer
                        if data.get('Abstract'):
                            results.append({
                                'title': data.get('Heading', query),
                                'url': data.get('AbstractURL', ''),
                                'content': data.get('Abstract', ''),
                                'source': 'DuckDuckGo (Instant Answer)'
                            })
                        
                        # Extract related topics
                        for topic in data.get('RelatedTopics', [])[:3]:
                            if isinstance(topic, dict) and topic.get('Text'):
                                results.append({
                                    'title': topic.get('Text', '')[:100] + '...',
                                    'url': topic.get('FirstURL', ''),
                                    'content': topic.get('Text', ''),
                                    'source': 'DuckDuckGo (Related)'
                                })
                        
                        if results:
                            return {'results': results}
                            
        except Exception as e:
            logger.warning(f"DuckDuckGo search failed: {e}")
        return None
    
    async def _search_wikipedia(self, query: str) -> Optional[Dict[str, Any]]:
        """Search using Wikipedia API."""
        try:
            # First, search for articles
            search_params = {
                'action': 'query',
                'format': 'json',
                'list': 'search',
                'srsearch': query,
                'srlimit': 3
            }
            
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=self.timeout)) as session:
                async with session.get(
                    'https://en.wikipedia.org/api/rest_v1/page/summary/' + urllib.parse.quote(query),
                    headers={'User-Agent': self.user_agent}
                ) as response:
                    if response.status == 200:
                        data = await response.json()
                        
                        if data.get('extract'):
                            return {
                                'results': [{
                                    'title': data.get('title', query),
                                    'url': data.get('content_urls', {}).get('desktop', {}).get('page', ''),
                                    'content': data.get('extract', ''),
                                    'source': 'Wikipedia'
                                }]
                            }
                            
        except Exception as e:
            logger.warning(f"Wikipedia search failed: {e}")
        return None
    
    def _generate_summary(self, results: List[Dict], query: str, context: str) -> str:
        """Generate a summary of search results for Gemma."""
        if not results:
            return f"No web search results found for '{query}'"
        
        summary_parts = [f"Web search results for '{query}':"]
        
        for i, result in enumerate(results[:3], 1):
            title = result.get('title', 'Untitled')
            content = result.get('content', '')[:200] + '...' if len(result.get('content', '')) > 200 else result.get('content', '')
            source = result.get('source', 'Unknown')
            
            summary_parts.append(f"\n{i}. {title} ({source})")
            if content:
                summary_parts.append(f"   {content}")
        
        summary_parts.append(f"\nFound {len(results)} relevant results from web search.")
        
        if context:
            summary_parts.append(f"This information may be relevant to: {context}")
        
        return '\n'.join(summary_parts)


class IntelligentWebSearch:
    """
    Main web search interface for CelFlow AI.
    Maintains compatibility with existing code while using enhanced search.
    """
    
    def __init__(self):
        self.multi_search = MultiSourceWebSearch()
        self.search_triggers = [
            "latest", "recent", "current", "today", "news", "update",
            "what is", "how to", "explain", "definition", "meaning",
            "compare", "difference", "vs", "versus", "between",
            "best", "top", "recommended", "popular", "trending",
            "research", "study", "analysis", "data", "statistics"
        ]
    
    def should_search_web(self, user_input: str, context: str = "") -> bool:
        """
        Determine if web search should be triggered based on user input.
        
        Args:
            user_input: User's query or request
            context: Additional context
            
        Returns:
            True if web search should be performed
        """
        user_lower = user_input.lower()
        
        # Check for explicit search triggers
        for trigger in self.search_triggers:
            if trigger in user_lower:
                return True
        
        # Check for question patterns
        question_patterns = [
            r'\bwhat\s+(?:is|are|was|were)\b',
            r'\bhow\s+(?:to|do|does|did)\b',
            r'\bwhen\s+(?:is|are|was|were|did|do)\b',
            r'\bwhere\s+(?:is|are|was|were|can|could)\b',
            r'\bwhy\s+(?:is|are|was|were|do|does|did)\b',
            r'\bwhich\s+(?:is|are|was|were)\b'
        ]
        
        for pattern in question_patterns:
            if re.search(pattern, user_lower):
                return True
        
        return False
    
    async def search_and_summarize(self, query: str, context: str = "") -> Dict[str, Any]:
        """
        Main search interface - delegates to MultiSourceWebSearch.
        
        Args:
            query: Search query
            context: Additional context
            
        Returns:
            Search results and summary
        """
        return await self.multi_search.search_and_summarize(query, context)


# Global instance for use by other modules
web_search = IntelligentWebSearch()
