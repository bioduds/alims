"""
DuckDuckGo Web Search for ALims AI

A simple and reliable web search implementation using DuckDuckGo's APIs.
No Docker or complex dependencies required.
"""

import asyncio
import aiohttp
import json
import re
import urllib.parse
from typing import Dict, List, Optional, Any
from datetime import datetime

from ..core.enhanced_logging import create_component_logger

logger = create_component_logger("duckduckgo_search")


class DuckDuckGoSearch:
    """
    Simple and reliable web search using DuckDuckGo APIs.
    """
    
    def __init__(self):
        self.timeout = 10
        self.max_results = 5
        self.user_agent = "ALims-AI/1.0 (Educational Research)"
        
    async def search_and_summarize(self, query: str, context: str = "") -> Dict[str, Any]:
        """
        Search using DuckDuckGo and return summarized results.
        
        Args:
            query: Search query
            context: Additional context for better results
            
        Returns:
            Dictionary with search results and summary
        """
        start_time = datetime.now()
        
        try:
            results = []
            
            # Method 1: DuckDuckGo Instant Answer API
            instant_results = await self._search_instant_answer(query)
            if instant_results:
                results.extend(instant_results)
                
            # Method 2: DuckDuckGo HTML scraping (fallback)
            if len(results) < 2:
                html_results = await self._search_html_scraping(query)
                if html_results:
                    results.extend(html_results)
            
            # Limit results
            results = results[:self.max_results]
            
            # Generate summary
            summary = self._generate_summary(results, query, context)
            
            # Prepare response
            response = {
                'results': results,
                'summary': summary,
                'query': query,
                'timestamp': datetime.now().isoformat(),
                'search_method': 'DuckDuckGo',
                'duration_seconds': (datetime.now() - start_time).total_seconds()
            }
            
            # Log the search activity
            logger.info(
                "DuckDuckGo search completed",
                {
                    "query": query,
                    "results_count": len(results),
                    "duration_seconds": response['duration_seconds']
                }
            )
            
            return response
            
        except Exception as e:
            logger.error(f"DuckDuckGo search failed: {e}")
            return {
                'results': [],
                'summary': f'Search failed: {str(e)}',
                'query': query,
                'search_method': 'DuckDuckGo',
                'error': str(e)
            }
    
    async def _search_instant_answer(self, query: str) -> List[Dict[str, Any]]:
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
                                'title': data.get('Heading', query.title()),
                                'url': data.get('AbstractURL', ''),
                                'content': data.get('Abstract', ''),
                                'source': 'DuckDuckGo Instant Answer'
                            })
                        
                        # Extract related topics
                        for topic in data.get('RelatedTopics', [])[:3]:
                            if isinstance(topic, dict) and topic.get('Text'):
                                results.append({
                                    'title': topic.get('Text', '')[:80] + '...',
                                    'url': topic.get('FirstURL', ''),
                                    'content': topic.get('Text', ''),
                                    'source': 'DuckDuckGo Related Topic'
                                })
                        
                        # Extract answer if available
                        if data.get('Answer'):
                            results.append({
                                'title': f"Answer: {query}",
                                'url': data.get('AnswerURL', ''),
                                'content': data.get('Answer', ''),
                                'source': 'DuckDuckGo Answer'
                            })
                        
                        return results
                        
        except Exception as e:
            logger.warning(f"DuckDuckGo Instant Answer search failed: {e}")
        return []
    
    async def _search_html_scraping(self, query: str) -> List[Dict[str, Any]]:
        """
        Fallback search using DuckDuckGo HTML (simplified).
        Note: This is a basic implementation for educational purposes.
        """
        try:
            # Simple search URL
            search_url = f"https://duckduckgo.com/html/?q={urllib.parse.quote(query)}"
            
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=self.timeout)) as session:
                async with session.get(
                    search_url,
                    headers={
                        'User-Agent': self.user_agent,
                        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8'
                    }
                ) as response:
                    if response.status == 200:
                        html = await response.text()
                        return self._parse_html_results(html, query)
                        
        except Exception as e:
            logger.warning(f"DuckDuckGo HTML search failed: {e}")
        return []
    
    def _parse_html_results(self, html: str, query: str) -> List[Dict[str, Any]]:
        """Parse HTML results from DuckDuckGo (basic implementation)."""
        results = []
        
        try:
            # Simple regex patterns to extract results
            # This is a basic implementation - in production you'd use proper HTML parsing
            title_pattern = r'<a[^>]*class="result__a"[^>]*href="([^"]*)"[^>]*>([^<]*)</a>'
            snippet_pattern = r'<a[^>]*class="result__snippet"[^>]*>([^<]*)</a>'
            
            titles = re.findall(title_pattern, html)
            snippets = re.findall(snippet_pattern, html)
            
            for i, (url, title) in enumerate(titles[:3]):
                snippet = snippets[i] if i < len(snippets) else ""
                
                # Clean up the data
                title = re.sub(r'<[^>]*>', '', title).strip()
                snippet = re.sub(r'<[^>]*>', '', snippet).strip()
                url = urllib.parse.unquote(url)
                
                if title and url:
                    results.append({
                        'title': title,
                        'url': url,
                        'content': snippet,
                        'source': 'DuckDuckGo Search'
                    })
                    
        except Exception as e:
            logger.warning(f"HTML parsing failed: {e}")
            
        return results
    
    def _generate_summary(self, results: List[Dict], query: str, context: str) -> str:
        """Generate a summary of search results for Gemma."""
        if not results:
            return f"No web search results found for '{query}'"
        
        summary_parts = [f"Web search results for '{query}' (via DuckDuckGo):"]
        
        for i, result in enumerate(results[:3], 1):
            title = result.get('title', 'Untitled')
            content = result.get('content', '')
            
            # Truncate long content
            if len(content) > 150:
                content = content[:150] + '...'
            
            summary_parts.append(f"\n{i}. {title}")
            if content:
                summary_parts.append(f"   {content}")
        
        summary_parts.append(f"\nFound {len(results)} relevant results.")
        
        if context:
            summary_parts.append(f"This information is relevant to: {context}")
        
        return '\n'.join(summary_parts)


class IntelligentWebSearch:
    """
    Main web search interface for ALims AI using DuckDuckGo.
    """
    
    def __init__(self):
        self.ddg_search = DuckDuckGoSearch()
        self.search_triggers = [
            "latest", "recent", "current", "today", "news", "update",
            "what is", "how to", "explain", "definition", "meaning",
            "compare", "difference", "vs", "versus", "between",
            "best", "top", "recommended", "popular", "trending",
            "research", "study", "analysis", "data", "statistics",
            "who is", "where is", "when is", "why", "which"
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
            r'\bwho\s+(?:is|are|was|were)\b',
            r'\bwhich\s+(?:is|are|was|were)\b'
        ]
        
        for pattern in question_patterns:
            if re.search(pattern, user_lower):
                return True
        
        return False
    
    async def search_and_summarize(self, query: str, context: str = "") -> Dict[str, Any]:
        """
        Main search interface using DuckDuckGo.
        
        Args:
            query: Search query
            context: Additional context
            
        Returns:
            Search results and summary
        """
        return await self.ddg_search.search_and_summarize(query, context)


# Global instance for use by other modules
web_search = IntelligentWebSearch()
