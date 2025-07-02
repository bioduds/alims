"""
Web Search Integration using SearXNG for CelFlow AI

This module provides intelligent web search capabilities for Gemma to access
real-time information when making decisions about analysis and visualizations.
"""

import asyncio
import aiohttp
import json
import logging
from typing import Dict, List, Optional, Any
from urllib.parse import urlencode, urlparse, quote_plus
import re
from datetime import datetime

logger = logging.getLogger(__name__)


class SearXNGClient:
    """Client for SearXNG web search engine."""
    
    def __init__(self, base_url: str = "http://localhost:8080"):
        """
        Initialize SearXNG client.
        
        Args:
            base_url: Base URL of SearXNG instance
        """
        self.base_url = base_url.rstrip('/')
        self.session = None
        self.categories = [
            'general', 'news', 'science', 'it', 'files', 'images'
        ]
        self.engines = [
            'google', 'bing', 'duckduckgo', 'startpage', 'wikipedia'
        ]
        
    async def __aenter__(self):
        """Async context manager entry."""
        self.session = aiohttp.ClientSession(
            timeout=aiohttp.ClientTimeout(total=30),
            headers={
                'User-Agent': 'CelFlow-AI/1.0 (Intelligence Agent)',
                'Accept': 'application/json'
            }
        )
        return self
        
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        if self.session:
            await self.session.close()
    
    async def health_check(self) -> bool:
        """Check if SearXNG instance is healthy."""
        try:
            async with self.session.get(f"{self.base_url}/") as response:
                return response.status == 200
        except Exception as e:
            logger.warning(f"SearXNG health check failed: {e}")
            return False
    
    async def search(
        self,
        query: str,
        category: str = "general",
        engines: Optional[List[str]] = None,
        format: str = "json",
        lang: str = "en",
        safesearch: int = 1,
        pageno: int = 1
    ) -> Dict[str, Any]:
        """
        Perform search query.
        
        Args:
            query: Search query
            category: Search category (general, news, science, etc.)
            engines: Specific engines to use
            format: Response format (json, html, csv, rss)
            lang: Language code
            safesearch: Safe search level (0=off, 1=moderate, 2=strict)
            pageno: Page number
            
        Returns:
            Search results dictionary
        """
        if not self.session:
            raise RuntimeError("SearXNG client not initialized")
            
        params = {
            'q': query,
            'category': category,
            'format': format,
            'lang': lang,
            'safesearch': safesearch,
            'pageno': pageno
        }
        
        if engines:
            params['engines'] = ','.join(engines)
            
        try:
            search_url = f"{self.base_url}/search"
            async with self.session.get(search_url, params=params) as response:
                if response.status == 200:
                    if format == 'json':
                        return await response.json()
                    else:
                        return {'raw': await response.text()}
                else:
                    logger.error(f"Search failed with status {response.status}")
                    return {'error': f'HTTP {response.status}'}
                    
        except Exception as e:
            logger.error(f"Search request failed: {e}")
            return {'error': str(e)}


class IntelligentWebSearch:
    """
    Intelligent web search agent that decides when and how to search for information.
    """
    
    def __init__(self, searxng_url: str = "http://localhost:8080"):
        """Initialize intelligent web search."""
        self.searxng_url = searxng_url
        self.search_patterns = {
            'current_events': [
                r'\b(?:news|current|recent|latest|today|yesterday|this week)\b',
                r'\b(?:happening|trending|breaking)\b',
                r'\b(?:2024|2025)\b'
            ],
            'data_sources': [
                r'\b(?:dataset|data|statistics|stats|numbers)\b',
                r'\b(?:census|survey|report|study)\b',
                r'\b(?:api|download|source)\b'
            ],
            'technical_info': [
                r'\b(?:how to|tutorial|guide|documentation)\b',
                r'\b(?:library|framework|tool|software)\b',
                r'\b(?:install|setup|configure)\b'
            ],
            'market_data': [
                r'\b(?:stock|price|market|trading|finance)\b',
                r'\b(?:cryptocurrency|crypto|bitcoin|ethereum)\b',
                r'\b(?:economy|inflation|gdp)\b'
            ]
        }
        
    def should_search_web(self, query: str, context: Dict[str, Any] = None) -> bool:
        """
        Determine if web search is needed for the query.
        
        Args:
            query: User query
            context: Additional context
            
        Returns:
            True if web search is recommended
        """
        query_lower = query.lower()
        
        # Check for explicit search indicators
        explicit_indicators = [
            'search', 'find', 'look up', 'research', 'latest', 'current',
            'news', 'recent', 'today', 'now', 'real-time', 'live'
        ]
        
        if any(indicator in query_lower for indicator in explicit_indicators):
            return True
            
        # Check pattern matches
        for category, patterns in self.search_patterns.items():
            for pattern in patterns:
                if re.search(pattern, query_lower):
                    logger.info(f"Web search triggered by {category} pattern: {pattern}")
                    return True
                    
        # Check for specific data requests that might need current info
        data_indicators = [
            'covid', 'weather', 'election', 'population', 'temperature',
            'unemployment', 'inflation', 'stock market', 'gdp'
        ]
        
        if any(indicator in query_lower for indicator in data_indicators):
            return True
            
        return False
    
    def extract_search_terms(self, query: str) -> List[str]:
        """
        Extract relevant search terms from user query.
        
        Args:
            query: User query
            
        Returns:
            List of search terms
        """
        # Remove common stop words but keep important context
        stop_words = {
            'a', 'an', 'and', 'are', 'as', 'at', 'be', 'by', 'for',
            'from', 'has', 'he', 'in', 'is', 'it', 'its', 'of', 'on',
            'that', 'the', 'to', 'was', 'were', 'will', 'with'
        }
        
        # Extract key phrases and terms
        words = re.findall(r'\b\w+\b', query.lower())
        filtered_words = [w for w in words if w not in stop_words and len(w) > 2]
        
        # Generate search terms
        search_terms = []
        
        # Original query (cleaned)
        search_terms.append(' '.join(filtered_words))
        
        # Key phrases (2-3 words)
        for i in range(len(filtered_words) - 1):
            phrase = ' '.join(filtered_words[i:i+2])
            search_terms.append(phrase)
            
        return search_terms[:3]  # Limit to top 3 search terms
    
    async def search_and_summarize(
        self,
        query: str,
        max_results: int = 5
    ) -> Dict[str, Any]:
        """
        Perform web search and summarize results for AI consumption.
        
        Args:
            query: Search query
            max_results: Maximum number of results to process
            
        Returns:
            Summarized search results
        """
        search_terms = self.extract_search_terms(query)
        all_results = []
        
        # Try SearXNG first, fallback to simple search if not available
        try:
            async with SearXNGClient(self.searxng_url) as client:
                # Check if SearXNG is available
                if await client.health_check():
                    logger.info("Using SearXNG for web search")
                    # Search with different terms and categories
                    for term in search_terms:
                        for category in ['general', 'news', 'science']:
                            try:
                                results = await client.search(
                                    query=term,
                                    category=category,
                                    pageno=1
                                )
                                
                                if 'results' in results:
                                    all_results.extend(results['results'][:max_results])
                                    
                            except Exception as e:
                                logger.error(f"SearXNG search failed for '{term}' in {category}: {e}")
                else:
                    raise Exception("SearXNG health check failed")
                    
        except Exception as searxng_error:
            logger.warning(f"SearXNG not available ({searxng_error}), using fallback search")
            
            # Use fallback search
            try:
                async with SimpleFallbackSearch() as fallback_client:
                    for term in search_terms[:2]:  # Limit terms for fallback
                        try:
                            results = await fallback_client.search(term, max_results)
                            if 'results' in results:
                                all_results.extend(results['results'])
                        except Exception as e:
                            logger.error(f"Fallback search failed for '{term}': {e}")
                            
            except Exception as fallback_error:
                logger.error(f"Both SearXNG and fallback search failed: {fallback_error}")
                return {
                    'status': 'unavailable',
                    'message': 'Web search service not available',
                    'results': []
                }
        
        # Process and summarize results
        processed_results = self._process_search_results(all_results, max_results)
        
        return {
            'status': 'success',
            'query': query,
            'search_terms': search_terms,
            'total_found': len(all_results),
            'processed': len(processed_results),
            'results': processed_results,
            'timestamp': datetime.now().isoformat()
        }
    
    def _process_search_results(
        self,
        results: List[Dict],
        max_results: int
    ) -> List[Dict[str, str]]:
        """
        Process and clean search results.
        
        Args:
            results: Raw search results
            max_results: Maximum results to return
            
        Returns:
            Cleaned and processed results
        """
        processed = []
        seen_urls = set()
        
        for result in results:
            if len(processed) >= max_results:
                break
                
            url = result.get('url', '')
            title = result.get('title', '')
            content = result.get('content', '')
            
            # Skip duplicates
            if url in seen_urls or not url:
                continue
                
            seen_urls.add(url)
            
            # Clean and validate content
            if title and len(title.strip()) > 0:
                processed.append({
                    'title': self._clean_text(title),
                    'url': url,
                    'content': self._clean_text(content)[:500],  # Limit content
                    'domain': urlparse(url).netloc
                })
        
        return processed
    
    def _clean_text(self, text: str) -> str:
        """Clean and normalize text."""
        if not text:
            return ""
            
        # Remove extra whitespace and newlines
        text = re.sub(r'\s+', ' ', text.strip())
        
        # Remove HTML tags if any
        text = re.sub(r'<[^>]+>', '', text)
        
        return text
    
    def format_results_for_ai(self, search_results: Dict[str, Any]) -> str:
        """
        Format search results for AI consumption.
        
        Args:
            search_results: Search results from search_and_summarize
            
        Returns:
            Formatted text for AI context
        """
        if search_results['status'] != 'success':
            return f"Web search unavailable: {search_results.get('message', 'Unknown error')}"
            
        if not search_results['results']:
            return "No relevant web results found for this query."
            
        formatted = f"Web Search Results for: {search_results['query']}\n"
        formatted += f"Found {search_results['total_found']} results, showing top {search_results['processed']}\n\n"
        
        for i, result in enumerate(search_results['results'], 1):
            formatted += f"{i}. {result['title']}\n"
            formatted += f"   Source: {result['domain']}\n"
            if result['content']:
                formatted += f"   Summary: {result['content']}\n"
            formatted += f"   URL: {result['url']}\n\n"
            
        return formatted


class SimpleFallbackSearch:
    """
    Simple fallback search that doesn't require SearXNG.
    Uses DuckDuckGo instant answer API for basic searches.
    """
    
    def __init__(self):
        """Initialize simple fallback search."""
        self.session = None
        
    async def __aenter__(self):
        """Async context manager entry."""
        self.session = aiohttp.ClientSession(
            timeout=aiohttp.ClientTimeout(total=15),
            headers={
                'User-Agent': 'CelFlow-AI/1.0 (Intelligence Agent)',
                'Accept': 'application/json'
            }
        )
        return self
        
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        if self.session:
            await self.session.close()
            
    async def search(self, query: str, max_results: int = 5) -> Dict[str, Any]:
        """
        Perform a simple web search using DuckDuckGo instant answers.
        
        Args:
            query: Search query
            max_results: Maximum number of results (for compatibility)
            
        Returns:
            Dictionary with search results
        """
        try:
            # Try DuckDuckGo instant answer API first
            ddg_url = "https://api.duckduckgo.com/"
            params = {
                'q': query,
                'format': 'json',
                'no_html': '1',
                'skip_disambig': '1'
            }
            
            async with self.session.get(ddg_url, params=params) as response:
                if response.status == 200:
                    data = await response.json()
                    
                    results = []
                    
                    # Add instant answer if available
                    if data.get('Answer'):
                        results.append({
                            'title': 'Instant Answer',
                            'content': data['Answer'],
                            'url': data.get('AnswerURL', ''),
                            'engine': 'duckduckgo'
                        })
                    
                    # Add abstract if available
                    if data.get('Abstract'):
                        results.append({
                            'title': data.get('Heading', 'Abstract'),
                            'content': data['Abstract'],
                            'url': data.get('AbstractURL', ''),
                            'engine': 'duckduckgo'
                        })
                    
                    # Add related topics
                    for topic in data.get('RelatedTopics', [])[:3]:
                        if isinstance(topic, dict) and topic.get('Text'):
                            results.append({
                                'title': topic.get('FirstURL', '').split('/')[-1] or 'Related',
                                'content': topic['Text'],
                                'url': topic.get('FirstURL', ''),
                                'engine': 'duckduckgo'
                            })
                    
                    if results:
                        return {
                            'results': results,
                            'query': query,
                            'total_results': len(results),
                            'search_engine': 'duckduckgo_fallback'
                        }
            
            # If no results from instant answers, return a simulated response
            return {
                'results': [{
                    'title': f'Search for: {query}',
                    'content': f'I attempted to search for "{query}" but could not retrieve specific results. This might be due to search service limitations or the query requiring more specific terms.',
                    'url': f'https://duckduckgo.com/?q={quote_plus(query)}',
                    'engine': 'fallback'
                }],
                'query': query,
                'total_results': 1,
                'search_engine': 'fallback_simulation'
            }
            
        except Exception as e:
            logger.error(f"Fallback search failed: {e}")
            return {
                'results': [{
                    'title': 'Search Unavailable',
                    'content': f'Web search is currently unavailable. Error: {str(e)}',
                    'url': '',
                    'engine': 'error'
                }],
                'query': query,
                'total_results': 0,
                'search_engine': 'error'
            }


# Singleton instance for use throughout the application
web_search_client = IntelligentWebSearch()


async def search_web_for_query(query: str) -> Optional[str]:
    """
    Convenience function to search web if needed and return formatted results.
    
    Args:
        query: User query
        
    Returns:
        Formatted search results or None if search not needed
    """
    if not web_search_client.should_search_web(query):
        return None
        
    logger.info(f"Performing web search for query: {query}")
    
    try:
        results = await web_search_client.search_and_summarize(query)
        return web_search_client.format_results_for_ai(results)
    except Exception as e:
        logger.error(f"Web search failed: {e}")
        return f"Web search failed: {str(e)}"
