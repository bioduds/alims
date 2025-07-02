"""
ALims Central AI Brain - Ollama Client
Manages connection to local Ollama Gemma 3:4B model
"""

import json
import logging
from typing import Dict, Any, Optional, AsyncIterator
from datetime import datetime, timedelta

import aiohttp
import tiktoken
from tenacity import retry, stop_after_attempt, wait_exponential
from pydantic import BaseModel

logger = logging.getLogger(__name__)


class OllamaResponse(BaseModel):
    """Structured response from Ollama API"""

    content: str
    model: str
    created_at: datetime
    done: bool
    total_duration: Optional[int] = None
    load_duration: Optional[int] = None
    prompt_eval_count: Optional[int] = None
    eval_count: Optional[int] = None


class OllamaClient:
    """Manages connection to local Ollama Gemma 3:4B model"""

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.base_url = config.get("base_url", "http://localhost:11434")
        self.model_name = config.get("model_name", "gemma3:4b")
        self.timeout = config.get("timeout", 30)
        self.max_tokens = config.get("max_tokens", 2048)
        self.temperature = config.get("temperature", 0.7)
        self.context_window = config.get("context_window", 8192)

        # Initialize session and tokenizer
        self.session: Optional[aiohttp.ClientSession] = None
        self.tokenizer = None
        self._initialize_tokenizer()

        # Health monitoring
        self.last_health_check = None
        self.is_healthy = False

        logger.info(f"OllamaClient initialized for model: {self.model_name}")

    def _initialize_tokenizer(self):
        """Initialize tokenizer for token counting"""
        try:
            # Use a general tokenizer for token counting
            self.tokenizer = tiktoken.get_encoding("cl100k_base")
        except Exception as e:
            logger.warning(f"Could not initialize tokenizer: {e}")
            self.tokenizer = None

    async def __aenter__(self):
        """Async context manager entry"""
        await self.start()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit"""
        await self.close()

    async def start(self):
        """Initialize the client session"""
        if not self.session:
            timeout = aiohttp.ClientTimeout(total=self.timeout)
            self.session = aiohttp.ClientSession(timeout=timeout)
            await self.validate_model_health()

    async def close(self):
        """Close the client session"""
        if self.session:
            await self.session.close()
            self.session = None

    @retry(
        stop=stop_after_attempt(3), wait=wait_exponential(multiplier=1, min=4, max=10)
    )
    async def validate_model_health(self) -> bool:
        """Ensure model is running and responsive"""
        try:
            if not self.session:
                await self.start()

            # Simple health check with minimal prompt
            await self._make_request(
                {
                    "model": self.model_name,
                    "prompt": "Hello",
                    "stream": False,
                    "options": {"num_predict": 10, "temperature": 0.1},
                }
            )

            self.is_healthy = True
            self.last_health_check = datetime.now()
            logger.info(f"Model {self.model_name} is healthy")
            return True

        except Exception as e:
            self.is_healthy = False
            logger.error(f"Model health check failed: {e}")
            return False

    async def _make_request(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Make HTTP request to Ollama API"""
        if not self.session:
            await self.start()

        url = f"{self.base_url}/api/generate"

        async with self.session.post(url, json=payload) as response:
            if response.status != 200:
                error_text = await response.text()
                raise Exception(f"Ollama API error {response.status}: {error_text}")

            return await response.json()

    async def count_tokens(self, text: str) -> int:
        """Count tokens for context management"""
        if not self.tokenizer:
            # Rough estimation if tokenizer not available
            return len(text.split()) * 1.3

        try:
            return len(self.tokenizer.encode(text))
        except Exception as e:
            logger.warning(f"Token counting failed: {e}")
            return len(text.split()) * 1.3

    async def generate_response(
        self,
        prompt: str,
        context: Optional[Dict[str, Any]] = None,
        system_prompt: Optional[str] = None,
    ) -> str:
        """Generate response with context awareness"""

        # Check model health periodically
        if (
            not self.last_health_check
            or datetime.now() - self.last_health_check > timedelta(minutes=5)
        ):
            await self.validate_model_health()

        if not self.is_healthy:
            raise Exception("Model is not healthy")

        # Build full prompt with system context
        full_prompt = self._build_full_prompt(prompt, context, system_prompt)

        # Ensure we don't exceed context window
        token_count = await self.count_tokens(full_prompt)
        if token_count > self.context_window - self.max_tokens:
            logger.warning(f"Prompt too long ({token_count} tokens), truncating")
            full_prompt = self._truncate_prompt(full_prompt)

        payload = {
            "model": self.model_name,
            "prompt": full_prompt,
            "stream": False,
            "options": {
                "num_predict": self.max_tokens,
                "temperature": self.temperature,
                "top_p": 0.9,
                "top_k": 40,
            },
        }

        try:
            response_data = await self._make_request(payload)
            content = response_data.get("response", "").strip()

            # Log interaction for monitoring
            logger.info(f"Generated response: {len(content)} characters")

            return content

        except Exception as e:
            logger.error(f"Response generation failed: {e}")
            raise

    async def stream_response(
        self,
        prompt: str,
        context: Optional[Dict[str, Any]] = None,
        system_prompt: Optional[str] = None,
    ) -> AsyncIterator[str]:
        """Stream real-time responses for chat interface"""

        if not self.is_healthy:
            await self.validate_model_health()
            if not self.is_healthy:
                raise Exception("Model is not healthy")

        full_prompt = self._build_full_prompt(prompt, context, system_prompt)

        payload = {
            "model": self.model_name,
            "prompt": full_prompt,
            "stream": True,
            "options": {
                "num_predict": self.max_tokens,
                "temperature": self.temperature,
            },
        }

        url = f"{self.base_url}/api/generate"

        try:
            async with self.session.post(url, json=payload) as response:
                if response.status != 200:
                    error_text = await response.text()
                    raise Exception(f"Ollama API error {response.status}: {error_text}")

                async for line in response.content:
                    if line:
                        try:
                            data = json.loads(line.decode("utf-8"))
                            if "response" in data:
                                yield data["response"]
                            if data.get("done", False):
                                break
                        except json.JSONDecodeError:
                            continue

        except Exception as e:
            logger.error(f"Streaming response failed: {e}")
            raise

    def _build_full_prompt(
        self,
        prompt: str,
        context: Optional[Dict[str, Any]] = None,
        system_prompt: Optional[str] = None,
    ) -> str:
        """Build full prompt with system context"""
        parts = []

        if system_prompt:
            parts.append(f"SYSTEM: {system_prompt}")

        if context:
            # Add relevant context information
            if "system_status" in context:
                parts.append(f"System Status: {context['system_status']}")
            if "user_profile" in context:
                parts.append(f"User Context: {context['user_profile']}")
            if "conversation_history" in context:
                history = context["conversation_history"][-5:]  # Last 5 exchanges
                for exchange in history:
                    parts.append(f"Previous: {exchange}")

        parts.append(f"USER: {prompt}")
        parts.append("ASSISTANT:")

        return "\n\n".join(parts)

    def _truncate_prompt(self, prompt: str) -> str:
        """Truncate prompt to fit context window"""
        max_tokens = self.context_window - self.max_tokens - 100  # Safety margin

        if not self.tokenizer:
            # Simple truncation by characters
            max_chars = max_tokens * 4  # Rough estimate
            return prompt[-max_chars:]

        # Truncate by tokens
        tokens = self.tokenizer.encode(prompt)
        if len(tokens) > max_tokens:
            truncated_tokens = tokens[-max_tokens:]
            return self.tokenizer.decode(truncated_tokens)

        return prompt

    async def get_model_info(self) -> Dict[str, Any]:
        """Get information about the current model"""
        try:
            url = f"{self.base_url}/api/show"
            payload = {"name": self.model_name}

            async with self.session.post(url, json=payload) as response:
                if response.status == 200:
                    return await response.json()
                else:
                    return {"error": f"Could not get model info: {response.status}"}

        except Exception as e:
            logger.error(f"Failed to get model info: {e}")
            return {"error": str(e)}

    def get_health_status(self) -> Dict[str, Any]:
        """Get current health status"""
        return {
            "is_healthy": self.is_healthy,
            "last_health_check": (
                self.last_health_check.isoformat() if self.last_health_check else None
            ),
            "model_name": self.model_name,
            "base_url": self.base_url,
        }


# Utility functions for easy access
async def create_ollama_client(config: Dict[str, Any]) -> OllamaClient:
    """Create and initialize an OllamaClient"""
    client = OllamaClient(config)
    await client.start()
    return client


async def quick_generate(prompt: str, model_config: Dict[str, Any]) -> str:
    """Quick generation for simple use cases"""
    async with OllamaClient(model_config) as client:
        return await client.generate_response(prompt)
