"""
Voice Interface - Speech-to-Text Command Processing

This module provides voice interaction capabilities for ALims including:
- Speech-to-text conversion using multiple engines
- Voice command recognition and processing
- Audio feedback and text-to-speech responses
- Continuous listening and wake word detection
- Voice activity detection and noise filtering
"""

import asyncio
import logging
import threading
import queue
import time
from datetime import datetime
from typing import Dict, Any, Optional, Callable, List
from dataclasses import dataclass
from enum import Enum
import json

# Audio processing imports
try:
    import speech_recognition as sr
    import pyttsx3
    import pyaudio
    import wave
    import numpy as np

    AUDIO_AVAILABLE = True
except ImportError:
    AUDIO_AVAILABLE = False
    sr = None
    pyttsx3 = None
    pyaudio = None
    wave = None
    np = None

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class VoiceEngineType(Enum):
    """Available speech recognition engines"""

    GOOGLE = "google"
    SPHINX = "sphinx"
    WHISPER = "whisper"
    AZURE = "azure"
    IBM = "ibm"


class VoiceCommandType(Enum):
    """Types of voice commands"""

    SYSTEM_CONTROL = "system_control"
    CHAT_MESSAGE = "chat_message"
    TASK_MANAGEMENT = "task_management"
    QUERY_REQUEST = "query_request"
    NAVIGATION = "navigation"
    SETTINGS = "settings"
    WAKE_WORD = "wake_word"
    STOP_LISTENING = "stop_listening"


class ListeningState(Enum):
    """Voice interface listening states"""

    IDLE = "idle"
    LISTENING = "listening"
    PROCESSING = "processing"
    RESPONDING = "responding"
    ERROR = "error"


@dataclass
class VoiceCommand:
    """A processed voice command"""

    command_id: str
    raw_text: str
    processed_text: str
    command_type: VoiceCommandType
    confidence: float
    timestamp: datetime
    processing_time: float
    engine_used: VoiceEngineType
    wake_word_detected: bool = False
    parameters: Dict[str, Any] = None


@dataclass
class VoiceResponse:
    """A voice response to be spoken"""

    response_id: str
    text: str
    priority: str  # low, normal, high, urgent
    voice_settings: Dict[str, Any]
    timestamp: datetime


@dataclass
class VoiceMetrics:
    """Voice interface performance metrics"""

    total_commands: int
    successful_recognitions: int
    failed_recognitions: int
    average_confidence: float
    average_processing_time: float
    wake_word_detections: int
    false_positives: int
    engine_performance: Dict[str, Dict[str, Any]]


class VoiceInterface:
    """
    Voice Interface System for ALims

    Provides speech-to-text, voice command processing, and audio feedback
    capabilities for hands-free interaction with the ALims system.
    """

    def __init__(self, config: Dict[str, Any]):
        """Initialize the Voice Interface"""
        self.config = config
        self.voice_config = config.get("voice_interface", {})

        # Check audio availability
        if not AUDIO_AVAILABLE:
            logger.warning("Audio libraries not available. Running in simulation mode.")
            self.simulation_mode = True
        else:
            self.simulation_mode = False

        # Core components (will be None in simulation mode)
        self.recognizer = sr.Recognizer() if not self.simulation_mode else None
        self.microphone = None
        self.tts_engine = None

        # State management
        self.is_listening = False
        self.listening_state = ListeningState.IDLE
        self.command_queue = queue.Queue()
        self.response_queue = queue.Queue()

        # Configuration
        self.wake_words = self.voice_config.get(
            "wake_words", ["hey alims", "alims"]
        )
        self.engines = self._get_available_engines()
        self.primary_engine = VoiceEngineType(
            self.voice_config.get("primary_engine", "google")
        )
        self.fallback_engines = [
            VoiceEngineType(e)
            for e in self.voice_config.get("fallback_engines", ["sphinx"])
        ]

        # Audio settings
        self.energy_threshold = self.voice_config.get("energy_threshold", 300)
        self.dynamic_energy_threshold = self.voice_config.get(
            "dynamic_energy_threshold", True
        )
        self.pause_threshold = self.voice_config.get("pause_threshold", 0.8)
        self.phrase_threshold = self.voice_config.get("phrase_threshold", 0.3)
        self.timeout = self.voice_config.get("timeout", 5)

        # TTS settings
        self.tts_enabled = self.voice_config.get("tts_enabled", True)
        self.tts_rate = self.voice_config.get("tts_rate", 200)
        self.tts_volume = self.voice_config.get("tts_volume", 0.8)
        self.tts_voice = self.voice_config.get("tts_voice", None)

        # Command processing
        self.command_callback: Optional[Callable] = None
        self.command_patterns = self._load_command_patterns()

        # Performance tracking
        self.metrics = VoiceMetrics(
            total_commands=0,
            successful_recognitions=0,
            failed_recognitions=0,
            average_confidence=0.0,
            average_processing_time=0.0,
            wake_word_detections=0,
            false_positives=0,
            engine_performance={},
        )

        # Threading
        self.listening_thread = None
        self.processing_thread = None
        self.response_thread = None
        self.stop_event = threading.Event()

        logger.info("VoiceInterface initialized successfully")

    def _get_available_engines(self) -> List[VoiceEngineType]:
        """Get list of available speech recognition engines"""
        available = []

        # Test Google Speech Recognition
        try:
            test_recognizer = sr.Recognizer()
            # Google is usually available if internet connection exists
            available.append(VoiceEngineType.GOOGLE)
        except:
            pass

        # Test CMU Sphinx (offline)
        try:
            test_recognizer = sr.Recognizer()
            # Sphinx is available if pocketsphinx is installed
            available.append(VoiceEngineType.SPHINX)
        except:
            pass

        # Add other engines based on availability
        # Whisper, Azure, IBM would require additional setup

        if not available:
            available.append(VoiceEngineType.SPHINX)  # Fallback

        logger.info(f"Available speech engines: {[e.value for e in available]}")
        return available

    def _load_command_patterns(self) -> Dict[str, Dict[str, Any]]:
        """Load voice command patterns and mappings"""
        return {
            "wake_words": {
                "patterns": self.wake_words,
                "type": VoiceCommandType.WAKE_WORD,
                "action": "activate_listening",
            },
            "stop_commands": {
                "patterns": ["stop listening", "stop", "cancel", "nevermind"],
                "type": VoiceCommandType.STOP_LISTENING,
                "action": "deactivate_listening",
            },
            "system_commands": {
                "patterns": [
                    "show status",
                    "system status",
                    "health check",
                    "start agent",
                    "stop agent",
                    "restart system",
                ],
                "type": VoiceCommandType.SYSTEM_CONTROL,
                "action": "system_control",
            },
            "chat_commands": {
                "patterns": [
                    "tell me about",
                    "what is",
                    "how do",
                    "explain",
                    "help me",
                    "assist with",
                    "chat about",
                ],
                "type": VoiceCommandType.CHAT_MESSAGE,
                "action": "chat_message",
            },
            "task_commands": {
                "patterns": [
                    "create task",
                    "add task",
                    "complete task",
                    "list tasks",
                    "show tasks",
                    "task status",
                ],
                "type": VoiceCommandType.TASK_MANAGEMENT,
                "action": "task_management",
            },
            "query_commands": {
                "patterns": [
                    "search for",
                    "find",
                    "lookup",
                    "query",
                    "get information",
                    "show me",
                    "display",
                ],
                "type": VoiceCommandType.QUERY_REQUEST,
                "action": "query_request",
            },
        }

    async def start(self):
        """Start the voice interface system"""
        try:
            logger.info("🎤 Starting Voice Interface...")

            if not self.simulation_mode:
                # Initialize microphone
                self.microphone = sr.Microphone()

                # Initialize TTS engine
                if self.tts_enabled:
                    self.tts_engine = pyttsx3.init()
                    self._configure_tts()

                # Calibrate microphone for ambient noise
                await self._calibrate_microphone()
            else:
                logger.info("Running in simulation mode - audio features disabled")

            # Start processing threads
            self._start_threads()

            logger.info("✅ Voice Interface started successfully")
            return True

        except Exception as e:
            logger.error(f"❌ Failed to start Voice Interface: {e}")
            return False

    async def stop(self):
        """Stop the voice interface system"""
        try:
            logger.info("🛑 Stopping Voice Interface...")

            # Signal threads to stop
            self.stop_event.set()
            self.is_listening = False

            # Wait for threads to finish
            if self.listening_thread and self.listening_thread.is_alive():
                self.listening_thread.join(timeout=2)

            if self.processing_thread and self.processing_thread.is_alive():
                self.processing_thread.join(timeout=2)

            if self.response_thread and self.response_thread.is_alive():
                self.response_thread.join(timeout=2)

            # Cleanup TTS
            if self.tts_engine:
                self.tts_engine.stop()

            logger.info("✅ Voice Interface stopped successfully")

        except Exception as e:
            logger.error(f"❌ Error stopping Voice Interface: {e}")

    def _configure_tts(self):
        """Configure text-to-speech engine"""
        if not self.tts_engine:
            return

        # Set speech rate
        self.tts_engine.setProperty("rate", self.tts_rate)

        # Set volume
        self.tts_engine.setProperty("volume", self.tts_volume)

        # Set voice if specified
        if self.tts_voice:
            voices = self.tts_engine.getProperty("voices")
            for voice in voices:
                if self.tts_voice.lower() in voice.name.lower():
                    self.tts_engine.setProperty("voice", voice.id)
                    break

    async def _calibrate_microphone(self):
        """Calibrate microphone for ambient noise"""
        try:
            logger.info("🎯 Calibrating microphone for ambient noise...")

            with self.microphone as source:
                # Adjust for ambient noise
                self.recognizer.adjust_for_ambient_noise(source, duration=2)

                # Set energy threshold
                if self.dynamic_energy_threshold:
                    self.recognizer.dynamic_energy_threshold = True
                else:
                    self.recognizer.energy_threshold = self.energy_threshold

                # Set other parameters
                self.recognizer.pause_threshold = self.pause_threshold
                self.recognizer.phrase_threshold = self.phrase_threshold

            logger.info(
                f"✅ Microphone calibrated (energy threshold: {self.recognizer.energy_threshold})"
            )

        except Exception as e:
            logger.error(f"❌ Microphone calibration failed: {e}")

    def _start_threads(self):
        """Start background processing threads"""
        # Listening thread
        self.listening_thread = threading.Thread(
            target=self._listening_loop, name="VoiceListening", daemon=True
        )
        self.listening_thread.start()

        # Command processing thread
        self.processing_thread = threading.Thread(
            target=self._processing_loop, name="VoiceProcessing", daemon=True
        )
        self.processing_thread.start()

        # Response thread
        self.response_thread = threading.Thread(
            target=self._response_loop, name="VoiceResponse", daemon=True
        )
        self.response_thread.start()

    def _listening_loop(self):
        """Main listening loop for voice input"""
        logger.info("🎧 Voice listening loop started")

        while not self.stop_event.is_set():
            try:
                if self.is_listening:
                    self.listening_state = ListeningState.LISTENING

                    # Listen for audio
                    with self.microphone as source:
                        audio = self.recognizer.listen(
                            source, timeout=self.timeout, phrase_time_limit=10
                        )

                    # Queue audio for processing
                    self.command_queue.put(
                        {"audio": audio, "timestamp": datetime.now()}
                    )

                else:
                    # Sleep when not actively listening
                    time.sleep(0.1)

            except sr.WaitTimeoutError:
                # Timeout is normal, continue listening
                continue
            except Exception as e:
                logger.error(f"Error in listening loop: {e}")
                self.listening_state = ListeningState.ERROR
                time.sleep(1)

    def _processing_loop(self):
        """Main processing loop for voice commands"""
        logger.info("⚙️ Voice processing loop started")

        while not self.stop_event.is_set():
            try:
                # Get audio from queue
                try:
                    audio_data = self.command_queue.get(timeout=1)
                except queue.Empty:
                    continue

                self.listening_state = ListeningState.PROCESSING
                start_time = time.time()

                # Process the audio
                command = self._process_audio(
                    audio_data["audio"], audio_data["timestamp"]
                )

                if command:
                    processing_time = time.time() - start_time
                    command.processing_time = processing_time

                    # Update metrics
                    self.metrics.total_commands += 1
                    self.metrics.successful_recognitions += 1

                    # Handle the command
                    try:
                        loop = asyncio.get_event_loop()
                        loop.create_task(self._handle_voice_command(command))
                    except RuntimeError:
                        # If no event loop is running, skip async handling
                        pass
                else:
                    self.metrics.failed_recognitions += 1

                self.listening_state = ListeningState.IDLE

            except Exception as e:
                logger.error(f"Error in processing loop: {e}")
                self.listening_state = ListeningState.ERROR
                time.sleep(1)

    def _response_loop(self):
        """Main loop for voice responses"""
        logger.info("🔊 Voice response loop started")

        while not self.stop_event.is_set():
            try:
                # Get response from queue
                try:
                    response = self.response_queue.get(timeout=1)
                except queue.Empty:
                    continue

                if self.tts_enabled and self.tts_engine:
                    self.listening_state = ListeningState.RESPONDING

                    # Speak the response
                    self.tts_engine.say(response.text)
                    self.tts_engine.runAndWait()

                    self.listening_state = ListeningState.IDLE

            except Exception as e:
                logger.error(f"Error in response loop: {e}")
                time.sleep(1)

    def _process_audio(self, audio, timestamp: datetime) -> Optional[VoiceCommand]:
        """Process audio data into a voice command"""
        try:
            # Try primary engine first
            text, confidence, engine = self._recognize_speech(
                audio, self.primary_engine
            )

            # Try fallback engines if primary fails
            if not text and self.fallback_engines:
                for fallback_engine in self.fallback_engines:
                    text, confidence, engine = self._recognize_speech(
                        audio, fallback_engine
                    )
                    if text:
                        break

            if not text:
                return None

            # Process the recognized text
            processed_text = text.lower().strip()
            command_type = self._classify_command(processed_text)
            wake_word_detected = self._detect_wake_word(processed_text)

            # Create command object
            command = VoiceCommand(
                command_id=f"voice_{int(timestamp.timestamp())}",
                raw_text=text,
                processed_text=processed_text,
                command_type=command_type,
                confidence=confidence,
                timestamp=timestamp,
                processing_time=0.0,
                engine_used=engine,
                wake_word_detected=wake_word_detected,
                parameters=self._extract_parameters(processed_text, command_type),
            )

            logger.info(
                f"Voice command recognized: '{text}' (confidence: {confidence:.2f})"
            )
            return command

        except Exception as e:
            logger.error(f"Error processing audio: {e}")
            return None

    def _recognize_speech(self, audio, engine: VoiceEngineType) -> tuple:
        """Recognize speech using specified engine"""
        try:
            if engine == VoiceEngineType.GOOGLE:
                text = self.recognizer.recognize_google(audio)
                confidence = 0.8  # Google doesn't provide confidence scores

            elif engine == VoiceEngineType.SPHINX:
                text = self.recognizer.recognize_sphinx(audio)
                confidence = 0.6  # Sphinx typically has lower accuracy

            else:
                # Fallback to Google
                text = self.recognizer.recognize_google(audio)
                confidence = 0.7
                engine = VoiceEngineType.GOOGLE

            return text, confidence, engine

        except sr.UnknownValueError:
            return None, 0.0, engine
        except sr.RequestError as e:
            logger.error(f"Speech recognition error with {engine.value}: {e}")
            return None, 0.0, engine

    def _classify_command(self, text: str) -> VoiceCommandType:
        """Classify the type of voice command"""
        text_lower = text.lower()

        # Check each command pattern
        for category, config in self.command_patterns.items():
            for pattern in config["patterns"]:
                if pattern.lower() in text_lower:
                    return config["type"]

        # Default to chat message if no specific pattern matches
        return VoiceCommandType.CHAT_MESSAGE

    def _detect_wake_word(self, text: str) -> bool:
        """Detect if wake word is present in text"""
        text_lower = text.lower()
        return any(wake_word.lower() in text_lower for wake_word in self.wake_words)

    def _extract_parameters(
        self, text: str, command_type: VoiceCommandType
    ) -> Dict[str, Any]:
        """Extract parameters from voice command text"""
        parameters = {}

        if command_type == VoiceCommandType.SYSTEM_CONTROL:
            if "start" in text:
                parameters["action"] = "start"
            elif "stop" in text:
                parameters["action"] = "stop"
            elif "restart" in text:
                parameters["action"] = "restart"
            elif "status" in text:
                parameters["action"] = "status"

        elif command_type == VoiceCommandType.TASK_MANAGEMENT:
            if "create" in text or "add" in text:
                parameters["action"] = "create"
            elif "complete" in text:
                parameters["action"] = "complete"
            elif "list" in text or "show" in text:
                parameters["action"] = "list"

        elif command_type == VoiceCommandType.QUERY_REQUEST:
            if "search" in text or "find" in text:
                parameters["action"] = "search"
                # Extract search terms (simplified)
                words = text.split()
                if "for" in words:
                    for_index = words.index("for")
                    if for_index + 1 < len(words):
                        parameters["query"] = " ".join(words[for_index + 1 :])

        return parameters

    async def _handle_voice_command(self, command: VoiceCommand):
        """Handle a processed voice command"""
        try:
            # Handle wake word
            if command.wake_word_detected:
                self.metrics.wake_word_detections += 1
                if not self.is_listening:
                    await self.start_listening()
                    await self.speak("I'm listening")
                    return

            # Handle stop command
            if command.command_type == VoiceCommandType.STOP_LISTENING:
                await self.stop_listening()
                await self.speak("Stopped listening")
                return

            # Forward to registered callback if available
            if self.command_callback:
                try:
                    await self.command_callback(command)
                except Exception as e:
                    logger.error(f"Error in command callback: {e}")
                    await self.speak(
                        "Sorry, I encountered an error processing that command"
                    )
            else:
                # Default response
                await self.speak(
                    "I heard you, but I'm not sure how to help with that yet"
                )

        except Exception as e:
            logger.error(f"Error handling voice command: {e}")

    async def start_listening(self):
        """Start active listening for voice commands"""
        self.is_listening = True
        self.listening_state = ListeningState.LISTENING
        logger.info("🎤 Started active listening")

    async def stop_listening(self):
        """Stop active listening for voice commands"""
        self.is_listening = False
        self.listening_state = ListeningState.IDLE
        logger.info("🔇 Stopped active listening")

    async def speak(self, text: str, priority: str = "normal"):
        """Add text to speech queue"""
        if not self.tts_enabled:
            return

        response = VoiceResponse(
            response_id=f"response_{int(time.time())}",
            text=text,
            priority=priority,
            voice_settings={},
            timestamp=datetime.now(),
        )

        self.response_queue.put(response)
        logger.info(f"Queued voice response: '{text}'")

    def set_command_callback(self, callback: Callable):
        """Set callback function for processing voice commands"""
        self.command_callback = callback
        logger.info("Voice command callback registered")

    def get_voice_metrics(self) -> Dict[str, Any]:
        """Get voice interface performance metrics"""
        total_attempts = (
            self.metrics.successful_recognitions + self.metrics.failed_recognitions
        )
        success_rate = (
            (self.metrics.successful_recognitions / total_attempts * 100)
            if total_attempts > 0
            else 0
        )

        return {
            "total_commands": self.metrics.total_commands,
            "successful_recognitions": self.metrics.successful_recognitions,
            "failed_recognitions": self.metrics.failed_recognitions,
            "success_rate": success_rate,
            "average_confidence": self.metrics.average_confidence,
            "average_processing_time": self.metrics.average_processing_time,
            "wake_word_detections": self.metrics.wake_word_detections,
            "false_positives": self.metrics.false_positives,
            "current_state": self.listening_state.value,
            "is_listening": self.is_listening,
            "available_engines": [e.value for e in self.engines],
            "primary_engine": self.primary_engine.value,
            "tts_enabled": self.tts_enabled,
        }

    def get_voice_status(self) -> Dict[str, Any]:
        """Get current voice interface status"""
        return {
            "is_active": self.is_listening,
            "current_state": self.listening_state.value,
            "microphone_available": self.microphone is not None,
            "tts_available": self.tts_engine is not None,
            "energy_threshold": getattr(self.recognizer, "energy_threshold", 0),
            "wake_words": self.wake_words,
            "command_queue_size": self.command_queue.qsize(),
            "response_queue_size": self.response_queue.qsize(),
        }


# Utility functions
def create_voice_interface(config: Dict[str, Any]) -> Optional[VoiceInterface]:
    """Create and initialize a voice interface instance"""
    try:
        voice_interface = VoiceInterface(config)
        return voice_interface
    except Exception as e:
        logger.error(f"Failed to create voice interface: {e}")
        return None
