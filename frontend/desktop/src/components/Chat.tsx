import React, { useState, useRef, useEffect } from 'react';
import { invoke } from '@tauri-apps/api/core';
import { cn } from '../utils/cn';
import { Message, ChatResponse, ChatSession } from '../types/alims';

interface ChatProps {
  className?: string;
}

export const Chat: React.FC<ChatProps> = ({ className }) => {
  const [messages, setMessages] = useState<Message[]>([]);
  const [input, setInput] = useState('');
  const [isResizing, setIsResizing] = useState(false);
  const [width, setWidth] = useState(400); // Default width
  const [sessionId, setSessionId] = useState<string | null>(null);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const chatContainerRef = useRef<HTMLDivElement>(null);
  const messagesEndRef = useRef<HTMLDivElement>(null);

  // Initialize chat session
  useEffect(() => {
    const initChat = async () => {
      try {
        setIsLoading(true);
        const session = await invoke<string>('start_chat_session');
        setSessionId(session);
        
        // Load chat history
        const history = await invoke<ChatSession>('get_chat_history', { sessionId: session });
        if (history?.messages) {
          setMessages(history.messages);
        }
      } catch (err) {
        console.error('Failed to initialize chat:', err);
        setError('Failed to initialize chat. Please try again.');
      } finally {
        setIsLoading(false);
      }
    };

    initChat();
  }, []);

  // Scroll to bottom when messages change
  const scrollToBottom = () => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  };

  useEffect(() => {
    scrollToBottom();
  }, [messages]);

  // Handle resizing
  const startResizing = (e: React.MouseEvent) => {
    setIsResizing(true);
    e.preventDefault();
  };

  useEffect(() => {
    const handleMouseMove = (e: MouseEvent) => {
      if (!isResizing) return;

      const containerWidth = window.innerWidth;
      const newWidth = containerWidth - e.clientX;
      
      // Limit width between 300px and 800px
      if (newWidth >= 300 && newWidth <= 800) {
        setWidth(newWidth);
      }
    };

    const handleMouseUp = () => {
      setIsResizing(false);
    };

    if (isResizing) {
      window.addEventListener('mousemove', handleMouseMove);
      window.addEventListener('mouseup', handleMouseUp);
    }

    return () => {
      window.removeEventListener('mousemove', handleMouseMove);
      window.removeEventListener('mouseup', handleMouseUp);
    };
  }, [isResizing]);

  // Handle message sending
  const handleSendMessage = async () => {
    if (!input.trim() || !sessionId) return;

    const newMessage: Message = {
      role: 'user',
      content: input.trim(),
      timestamp: new Date().toLocaleTimeString(),
    };

    setMessages((prev) => [...prev, newMessage]);
    setInput('');
    setError(null);

    try {
      const response = await invoke<ChatResponse>('send_chat_message', {
        message: newMessage.content,
        sessionId,
      });

      if (response.error) {
        setError(response.error);
        return;
      }

      const aiMessage: Message = {
        role: 'assistant',
        content: response.response.content,
        timestamp: new Date().toLocaleTimeString(),
        agent_name: response.response.agent_name,
        specialization: response.response.specialization,
        confidence: response.response.confidence,
        suggested_actions: response.response.suggested_actions,
      };

      setMessages((prev) => [...prev, aiMessage]);
    } catch (err) {
      console.error('Failed to send message:', err);
      setError('Failed to send message. Please try again.');
    }
  };

  const handleKeyPress = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      handleSendMessage();
    }
  };

  if (isLoading) {
    return (
      <div className="fixed top-0 right-0 h-screen bg-white dark:bg-gray-800 shadow-lg flex items-center justify-center" style={{ width: `${width}px` }}>
        <div className="text-center">
          <div className="animate-spin rounded-full h-8 w-8 border-t-2 border-b-2 border-blue-500 mx-auto"></div>
          <p className="mt-4 text-gray-600 dark:text-gray-300">Initializing chat...</p>
        </div>
      </div>
    );
  }

  return (
    <div 
      ref={chatContainerRef}
      className={cn(
        'fixed top-0 right-0 h-screen bg-white dark:bg-gray-800 shadow-lg flex flex-col',
        'border-l border-gray-200 dark:border-gray-700',
        className
      )}
      style={{ width: `${width}px` }}
    >
      {/* Resizer */}
      <div
        className={cn(
          'absolute left-0 top-0 w-1 h-full cursor-col-resize',
          'hover:bg-blue-500 transition-colors',
          isResizing && 'bg-blue-500'
        )}
        onMouseDown={startResizing}
      />

      {/* Header */}
      <div className="p-4 border-b border-gray-200 dark:border-gray-700">
        <h2 className="text-lg font-semibold text-gray-800 dark:text-white">
          🔬 Chat with ALIMS AI
        </h2>
      </div>

      {/* Messages */}
      <div className="flex-1 overflow-y-auto p-4 space-y-4">
        {messages.map((message, index) => (
          <div
            key={index}
            className={cn(
              'flex flex-col max-w-[80%] rounded-lg p-3',
              message.role === 'user' 
                ? 'ml-auto bg-blue-500 text-white' 
                : 'bg-gray-100 dark:bg-gray-700 dark:text-white'
            )}
          >
            {message.role === 'assistant' && message.agent_name && (
              <div className="text-xs text-gray-500 dark:text-gray-400 mb-1">
                {message.agent_name} ({message.specialization})
              </div>
            )}
            <div className="text-sm">{message.content}</div>
            <div className={cn(
              'text-xs mt-1',
              message.role === 'user' 
                ? 'text-blue-100' 
                : 'text-gray-500 dark:text-gray-400'
            )}>
              {message.timestamp}
            </div>
            {message.role === 'assistant' && message.suggested_actions && message.suggested_actions.length > 0 && (
              <div className="mt-2 space-y-1">
                {message.suggested_actions.map((action, actionIndex) => (
                  <button
                    key={actionIndex}
                    onClick={() => setInput(action)}
                    className={cn(
                      'text-xs px-2 py-1 rounded',
                      'bg-gray-200 dark:bg-gray-600',
                      'hover:bg-gray-300 dark:hover:bg-gray-500',
                      'text-gray-700 dark:text-gray-200',
                      'transition-colors'
                    )}
                  >
                    {action}
                  </button>
                ))}
              </div>
            )}
          </div>
        ))}
        <div ref={messagesEndRef} />
      </div>

      {/* Error message */}
      {error && (
        <div className="px-4 py-2 bg-red-100 dark:bg-red-900 text-red-700 dark:text-red-200 text-sm">
          {error}
        </div>
      )}

      {/* Input */}
      <div className="p-4 border-t border-gray-200 dark:border-gray-700">
        <div className="flex space-x-2">
          <textarea
            value={input}
            onChange={(e) => setInput(e.target.value)}
            onKeyPress={handleKeyPress}
            placeholder="Type your message..."
            className={cn(
              'flex-1 p-2 rounded-lg border border-gray-200 dark:border-gray-600',
              'focus:outline-none focus:ring-2 focus:ring-blue-500',
              'bg-white dark:bg-gray-700 text-gray-800 dark:text-white',
              'resize-none'
            )}
            rows={3}
          />
          <button
            onClick={handleSendMessage}
            className={cn(
              'px-4 py-2 rounded-lg bg-blue-500 text-white',
              'hover:bg-blue-600 transition-colors',
              'disabled:opacity-50 disabled:cursor-not-allowed'
            )}
            disabled={!input.trim() || !sessionId}
          >
            Send
          </button>
        </div>
      </div>
    </div>
  );
};

export default Chat; 