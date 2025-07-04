/**
 * Main Interface Agent API Client
 * 
 * TypeScript client for interacting with the ALIMS Main Interface Agent
 * from the Tauri frontend application.
 */

export interface ConversationMessage {
  role: 'user' | 'agent';
  content: string;
  timestamp: string;
  agent_source?: string;
}

export interface ConversationInfo {
  conversation_id: string;
  state: string;
  message_count: number;
}

export interface SystemStatus {
  central_brain_state: string;
  active_conversations: number;
  total_conversations: number;
  available_agents: number;
  busy_agents: number;
  error_agents: number;
  pending_requests: number;
  pending_responses: number;
  initialized: boolean;
  service_status: string;
}

export interface ApiResponse<T> {
  success: boolean;
  data?: T;
  error?: string;
}

export class MainInterfaceAgentClient {
  private baseUrl: string;

  constructor(baseUrl: string = 'http://127.0.0.1:8001') {
    this.baseUrl = baseUrl;
  }

  /**
   * Start a new conversation with the Main Interface Agent
   */
  async startConversation(): Promise<ApiResponse<{ conversation_id: string }>> {
    try {
      const response = await fetch(`${this.baseUrl}/api/v1/interface/conversations/start`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({}),
      });

      const data = await response.json();
      
      if (data.success) {
        return {
          success: true,
          data: { conversation_id: data.conversation_id }
        };
      } else {
        return {
          success: false,
          error: data.error || 'Failed to start conversation'
        };
      }
    } catch (error) {
      return {
        success: false,
        error: `Network error: ${error}`
      };
    }
  }

  /**
   * Send a message to a conversation
   */
  async sendMessage(
    conversationId: string, 
    message: string, 
    messageType: string = 'SAMPLE_INQUIRY',
    priority: string = 'MEDIUM'
  ): Promise<ApiResponse<{ messages: ConversationMessage[] }>> {
    try {
      const response = await fetch(`${this.baseUrl}/api/v1/interface/conversations/message`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          conversation_id: conversationId,
          message,
          message_type: messageType,
          priority
        }),
      });

      const data = await response.json();
      
      if (data.success) {
        return {
          success: true,
          data: { messages: data.messages || [] }
        };
      } else {
        return {
          success: false,
          error: data.error || 'Failed to send message'
        };
      }
    } catch (error) {
      return {
        success: false,
        error: `Network error: ${error}`
      };
    }
  }

  /**
   * Get all messages for a conversation
   */
  async getConversationMessages(conversationId: string): Promise<ApiResponse<{ messages: ConversationMessage[] }>> {
    try {
      const response = await fetch(`${this.baseUrl}/api/v1/interface/conversations/${conversationId}/messages`);
      const data = await response.json();
      
      if (data.success) {
        return {
          success: true,
          data: { messages: data.messages || [] }
        };
      } else {
        return {
          success: false,
          error: data.error || 'Failed to get messages'
        };
      }
    } catch (error) {
      return {
        success: false,
        error: `Network error: ${error}`
      };
    }
  }

  /**
   * Get active conversations
   */
  async getActiveConversations(): Promise<ApiResponse<{ conversations: ConversationInfo[] }>> {
    try {
      const response = await fetch(`${this.baseUrl}/api/v1/interface/conversations/active`);
      const data = await response.json();
      
      if (data.success) {
        return {
          success: true,
          data: { conversations: data.conversations || [] }
        };
      } else {
        return {
          success: false,
          error: data.error || 'Failed to get conversations'
        };
      }
    } catch (error) {
      return {
        success: false,
        error: `Network error: ${error}`
      };
    }
  }

  /**
   * Get system status
   */
  async getSystemStatus(): Promise<ApiResponse<{ status: SystemStatus }>> {
    try {
      const response = await fetch(`${this.baseUrl}/api/v1/interface/status`);
      const data = await response.json();
      
      if (data.success) {
        return {
          success: true,
          data: { status: data.status }
        };
      } else {
        return {
          success: false,
          error: data.error || 'Failed to get status'
        };
      }
    } catch (error) {
      return {
        success: false,
        error: `Network error: ${error}`
      };
    }
  }

  /**
   * Complete a conversation
   */
  async completeConversation(conversationId: string): Promise<ApiResponse<{ message: string }>> {
    try {
      const response = await fetch(`${this.baseUrl}/api/v1/interface/conversations/${conversationId}/complete`, {
        method: 'POST',
      });
      const data = await response.json();
      
      if (data.success) {
        return {
          success: true,
          data: { message: data.message }
        };
      } else {
        return {
          success: false,
          error: data.error || 'Failed to complete conversation'
        };
      }
    } catch (error) {
      return {
        success: false,
        error: `Network error: ${error}`
      };
    }
  }

  /**
   * Health check
   */
  async healthCheck(): Promise<ApiResponse<{ status: string; agent_status: string; initialized: boolean }>> {
    try {
      const response = await fetch(`${this.baseUrl}/api/v1/interface/health`);
      const data = await response.json();
      
      return {
        success: true,
        data: data
      };
    } catch (error) {
      return {
        success: false,
        error: `Network error: ${error}`
      };
    }
  }
}

// Export a default instance
export const mainInterfaceClient = new MainInterfaceAgentClient();
