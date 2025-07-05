import { useState, useEffect, useCallback, useRef } from 'react';
import { 
  StageComponent, 
  StageComponentType,
  LimsChatMessage,
  LimsStageContext,
  SystemState,
  ChatMessageType,
  LimsComponentType,
  ComponentData,
  ComponentState
} from '../types/stage';

// ============================================================================
// TLA+ VALIDATED LIMS STAGE SYSTEM IMPLEMENTATION
// ============================================================================

/**
 * LimsStageSystem - Implementation following the TLA+ validated specification
 * 
 * This class implements the mathematically verified LIMS stage system that
 * ensures every chat message triggers appropriate stage component updates.
 * 
 * Key TLA+ Properties Maintained:
 * - ChatAlwaysTriggersStageUpdate: Every chat MUST update stage
 * - ComponentLimit: Never exceed MAX_COMPONENTS (3)
 * - ChatHistoryLimit: Never exceed MAX_CHAT_HISTORY (5)
 * - ValidSystemState: Always maintain valid state transitions
 */
export class LimsStageSystem {
  private activeComponents: StageComponent[] = [];
  private chatHistory: LimsChatMessage[] = [];
  private stageContext: LimsStageContext;
  private systemState: SystemState = 'INITIALIZING';
  
  // TLA+ validated constants
  private readonly MAX_COMPONENTS = 3;
  private readonly MAX_CHAT_HISTORY = 5;
  
  // Event callbacks for React integration
  private onStateChangeCallback?: (state: SystemState) => void;
  private onComponentsChangeCallback?: (components: StageComponent[]) => void;
  private onChatHistoryChangeCallback?: (history: LimsChatMessage[]) => void;

  constructor() {
    this.stageContext = {
      currentFocus: 'GENERAL',
      activeWorkflow: 'NONE',
      knowledgeBase: new Set<string>(),
      userPreferences: 'DEFAULT'
    };
  }

  // ========================================
  // TLA+ STATE MACHINE IMPLEMENTATION
  // ========================================

  /**
   * TLA+ Action: CompleteInitialization
   * Transitions from INITIALIZING to READY state
   */
  completeInitialization(): void {
    if (this.systemState !== 'INITIALIZING') {
      throw new Error(`Invalid state transition: Cannot initialize from ${this.systemState}`);
    }
    
    this.systemState = 'READY';
    this.notifyStateChange();
  }

  /**
   * TLA+ Action: ProcessChatMessage (synchronous version for testing)
   * Transitions from READY to PROCESSING_CHAT state
   */
  processChatMessage(message: LimsChatMessage): void {
    this.processChatMessageSync(message);
  }

  /**
   * TLA+ Action: ProcessChatMessage (synchronous version)
   * Transitions from READY to PROCESSING_CHAT state
   */
  processChatMessageSync(message: LimsChatMessage): void {
    if (this.systemState !== 'READY') {
      throw new Error(`Invalid state transition: Cannot process chat from ${this.systemState}`);
    }

    this.systemState = 'PROCESSING_CHAT';
    
    // Add to chat history with TLA+ validated limit
    this.chatHistory.push(message);
    if (this.chatHistory.length > this.MAX_CHAT_HISTORY) {
      this.chatHistory.shift(); // Remove oldest message
    }
    
    this.notifyStateChange();
    this.notifyChatHistoryChange();
  }

  /**
   * TLA+ Action: UpdateStageFromChat
   * Transitions from PROCESSING_CHAT to UPDATING_STAGE state
   * 
   * CORE TLA+ RULE: This method MUST add components to the stage
   */
  updateStageFromChat(message: LimsChatMessage): void {
    if (this.systemState !== 'PROCESSING_CHAT') {
      throw new Error(`Invalid state transition: Cannot update stage from ${this.systemState}`);
    }

    this.systemState = 'UPDATING_STAGE';
    
    // TLA+ validated component determination
    const requiredComponentTypes = this.determineComponentsForMessage(message.limsType || 'GENERAL_QUERY');
    
    // Create new components following TLA+ specification
    const newComponents: StageComponent[] = requiredComponentTypes.map((componentType) => ({
      id: `${message.id}_${componentType}`,
      type: this.mapLimsToStageType(componentType),
      state: 'Active' as ComponentState,
      priority: 1,
      data: this.createComponentData(componentType, message),
      metadata: {
        lastUpdated: new Date(),
        relevanceScore: 0.9,
        userInteractions: 0
      }
    }));

    // Add components while respecting TLA+ limit
    this.addComponentsWithLimit(newComponents);
    
    // Update stage context
    this.stageContext = {
      ...this.stageContext,
      currentFocus: message.limsType || 'GENERAL_QUERY',
      knowledgeBase: new Set([...this.stageContext.knowledgeBase, message.content])
    };

    this.notifyStateChange();
    this.notifyComponentsChange();
  }

  /**
   * TLA+ Action: CompleteStageUpdate
   * Transitions from UPDATING_STAGE to READY state
   */
  completeStageUpdate(): void {
    if (this.systemState !== 'UPDATING_STAGE') {
      throw new Error(`Invalid state transition: Cannot complete update from ${this.systemState}`);
    }

    this.systemState = 'READY';
    this.notifyStateChange();
  }

  /**
   * TLA+ Action: HandleError
   * Transitions from any state to ERROR state
   */
  handleError(): void {
    this.systemState = 'ERROR';
    this.notifyStateChange();
  }

  /**
   * TLA+ Action: RecoverFromError
   * Transitions from ERROR to READY state
   */
  recoverFromError(): void {
    if (this.systemState !== 'ERROR') {
      throw new Error(`Invalid state transition: Cannot recover from ${this.systemState}`);
    }

    this.systemState = 'READY';
    this.notifyStateChange();
  }

  /**
   * TLA+ Action: RemoveComponent
   * Removes a component while maintaining READY state
   */
  removeComponent(componentId: string): void {
    if (this.systemState !== 'READY') {
      throw new Error(`Invalid state: Cannot remove component from ${this.systemState}`);
    }

    const initialLength = this.activeComponents.length;
    this.activeComponents = this.activeComponents.filter(c => c.id !== componentId);
    
    if (this.activeComponents.length < initialLength) {
      this.notifyComponentsChange();
    }
  }

  // ========================================
  // TLA+ SPECIFICATION HELPER METHODS
  // ========================================

  /**
   * TLA+ Function: DetermineComponentsForMessage
   * Maps chat message types to required component types
   * This implements the validated mapping from the TLA+ specification
   */
  private determineComponentsForMessage(messageType: ChatMessageType): LimsComponentType[] {
    switch (messageType) {
      case 'SAMPLE_INQUIRY':
        return ['SAMPLE_TRACKER'];
      case 'TEST_REQUEST':
        return ['TEST_CATALOG'];
      case 'KNOWLEDGE_QUERY':
        return ['KNOWLEDGE_BASE'];
      case 'GENERAL_QUERY':
      default:
        return ['KNOWLEDGE_BASE'];
    }
  }

  /**
   * Maps LIMS component types to existing stage component types
   */
  private mapLimsToStageType(limsType: LimsComponentType): StageComponentType {
    switch (limsType) {
      case 'SAMPLE_TRACKER':
        return 'SampleTracker';
      case 'TEST_CATALOG':
        return 'TestCatalog';
      case 'KNOWLEDGE_BASE':
        return 'KnowledgeExplorer';
      default:
        return 'KnowledgeExplorer';
    }
  }

  /**
   * Creates component data based on LIMS component type and message
   */
  private createComponentData(componentType: LimsComponentType, message: LimsChatMessage): ComponentData {
    const baseData: ComponentData = {
      actions: [
        {
          id: `action_${message.id}`,
          type: 'navigate',
          label: `View ${componentType}`,
          description: `Open ${componentType} panel`,
          icon: 'view',
          priority: 'medium',
          onExecute: () => console.log(`Opening ${componentType}`)
        }
      ]
    };

    switch (componentType) {
      case 'SAMPLE_TRACKER':
        return {
          ...baseData,
          samples: [] // Would be populated with relevant samples
        };
      case 'TEST_CATALOG':
        return {
          ...baseData,
          tests: [] // Would be populated with relevant tests
        };
      case 'KNOWLEDGE_BASE':
        return {
          ...baseData,
          knowledge: [] // Would be populated with relevant knowledge items
        };
      default:
        return baseData;
    }
  }

  /**
   * Adds components while respecting TLA+ MAX_COMPONENTS limit
   */
  private addComponentsWithLimit(newComponents: StageComponent[]): void {
    // Add new components
    this.activeComponents.push(...newComponents);
    
    // Enforce TLA+ component limit
    while (this.activeComponents.length > this.MAX_COMPONENTS) {
      // Remove oldest component (FIFO)
      this.activeComponents.shift();
    }
  }

  // ========================================
  // PUBLIC ACCESSORS (for testing and React integration)
  // ========================================

  getActiveComponents(): StageComponent[] {
    return [...this.activeComponents];
  }

  getChatHistory(): LimsChatMessage[] {
    return [...this.chatHistory];
  }

  getStageContext(): LimsStageContext {
    return { ...this.stageContext };
  }

  getSystemState(): SystemState {
    return this.systemState;
  }

  clearActiveComponents(): void {
    this.activeComponents = [];
    this.notifyComponentsChange();
  }

  // ========================================
  // NOTIFICATION METHODS
  // ========================================

  private notifyStateChange(): void {
    if (this.onStateChangeCallback) {
      this.onStateChangeCallback(this.systemState);
    }
  }

  private notifyComponentsChange(): void {
    if (this.onComponentsChangeCallback) {
      this.onComponentsChangeCallback([...this.activeComponents]);
    }
  }

  private notifyChatHistoryChange(): void {
    if (this.onChatHistoryChangeCallback) {
      this.onChatHistoryChangeCallback([...this.chatHistory]);
    }
  }

  // ========================================
  // REACT INTEGRATION METHODS
  // ========================================

  /**
   * Set callbacks for React state updates
   */
  setEventCallbacks(
    onStateChange: (state: SystemState) => void,
    onComponentsChange: (components: StageComponent[]) => void,
    onChatHistoryChange: (history: LimsChatMessage[]) => void
  ): void {
    this.onStateChangeCallback = onStateChange;
    this.onComponentsChangeCallback = onComponentsChange;
    this.onChatHistoryChangeCallback = onChatHistoryChange;
  }

  /**
   * Initialize the system (async version for React compatibility)
   */
  async initialize(): Promise<void> {
    return new Promise((resolve) => {
      // Simulate initialization delay
      setTimeout(() => {
        this.completeInitialization();
        resolve();
      }, 100);
    });
  }

  /**
   * Process chat message (async version for React compatibility)
   */
  async processChatMessageAsync(message: LimsChatMessage): Promise<void> {
    return new Promise((resolve, reject) => {
      try {
        // Call the synchronous version
        this.processChatMessageSync(message);
        
        // Update stage from chat
        this.updateStageFromChat(message);
        
        // Complete stage update
        this.completeStageUpdate();
        
        resolve();
      } catch (error) {
        this.handleError();
        reject(error);
      }
    });
  }
}

// ============================================================================
// REACT HOOK FOR LIMS STAGE SYSTEM
// ============================================================================

/**
 * React hook that provides a TLA+ validated LIMS stage system
 * This hook manages the stage system lifecycle and provides reactive updates
 */
export function useLimsStageSystem() {
  const [systemState, setSystemState] = useState<SystemState>('INITIALIZING');
  const [activeComponents, setActiveComponents] = useState<StageComponent[]>([]);
  const [chatHistory, setChatHistory] = useState<LimsChatMessage[]>([]);
  
  const stageSystemRef = useRef<LimsStageSystem>();

  useEffect(() => {
    // Initialize the stage system
    const stageSystem = new LimsStageSystem();
    
    // Set up event listeners
    stageSystem.setEventCallbacks(
      setSystemState,
      setActiveComponents,
      setChatHistory
    );
    
    stageSystemRef.current = stageSystem;
    
    // Complete initialization
    stageSystem.completeInitialization();
    
    return () => {
      // Cleanup if needed
    };
  }, []);

  const processChatMessage = useCallback(async (message: LimsChatMessage) => {
    if (!stageSystemRef.current) {
      return;
    }
    
    try {
      // TLA+ validated workflow: async chat processing
      await stageSystemRef.current.processChatMessageAsync(message);
    } catch (error) {
      console.error('Error processing chat message:', error);
      stageSystemRef.current.handleError();
      
      // Attempt recovery
      setTimeout(() => {
        stageSystemRef.current?.recoverFromError();
      }, 1000);
    }
  }, []);

  const removeComponent = useCallback((componentId: string) => {
    if (!stageSystemRef.current) {
      return;
    }
    stageSystemRef.current.removeComponent(componentId);
  }, []);

  return {
    systemState,
    activeComponents,
    chatHistory,
    processChatMessage,
    removeComponent,
    stageSystem: stageSystemRef.current
  };
}
