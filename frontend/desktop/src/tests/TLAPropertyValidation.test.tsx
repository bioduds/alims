import { describe, test, expect, beforeEach } from '@jest/globals';

// Import the types and components we'll need to implement
import {
  StageComponent,
  LimsChatMessage,
  LimsStageContext,
  SystemState,
  ChatMessageType,
  LimsComponentType
} from '../types/stage';

import { LimsStageSystem } from '../components/LimsStageSystem';

/**
 * Test suite that validates the TLA+ properties from LimsStageSystem.tla
 * 
 * These tests ensure our implementation follows the mathematically verified
 * specification and maintains all safety invariants.
 */
describe('TLA+ Property Validation', () => {
  let stageSystem: LimsStageSystem;
  
  beforeEach(() => {
    // Setup for each test - creates a fresh LimsStageSystem instance
    stageSystem = new LimsStageSystem();
  });
  
  // Helper function to create properly typed test messages
  const createTestMessage = (messageType: ChatMessageType, id: string = `msg_${Date.now()}`, content: string = `Test ${messageType} message`): LimsChatMessage => ({
    id,
    role: 'user',
    content,
    type: messageType,
    timestamp: new Date(),
    limsType: messageType,
    triggeredComponents: []
  });
  
  // ========================================
  // TLA+ Safety Property Tests  
  // ========================================
  
  test('TypeInvariant - all variables maintain correct types', () => {
    // Initial state should satisfy type invariant
    expect(Array.isArray(stageSystem.getActiveComponents())).toBe(true);
    expect(Array.isArray(stageSystem.getChatHistory())).toBe(true);
    expect(typeof stageSystem.getStageContext()).toBe('object');
    expect(['INITIALIZING', 'READY', 'PROCESSING_CHAT', 'UPDATING_STAGE', 'ERROR', 'MAINTENANCE'])
      .toContain(stageSystem.getSystemState());
    
    // After initialization, types should still be correct
    stageSystem.completeInitialization();
    expect(Array.isArray(stageSystem.getActiveComponents())).toBe(true);
    expect(stageSystem.getSystemState()).toBe('READY');
  });
  
  test('ComponentLimit - never exceed MAX_COMPONENTS (3)', () => {
    const MAX_COMPONENTS = 3;
    
    // Process multiple messages that would create many components
    const messages: LimsChatMessage[] = [
      { 
        id: 'msg1', 
        role: 'user',
        content: 'sample test', 
        timestamp: new Date(1), 
        limsType: 'SAMPLE_INQUIRY',
        triggeredComponents: [] 
      },
      { 
        id: 'msg2', 
        role: 'user',
        content: 'test request', 
        timestamp: new Date(2), 
        limsType: 'TEST_REQUEST',
        triggeredComponents: [] 
      },
      { 
        id: 'msg3', 
        role: 'user',
        content: 'knowledge query', 
        timestamp: new Date(3), 
        limsType: 'KNOWLEDGE_QUERY',
        triggeredComponents: [] 
      },
      { 
        id: 'msg4', 
        role: 'user',
        content: 'general query', 
        timestamp: new Date(4), 
        limsType: 'GENERAL_QUERY',
        triggeredComponents: [] 
      },
    ];
    
    stageSystem.completeInitialization();
    
    for (const msg of messages) {
      stageSystem.processChatMessage(msg);
      stageSystem.updateStageFromChat(msg);
      stageSystem.completeStageUpdate();
      
      // Check component limit is never exceeded
      expect(stageSystem.getActiveComponents().length).toBeLessThanOrEqual(MAX_COMPONENTS);
    }
  });
  
  test('ChatHistoryLimit - never exceed MAX_CHAT_HISTORY (5)', () => {
    const MAX_CHAT_HISTORY = 5;
    
    stageSystem.completeInitialization();
    
    // Send more messages than the limit
    for (let i = 0; i < 10; i++) {
      const msg: LimsChatMessage = {
        id: `msg${i}`,
        role: 'user',
        content: `test ${i}`,
        type: 'GENERAL_QUERY',
        timestamp: new Date(i + 1),
        limsType: 'GENERAL_QUERY',
        triggeredComponents: []
      };
      
      // Complete full workflow
      stageSystem.processChatMessage(msg);
      stageSystem.updateStageFromChat(msg);
      stageSystem.completeStageUpdate();
      
      // Check history limit is never exceeded  
      expect(stageSystem.getChatHistory().length).toBeLessThanOrEqual(MAX_CHAT_HISTORY);
    }
  });
  
  test('ValidActiveComponents - all components have valid LIMS types', () => {
    const validTypes: LimsComponentType[] = ['SAMPLE_TRACKER', 'TEST_CATALOG', 'KNOWLEDGE_BASE'];
    
    stageSystem.completeInitialization();
    
    const msg: LimsChatMessage = {
      id: 'msg1',
      role: 'user',
      content: 'test',
      timestamp: new Date(1),
      limsType: 'SAMPLE_INQUIRY',
      triggeredComponents: []
    };
    stageSystem.processChatMessage(msg);
    stageSystem.updateStageFromChat(msg);
    
    // All components should have valid types - checking against stage component types
    const activeComponents = stageSystem.getActiveComponents();
    for (const component of activeComponents) {
      // Map back to LIMS types for validation
      const limsType = mapStageToLimsType(component.type);
      expect(validTypes).toContain(limsType);
    }
  });
  
  test('ValidSystemState - system state is always valid', () => {
    const validStates: SystemState[] = [
      'INITIALIZING', 'READY', 'PROCESSING_CHAT', 'UPDATING_STAGE', 'ERROR', 'MAINTENANCE'
    ];
    
    // Check initial state
    expect(validStates).toContain(stageSystem.getSystemState());
    
    // Check after state transitions
    stageSystem.completeInitialization();
    expect(validStates).toContain(stageSystem.getSystemState());
    
    const msg: LimsChatMessage = {
      id: 'msg1',
      role: 'user',
      content: 'test',
      timestamp: new Date(1),
      limsType: 'SAMPLE_INQUIRY',
      triggeredComponents: []
    };
    stageSystem.processChatMessage(msg);
    expect(validStates).toContain(stageSystem.getSystemState());
    
    stageSystem.updateStageFromChat(msg);
    expect(validStates).toContain(stageSystem.getSystemState());
  });
  
  // ========================================
  // Core Business Logic Tests (TLA+ Derived)
  // ========================================
  
  test('ChatAlwaysTriggersStageUpdate - core rule validation', () => {
    stageSystem.completeInitialization();
    
    const initialComponentCount = stageSystem.getActiveComponents().length;
    
    const msg: LimsChatMessage = {
      id: 'msg1',
      role: 'user',
      content: 'sample inquiry',
      timestamp: new Date(1),
      limsType: 'SAMPLE_INQUIRY',
      triggeredComponents: []
    };
    stageSystem.processChatMessage(msg);
    stageSystem.updateStageFromChat(msg);
    
    // Stage must have been updated with new components
    expect(stageSystem.getActiveComponents().length).toBeGreaterThan(initialComponentCount);
    
    // Verify correct component type was added
    const componentTypes = stageSystem.getActiveComponents().map((comp: StageComponent) => comp.type);
    expect(componentTypes).toContain('SampleTracker');
  });
  
  test('DetermineComponentsForMessage - chat to stage mapping rules', () => {
    const testCases: Array<[ChatMessageType, LimsComponentType[]]> = [
      ['SAMPLE_INQUIRY', ['SAMPLE_TRACKER']],
      ['TEST_REQUEST', ['TEST_CATALOG']],
      ['KNOWLEDGE_QUERY', ['KNOWLEDGE_BASE']],
      ['GENERAL_QUERY', ['KNOWLEDGE_BASE']],
    ];
    
    stageSystem.completeInitialization();
    
    for (const [msgType, expectedComponents] of testCases) {
      // Clear components for clean test
      stageSystem.clearActiveComponents();
      
      const msg: LimsChatMessage = {
        id: `msg_${msgType}`,
        role: 'user',
        content: 'test',
        type: msgType,
        timestamp: new Date(1),
        limsType: msgType,
        triggeredComponents: []
      };
      
      // Complete full workflow
      stageSystem.processChatMessage(msg);
      stageSystem.updateStageFromChat(msg);
      stageSystem.completeStageUpdate();
      
      // Check that correct component types were added
      const actualTypes = stageSystem.getActiveComponents().map((comp: StageComponent) => {
        return mapStageToLimsType(comp.type);
      });
      for (const expectedType of expectedComponents) {
        expect(actualTypes).toContain(expectedType);
      }
    }
  });
  
  test('Valid state machine transitions', () => {
    // INITIALIZING -> READY
    expect(stageSystem.getSystemState()).toBe('INITIALIZING');
    stageSystem.completeInitialization();
    expect(stageSystem.getSystemState()).toBe('READY');
    
    // READY -> PROCESSING_CHAT
    const msg: LimsChatMessage = {
      id: 'msg1',
      role: 'user',
      content: 'test',
      timestamp: new Date(1),
      limsType: 'SAMPLE_INQUIRY',
      triggeredComponents: []
    };
    stageSystem.processChatMessage(msg);
    expect(stageSystem.getSystemState()).toBe('PROCESSING_CHAT');
    
    // PROCESSING_CHAT -> UPDATING_STAGE
    stageSystem.updateStageFromChat(msg);
    expect(stageSystem.getSystemState()).toBe('UPDATING_STAGE');
    
    // UPDATING_STAGE -> READY
    stageSystem.completeStageUpdate();
    expect(stageSystem.getSystemState()).toBe('READY');
  });
  
  test('Error handling and recovery - CanAlwaysRecover', () => {
    stageSystem.completeInitialization();
    
    // Trigger error condition
    stageSystem.handleError();
    expect(stageSystem.getSystemState()).toBe('ERROR');
    
    // System should be able to recover
    stageSystem.recoverFromError();
    expect(stageSystem.getSystemState()).toBe('READY');
  });
  
  test('Component removal functionality', () => {
    stageSystem.completeInitialization();
    
    // Add a component
    const msg: LimsChatMessage = {
      id: 'msg1',
      role: 'user',
      content: 'test',
      timestamp: new Date(1),
      limsType: 'SAMPLE_INQUIRY',
      triggeredComponents: []
    };
    stageSystem.processChatMessage(msg);
    stageSystem.updateStageFromChat(msg);
    stageSystem.completeStageUpdate();
    
    const initialCount = stageSystem.getActiveComponents().length;
    expect(initialCount).toBeGreaterThan(0);
    
    // Remove a component
    const componentToRemove = stageSystem.getActiveComponents()[0];
    stageSystem.removeComponent(componentToRemove.id);
    
    // Verify removal
    expect(stageSystem.getActiveComponents().length).toBe(initialCount - 1);
    
    // System state should remain valid
    expect(stageSystem.getSystemState()).toBe('READY');
  });
  
  // ========================================
  // Integration Tests
  // ========================================
  
  test('Full chat to stage workflow - end to end', async () => {
    // Start from initial state
    expect(stageSystem.getSystemState()).toBe('INITIALIZING');
    
    // Initialize system
    stageSystem.completeInitialization();
    expect(stageSystem.getSystemState()).toBe('READY');
    
    // Process chat message
    const msg: LimsChatMessage = {
      id: 'msg1',
      role: 'user',
      content: 'I need to track a blood sample',
      timestamp: new Date(1),
      limsType: 'SAMPLE_INQUIRY',
      triggeredComponents: []
    };
    stageSystem.processChatMessage(msg);
    expect(stageSystem.getSystemState()).toBe('PROCESSING_CHAT');
    expect(stageSystem.getChatHistory()).toContainEqual(msg);
    
    // Update stage
    stageSystem.updateStageFromChat(msg);
    expect(stageSystem.getSystemState()).toBe('UPDATING_STAGE');
    
    // Verify correct component was added
    const componentTypes = stageSystem.getActiveComponents().map((comp: StageComponent) => comp.type);
    expect(componentTypes).toContain('SampleTracker');
    
    // Complete update
    stageSystem.completeStageUpdate();
    expect(stageSystem.getSystemState()).toBe('READY');
    
    // System is ready for next interaction
    expect(stageSystem.getActiveComponents().length).toBeGreaterThan(0);
    expect(stageSystem.getChatHistory().length).toBe(1);
  });
  
  test('Multiple message types workflow', () => {
    stageSystem.completeInitialization();
    
    const messages: LimsChatMessage[] = [
      { 
        id: 'msg1', 
        role: 'user',
        content: 'track sample', 
        timestamp: new Date(1), 
        limsType: 'SAMPLE_INQUIRY',
        triggeredComponents: [] 
      },
      { 
        id: 'msg2', 
        role: 'user',
        content: 'available tests', 
        timestamp: new Date(2), 
        limsType: 'TEST_REQUEST',
        triggeredComponents: [] 
      },
      { 
        id: 'msg3', 
        role: 'user',
        content: 'protocol info', 
        timestamp: new Date(3), 
        limsType: 'KNOWLEDGE_QUERY',
        triggeredComponents: [] 
      },
    ];
    
    for (const msg of messages) {
      const initialComponents = stageSystem.getActiveComponents().length;
      
      // Process message
      stageSystem.processChatMessage(msg);
      stageSystem.updateStageFromChat(msg);
      stageSystem.completeStageUpdate();
      
      // Each message should add components (or at least not reduce them)
      expect(stageSystem.getActiveComponents().length).toBeGreaterThanOrEqual(initialComponents);
      
      // System should return to READY
      expect(stageSystem.getSystemState()).toBe('READY');
    }
    
    // All messages should be in history
    expect(stageSystem.getChatHistory().length).toBe(messages.length);
    
    // Should have components from all message types
    const componentTypes = stageSystem.getActiveComponents().map((comp: StageComponent) => comp.type);
    const expectedTypes = ['SampleTracker', 'TestCatalog', 'KnowledgeExplorer'];
    for (const expectedType of expectedTypes) {
      expect(componentTypes).toContain(expectedType);
    }
  });
});

// Helper function to map stage component types back to LIMS types for validation
function mapStageToLimsType(stageType: string): LimsComponentType {
  switch (stageType) {
    case 'SampleTracker':
      return 'SAMPLE_TRACKER';
    case 'TestCatalog':
      return 'TEST_CATALOG';
    case 'KnowledgeExplorer':
      return 'KNOWLEDGE_BASE';
    default:
      return 'KNOWLEDGE_BASE';
  }
}
