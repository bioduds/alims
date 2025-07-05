import '@testing-library/jest-dom';

// Mock window.limsStageSystem for tests
declare global {
  interface Window {
    limsStageSystem?: {
      sendMessage: (content: string, explicitType?: string) => void;
    };
  }
}

// Mock Tauri APIs
global.window = Object.create(window);
Object.defineProperty(window, 'matchMedia', {
  writable: true,
  value: jest.fn().mockImplementation(query => ({
    matches: false,
    media: query,
    onchange: null,
    addListener: jest.fn(), // deprecated
    removeListener: jest.fn(), // deprecated
    addEventListener: jest.fn(),
    removeEventListener: jest.fn(),
    dispatchEvent: jest.fn(),
  })),
});

// Mock ResizeObserver
global.ResizeObserver = jest.fn().mockImplementation(() => ({
  observe: jest.fn(),
  unobserve: jest.fn(),
  disconnect: jest.fn(),
}));
