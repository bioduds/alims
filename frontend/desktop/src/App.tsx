import { useState, useRef } from "react";
import "./index.css";
import SystemStatsDashboard from "./components/SystemStatsDashboard";
import VisualizationEngine from "./components/VisualizationEngine";
import MainInterfaceChat from "./components/MainInterfaceChat";

// Types
interface VisualizationData {
  type: 'line' | 'bar' | 'pie' | 'doughnut' | 'radar' | 'scatter' | 'heatmap' | 'network' | 'd3_custom' | 'plotly' | 'system_dashboard' | 'chart' | 'plot' | 'table' | 'graph' | 'text' | 'code' | 'image';
  title?: string;
  data?: any;
  config?: any;
  content?: string;
  realTimeData?: boolean;
  updateInterval?: number;
}

function App() {
  const [currentVisualization, setCurrentVisualization] = useState<VisualizationData | null>(null);

  const visualizationRef = useRef<HTMLDivElement>(null);

  const captureScreenshot = async () => {
    // Screenshot functionality can be implemented later if needed
    console.log('Screenshot capture requested');
  };

  const renderVisualization = (viz: VisualizationData) => {
    // Use the new VisualizationEngine for advanced chart types
    if (['line', 'bar', 'pie', 'doughnut', 'radar', 'scatter', 'heatmap', 'network', 'd3_custom', 'plotly', 'image'].includes(viz.type)) {
      return <VisualizationEngine visualization={viz} />;
    }

    // Legacy visualization types for backward compatibility
    switch (viz.type) {
      case 'system_dashboard':
        return <SystemStatsDashboard />;
      case 'chart':
        return (
          <div className="bg-gray-800 rounded-lg p-6 border border-gray-600">
            <h3 className="text-lg font-semibold text-blue-400 mb-4">{viz.title || 'Chart'}</h3>
            <div className="text-center text-gray-400 py-8">
              📊 Chart visualization would render here
              <br />
              <small className="text-xs">Data: {JSON.stringify(viz.data).substring(0, 100)}...</small>
            </div>
          </div>
        );
      case 'plot':
        return (
          <div className="bg-gray-800 rounded-lg p-6 border border-gray-600">
            <h3 className="text-lg font-semibold text-green-400 mb-4">{viz.title || 'Plot'}</h3>
            <div className="text-center text-gray-400 py-8">
              📈 Plot visualization would render here
              <br />
              <small className="text-xs">Data: {JSON.stringify(viz.data).substring(0, 100)}...</small>
            </div>
          </div>
        );
      case 'table':
        return (
          <div className="bg-gray-800 rounded-lg p-6 border border-gray-600">
            <h3 className="text-lg font-semibold text-purple-400 mb-4">{viz.title || 'Data Table'}</h3>
            <div className="text-center text-gray-400 py-8">
              📋 Table visualization would render here
              <br />
              <small className="text-xs">Data: {JSON.stringify(viz.data).substring(0, 100)}...</small>
            </div>
          </div>
        );
      case 'graph':
        return (
          <div className="bg-gray-800 rounded-lg p-6 border border-gray-600">
            <h3 className="text-lg font-semibold text-cyan-400 mb-4">{viz.title || 'Graph'}</h3>
            <div className="text-center text-gray-400 py-8">
              🕸️ Graph visualization would render here
              <br />
              <small className="text-xs">Data: {JSON.stringify(viz.data).substring(0, 100)}...</small>
            </div>
          </div>
        );
      case 'text':
        return (
          <div className="bg-gray-800 rounded-lg p-6 border border-gray-600">
            <h3 className="text-lg font-semibold text-gray-400 mb-4">{viz.title || 'Text Output'}</h3>
            <div className="text-gray-300 font-mono text-sm whitespace-pre-wrap">
              {viz.content || 'Text content would appear here'}
            </div>
          </div>
        );
      case 'code':
        return (
          <div className="bg-gray-800 rounded-lg p-6 border border-gray-600">
            <h3 className="text-lg font-semibold text-yellow-400 mb-4">{viz.title || 'Code Output'}</h3>
            <div className="bg-gray-900 rounded p-4 text-green-400 font-mono text-sm whitespace-pre-wrap">
              {viz.content || 'Code output would appear here'}
            </div>
          </div>
        );
      default:
        return (
          <div className="bg-gray-800 rounded-lg p-6 border border-gray-600">
            <h3 className="text-lg font-semibold text-gray-400 mb-4">Visualization</h3>
            <div className="text-center text-gray-500 py-8">
              🔮 AI-generated visualization will appear here
            </div>
          </div>
        );
    }
  };

  // Main UI
  return (
    <div className="h-screen bg-gray-900 text-white flex">
      {/* Left side - Main Interface Chat (1/3) */}
      <div className="w-96 bg-gray-800 border-r border-gray-700 flex flex-col">
        {/* Header */}
        <div className="p-4 border-b border-gray-700">
          <h2 className="text-xl font-bold text-blue-400">🔬 ALIMS Laboratory Chat</h2>
          <p className="text-sm text-gray-400">
            Intelligent chat interface powered by the Main Interface Agent
          </p>
        </div>

        {/* Chat Component */}
        <div className="flex-1 overflow-hidden">
          <MainInterfaceChat onVisualizationUpdate={setCurrentVisualization} />
        </div>
      </div>

      {/* Right side - Visualization Stage (2/3) */}
      <div className="flex-1 bg-gray-900 flex flex-col">
        {/* Stage header */}
        <div className="p-4 border-b border-gray-700 bg-gray-800/50">
          <h3 className="text-lg font-semibold text-blue-400">🎭 Laboratory Analysis Stage</h3>
          <p className="text-sm text-gray-400">
            Real-time visualization space for laboratory insights and data analysis
          </p>
        </div>
        
        {/* Main visualization area */}
        <div className="flex-1 p-6 overflow-auto" ref={visualizationRef}>
          {currentVisualization ? (
            renderVisualization(currentVisualization)
          ) : (
            <div className="h-full flex items-center justify-center">
                <div className="text-center max-w-md">
                  <div className="text-6xl text-gray-600 mb-4">🧪⚗️🔬</div>
                  <h2 className="text-2xl font-bold text-gray-400 mb-2">Ready for Laboratory Analysis</h2>
                  <p className="text-gray-500 mb-6">Ask the Main Interface Agent to create laboratory visualizations, analyze sample data, or generate LIMS insights</p>

                <div className="grid grid-cols-2 gap-4 max-w-md mx-auto text-left">
                  <div className="bg-gray-800/50 rounded-lg p-4 border border-gray-600">
                      <div className="text-blue-400 font-semibold mb-2">🧪 Sample Tracking</div>
                      <p className="text-xs text-gray-400">Sample status, chain of custody, test results</p>
                  </div>
                  <div className="bg-gray-800/50 rounded-lg p-4 border border-gray-600">
                      <div className="text-green-400 font-semibold mb-2">📈 QC Analysis</div>
                      <p className="text-xs text-gray-400">Quality control trends, method validation, statistics</p>
                  </div>
                  <div className="bg-gray-800/50 rounded-lg p-4 border border-gray-600">
                      <div className="text-purple-400 font-semibold mb-2">📋 Lab Reports</div>
                      <p className="text-xs text-gray-400">Analytical reports, compliance summaries, audit trails</p>
                  </div>
                  <div className="bg-gray-800/50 rounded-lg p-4 border border-gray-600">
                      <div className="text-yellow-400 font-semibold mb-2">⚗️ Instrument Data</div>
                      <p className="text-xs text-gray-400">Equipment utilization, calibration status, results</p>
                  </div>
                </div>
              </div>
            </div>
          )}
        </div>
        
        {/* Stage footer with quick actions */}
        <div className="p-4 border-t border-gray-700 bg-gray-800/50">
          <div className="flex space-x-2 text-xs">
            <button 
              onClick={() => setCurrentVisualization({
                type: 'chart',
                title: 'Sample Tracking Dashboard',
                data: { samples: 50, pending: 12, completed: 38 }
              })}
              className="bg-blue-600/20 hover:bg-blue-600/40 text-blue-400 px-3 py-1 rounded transition-colors"
            >
              🧪 Sample Chart
            </button>
            <button 
              onClick={() => setCurrentVisualization({
                type: 'plot',
                title: 'QC Trending Analysis',
                data: { trend: 'improving', accuracy: 95.2 }
              })}
              className="bg-green-600/20 hover:bg-green-600/40 text-green-400 px-3 py-1 rounded transition-colors"
            >
              📈 QC Analysis
            </button>
            <button 
              onClick={() => setCurrentVisualization({
                type: 'table',
                title: 'Laboratory Results',
                data: { rows: 25, columns: 8 }
              })}
              className="bg-purple-600/20 hover:bg-purple-600/40 text-purple-400 px-3 py-1 rounded transition-colors"
            >
              📋 Data Table
            </button>
            <button 
              onClick={captureScreenshot}
              className="bg-orange-600/20 hover:bg-orange-600/40 text-orange-400 px-3 py-1 rounded transition-colors"
            >
              📸 Screenshot
            </button>
            <button 
              onClick={() => setCurrentVisualization({
                type: 'system_dashboard',
                title: 'Real-Time Laboratory Performance',
                data: {},
                realTimeData: true,
                updateInterval: 3000
              })}
              className="bg-cyan-600/20 hover:bg-cyan-600/40 text-cyan-400 px-3 py-1 rounded transition-colors"
            >
              📊 Live Metrics
            </button>
            <button 
              onClick={() => setCurrentVisualization(null)}
              className="bg-gray-600/20 hover:bg-gray-600/40 text-gray-400 px-3 py-1 rounded transition-colors ml-auto"
            >
              🗑️ Clear Stage
            </button>
          </div>
        </div>
      </div>
    </div>
  );
}

export default App;
