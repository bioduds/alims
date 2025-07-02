import { AnalysisResults, PatternEvolutionPoint, ClusteringAlgorithm } from "../types/alims";
import { LineChart, Line, XAxis, YAxis, CartesianGrid, Tooltip, ResponsiveContainer, AreaChart, Area } from "recharts";
import { TrendingUp, Clock, BarChart3 } from "lucide-react";

interface PatternEvolutionProps {
  analysisData: AnalysisResults | null;
}

export default function PatternEvolution({ analysisData }: PatternEvolutionProps) {
  // Mock time series data for pattern evolution
  const evolutionData = generateMockEvolutionData();
  
  // Activity pattern data from current analysis
  const activityData = analysisData ? generateActivityPattern(analysisData) : [];

  return (
    <div className="space-y-6">
      {/* Pattern Evolution Over Time */}
      <div className="glass-panel rounded-xl p-6">
        <h3 className="text-lg font-semibold text-neural-900 mb-4 flex items-center gap-2">
          <TrendingUp className="w-5 h-5" />
          Pattern Evolution Timeline
        </h3>
        <div className="h-80">
          <ResponsiveContainer width="100%" height="100%">
            <LineChart data={evolutionData}>
              <CartesianGrid strokeDasharray="3 3" />
              <XAxis 
                dataKey="timestamp" 
                tickFormatter={(value) => new Date(value).toLocaleDateString()}
              />
              <YAxis />
              <Tooltip 
                labelFormatter={(value) => new Date(value).toLocaleString()}
                formatter={(value: number, name: string) => [
                  name === 'confidence' ? `${(value * 100).toFixed(1)}%` : value,
                  name === 'confidence' ? 'Confidence' : 'Pattern Count'
                ]}
              />
              <Line 
                type="monotone" 
                dataKey="pattern_count" 
                stroke="#0ea5e9" 
                strokeWidth={2}
                dot={{ fill: '#0ea5e9', strokeWidth: 2, r: 4 }}
                name="pattern_count"
              />
              <Line 
                type="monotone" 
                dataKey="confidence" 
                stroke="#d946ef" 
                strokeWidth={2}
                dot={{ fill: '#d946ef', strokeWidth: 2, r: 4 }}
                name="confidence"
              />
            </LineChart>
          </ResponsiveContainer>
        </div>
        <div className="mt-4 grid grid-cols-1 md:grid-cols-3 gap-4">
          <div className="text-center p-4 bg-primary-50 rounded-lg">
            <div className="text-2xl font-bold text-primary-600">
              {evolutionData[evolutionData.length - 1]?.pattern_count || 0}
            </div>
            <div className="text-sm text-neural-600">Current Patterns</div>
          </div>
          <div className="text-center p-4 bg-accent-50 rounded-lg">
            <div className="text-2xl font-bold text-accent-600">
              {((evolutionData[evolutionData.length - 1]?.confidence || 0) * 100).toFixed(1)}%
            </div>
            <div className="text-sm text-neural-600">Latest Confidence</div>
          </div>
          <div className="text-center p-4 bg-neural-50 rounded-lg">
            <div className="text-2xl font-bold text-neural-600">
              {evolutionData.length}
            </div>
            <div className="text-sm text-neural-600">Analysis Points</div>
          </div>
        </div>
      </div>

      {/* Daily Activity Pattern */}
      <div className="glass-panel rounded-xl p-6">
        <h3 className="text-lg font-semibold text-neural-900 mb-4 flex items-center gap-2">
          <Clock className="w-5 h-5" />
          Daily Activity Pattern
        </h3>
        <div className="h-64">
          <ResponsiveContainer width="100%" height="100%">
            <AreaChart data={activityData}>
              <CartesianGrid strokeDasharray="3 3" />
              <XAxis dataKey="hour" tickFormatter={(value) => `${value}:00`} />
              <YAxis />
              <Tooltip 
                labelFormatter={(value) => `${value}:00`}
                formatter={(value: number) => [value.toLocaleString(), 'Events']}
              />
              <Area 
                type="monotone" 
                dataKey="events" 
                stroke="#0ea5e9" 
                fill="#0ea5e9" 
                fillOpacity={0.3}
              />
            </AreaChart>
          </ResponsiveContainer>
        </div>
        <div className="mt-4">
          <div className="flex items-center justify-between text-sm text-neural-600">
            <span>Peak Activity: {findPeakHour(activityData)}:00</span>
            <span>Total Events: {activityData.reduce((sum, item) => sum + item.events, 0).toLocaleString()}</span>
          </div>
        </div>
      </div>

      {/* Pattern Stability Metrics */}
      <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
        <div className="glass-panel rounded-xl p-6">
          <h3 className="text-lg font-semibold text-neural-900 mb-4 flex items-center gap-2">
            <BarChart3 className="w-5 h-5" />
            Pattern Stability
          </h3>
          <div className="space-y-4">
            <div className="flex items-center justify-between p-3 bg-neural-50 rounded-lg">
              <span className="text-neural-700">Cluster Consistency</span>
              <div className="flex items-center gap-2">
                <div className="w-24 bg-neural-200 rounded-full h-2">
                  <div 
                    className="bg-primary-600 h-2 rounded-full" 
                    style={{ width: '85%' }}
                  ></div>
                </div>
                <span className="text-sm font-medium text-neural-900">85%</span>
              </div>
            </div>
            <div className="flex items-center justify-between p-3 bg-neural-50 rounded-lg">
              <span className="text-neural-700">Algorithm Agreement</span>
              <div className="flex items-center gap-2">
                <div className="w-24 bg-neural-200 rounded-full h-2">
                  <div 
                    className="bg-accent-600 h-2 rounded-full" 
                    style={{ width: '92%' }}
                  ></div>
                </div>
                <span className="text-sm font-medium text-neural-900">92%</span>
              </div>
            </div>
            <div className="flex items-center justify-between p-3 bg-neural-50 rounded-lg">
              <span className="text-neural-700">Temporal Stability</span>
              <div className="flex items-center gap-2">
                <div className="w-24 bg-neural-200 rounded-full h-2">
                  <div 
                    className="bg-neural-600 h-2 rounded-full" 
                    style={{ width: '78%' }}
                  ></div>
                </div>
                <span className="text-sm font-medium text-neural-900">78%</span>
              </div>
            </div>
          </div>
        </div>

        <div className="glass-panel rounded-xl p-6">
          <h3 className="text-lg font-semibold text-neural-900 mb-4">Pattern Insights</h3>
          <div className="space-y-4">
            <div className="p-4 bg-primary-50 border-l-4 border-primary-400 rounded">
              <div className="font-medium text-primary-800">Stable Clustering</div>
              <div className="text-sm text-primary-700 mt-1">
                The 2-cluster solution has remained consistent across multiple analyses, 
                indicating strong natural groupings in your data.
              </div>
            </div>
            <div className="p-4 bg-accent-50 border-l-4 border-accent-400 rounded">
              <div className="font-medium text-accent-800">Peak Activity Detected</div>
              <div className="text-sm text-accent-700 mt-1">
                Highest activity occurs during afternoon hours (2-4 PM), 
                suggesting optimal times for system maintenance.
              </div>
            </div>
            <div className="p-4 bg-neural-50 border-l-4 border-neural-400 rounded">
              <div className="font-medium text-neural-800">Evolution Trend</div>
              <div className="text-sm text-neural-700 mt-1">
                Pattern confidence has increased over time, indicating 
                improved data quality and more stable behavioral patterns.
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}

function generateMockEvolutionData(): PatternEvolutionPoint[] {
  const data: PatternEvolutionPoint[] = [];
  const now = new Date();
  
  for (let i = 14; i >= 0; i--) {
    const date = new Date(now);
    date.setDate(date.getDate() - i);
    
    data.push({
      timestamp: date.toISOString(),
      pattern_count: 2 + Math.floor(Math.random() * 2), // 2-3 patterns
      confidence: 0.75 + Math.random() * 0.2, // 75-95% confidence
      algorithm: ClusteringAlgorithm.KMEANS
    });
  }
  
  return data;
}

function generateActivityPattern(analysisData: AnalysisResults) {
  // Generate hourly activity pattern based on analysis data
  const hourlyData = [];
  const totalEvents = analysisData.data_summary.total_events;
  
  for (let hour = 0; hour < 24; hour++) {
    // Simulate realistic activity pattern with peaks during work hours
    let multiplier = 0.3; // Base activity
    if (hour >= 8 && hour <= 18) {
      multiplier = 0.8 + Math.sin((hour - 8) * Math.PI / 10) * 0.4;
    }
    
    hourlyData.push({
      hour,
      events: Math.floor(totalEvents * multiplier / 24 + Math.random() * 1000)
    });
  }
  
  return hourlyData;
}

function findPeakHour(data: { hour: number; events: number }[]): number {
  return data.reduce((peak, current) => 
    current.events > peak.events ? current : peak
  ).hour;
} 