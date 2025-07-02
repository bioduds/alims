import { Recommendation } from "../types/alims";
import { AlertTriangle, CheckCircle, Info, Zap, ArrowRight, Clock } from "lucide-react";

interface RecommendationsPanelProps {
  recommendations: Recommendation[];
  analysisId: string;
}

export default function RecommendationsPanel({ recommendations, analysisId }: RecommendationsPanelProps) {
  const priorityOrder = { 'HIGH': 0, 'MEDIUM': 1, 'LOW': 2 };
  const sortedRecommendations = [...recommendations].sort((a, b) => 
    priorityOrder[a.priority as keyof typeof priorityOrder] - priorityOrder[b.priority as keyof typeof priorityOrder]
  );

  const highPriorityCount = recommendations.filter(r => r.priority === 'HIGH').length;
  const actionRequiredCount = recommendations.filter(r => r.action_required).length;

  return (
    <div className="space-y-6">
      {/* Summary Cards */}
      <div className="grid grid-cols-1 md:grid-cols-4 gap-6">
        <div className="glass-panel rounded-xl p-6">
          <div className="flex items-center gap-3">
            <div className="p-2 bg-red-100 text-red-600 rounded-lg">
              <AlertTriangle className="w-5 h-5" />
            </div>
            <div>
              <div className="text-2xl font-bold text-neural-900">{highPriorityCount}</div>
              <div className="text-sm text-neural-600">High Priority</div>
            </div>
          </div>
        </div>

        <div className="glass-panel rounded-xl p-6">
          <div className="flex items-center gap-3">
            <div className="p-2 bg-accent-100 text-accent-600 rounded-lg">
              <Zap className="w-5 h-5" />
            </div>
            <div>
              <div className="text-2xl font-bold text-neural-900">{actionRequiredCount}</div>
              <div className="text-sm text-neural-600">Action Required</div>
            </div>
          </div>
        </div>

        <div className="glass-panel rounded-xl p-6">
          <div className="flex items-center gap-3">
            <div className="p-2 bg-primary-100 text-primary-600 rounded-lg">
              <CheckCircle className="w-5 h-5" />
            </div>
            <div>
              <div className="text-2xl font-bold text-neural-900">{recommendations.length}</div>
              <div className="text-sm text-neural-600">Total Recommendations</div>
            </div>
          </div>
        </div>

        <div className="glass-panel rounded-xl p-6">
          <div className="flex items-center gap-3">
            <div className="p-2 bg-neural-100 text-neural-600 rounded-lg">
              <Clock className="w-5 h-5" />
            </div>
            <div>
              <div className="text-2xl font-bold text-neural-900">
                {Math.ceil(actionRequiredCount * 2.5)}h
              </div>
              <div className="text-sm text-neural-600">Est. Implementation</div>
            </div>
          </div>
        </div>
      </div>

      {/* Recommendations List */}
      <div className="space-y-4">
        <h3 className="text-lg font-semibold text-neural-900">Implementation Roadmap</h3>
        
        {sortedRecommendations.map((recommendation, index) => (
          <RecommendationCard 
            key={index}
            recommendation={recommendation}
            index={index}
          />
        ))}
      </div>

      {/* Implementation Timeline */}
      <div className="glass-panel rounded-xl p-6">
        <h3 className="text-lg font-semibold text-neural-900 mb-4">Suggested Implementation Timeline</h3>
        <div className="space-y-4">
          {generateTimeline(sortedRecommendations).map((phase, index) => (
            <div key={index} className="flex items-start gap-4">
              <div className="flex-shrink-0 w-8 h-8 bg-primary-600 text-white rounded-full flex items-center justify-center text-sm font-medium">
                {index + 1}
              </div>
              <div className="flex-1">
                <div className="flex items-center justify-between mb-2">
                  <h4 className="font-medium text-neural-900">{phase.title}</h4>
                  <span className="text-sm text-neural-500">{phase.duration}</span>
                </div>
                <p className="text-sm text-neural-600 mb-2">{phase.description}</p>
                <div className="flex flex-wrap gap-2">
                  {phase.recommendations.map((rec, recIndex) => (
                    <span 
                      key={recIndex}
                      className={`px-2 py-1 text-xs rounded-full ${getPriorityClasses(rec.priority).badge}`}
                    >
                      {rec.category}
                    </span>
                  ))}
                </div>
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Analysis Metadata */}
      <div className="glass-panel rounded-xl p-4 bg-neural-50">
        <div className="flex items-center justify-between text-sm text-neural-600">
          <span>Analysis ID: {analysisId}</span>
          <span>Generated: {new Date().toLocaleString()}</span>
        </div>
      </div>
    </div>
  );
}

interface RecommendationCardProps {
  recommendation: Recommendation;
  index: number;
}

function RecommendationCard({ recommendation, index }: RecommendationCardProps) {
  const priorityConfig = getPriorityClasses(recommendation.priority);

  return (
    <div className={`glass-panel rounded-xl p-6 border-l-4 ${priorityConfig.border}`}>
      <div className="flex items-start justify-between mb-3">
        <div className="flex items-center gap-3">
          <div className={`p-2 rounded-lg ${priorityConfig.iconBg}`}>
            {priorityConfig.icon}
          </div>
          <div>
            <div className="flex items-center gap-2">
              <span className={`px-2 py-1 text-xs font-medium rounded-full ${priorityConfig.badge}`}>
                {recommendation.priority}
              </span>
              <span className="text-sm text-neural-500">{recommendation.category}</span>
            </div>
          </div>
        </div>
        
        {recommendation.action_required && (
          <div className="flex items-center gap-1 text-accent-600">
            <Zap className="w-4 h-4" />
            <span className="text-xs font-medium">Action Required</span>
          </div>
        )}
      </div>

      <h4 className="font-medium text-neural-900 mb-2">
        {recommendation.message}
      </h4>

      {recommendation.technical_details && (
        <div className="bg-neural-50 rounded-lg p-3 mb-4">
          <div className="text-xs font-medium text-neural-700 mb-1">Technical Details:</div>
          <div className="text-sm text-neural-600">{recommendation.technical_details}</div>
        </div>
      )}

      <div className="flex items-center justify-between">
        <div className="text-xs text-neural-500">
          Step {index + 1} of {index + 1}
        </div>
        
        {recommendation.action_required && (
          <button className="flex items-center gap-1 px-3 py-1 bg-primary-600 text-white text-xs rounded-lg hover:bg-primary-700 transition-colors">
            Implement
            <ArrowRight className="w-3 h-3" />
          </button>
        )}
      </div>
    </div>
  );
}

function getPriorityClasses(priority: string) {
  switch (priority) {
    case 'HIGH':
      return {
        border: 'border-red-400',
        iconBg: 'bg-red-100 text-red-600',
        badge: 'bg-red-100 text-red-700',
        icon: <AlertTriangle className="w-4 h-4" />
      };
    case 'MEDIUM':
      return {
        border: 'border-accent-400',
        iconBg: 'bg-accent-100 text-accent-600',
        badge: 'bg-accent-100 text-accent-700',
        icon: <Info className="w-4 h-4" />
      };
    case 'LOW':
      return {
        border: 'border-primary-400',
        iconBg: 'bg-primary-100 text-primary-600',
        badge: 'bg-primary-100 text-primary-700',
        icon: <CheckCircle className="w-4 h-4" />
      };
    default:
      return {
        border: 'border-neural-400',
        iconBg: 'bg-neural-100 text-neural-600',
        badge: 'bg-neural-100 text-neural-700',
        icon: <Info className="w-4 h-4" />
      };
  }
}

function generateTimeline(recommendations: Recommendation[]) {
  const phases = [
    {
      title: "Phase 1: High Priority Implementation",
      duration: "Week 1-2",
      description: "Address critical architecture decisions and high-impact optimizations",
      recommendations: recommendations.filter(r => r.priority === 'HIGH')
    },
    {
      title: "Phase 2: Medium Priority Enhancements",
      duration: "Week 3-4",
      description: "Implement performance improvements and system optimizations",
      recommendations: recommendations.filter(r => r.priority === 'MEDIUM')
    },
    {
      title: "Phase 3: Low Priority Refinements",
      duration: "Week 5-6",
      description: "Fine-tune system parameters and add additional features",
      recommendations: recommendations.filter(r => r.priority === 'LOW')
    }
  ].filter(phase => phase.recommendations.length > 0);

  return phases;
} 