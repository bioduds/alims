import React, { useState, useEffect } from 'react';
import { StageComponent, ComponentData } from '../../types/stage';

interface KnowledgeItem {
  id: string;
  title: string;
  content: string;
  category: 'PROTOCOLS' | 'PROCEDURES' | 'REFERENCES' | 'STANDARDS' | 'REGULATIONS';
  tags: string[];
  lastUpdated: string;
  relevanceScore?: number;
}

interface KnowledgeBaseProps {
  component: StageComponent;
  onAction?: (action: any) => void;
}

export const KnowledgeBaseComponent: React.FC<KnowledgeBaseProps> = ({
  component,
  onAction
}) => {
  const [knowledgeItems, setKnowledgeItems] = useState<KnowledgeItem[]>([]);
  const [selectedItem, setSelectedItem] = useState<KnowledgeItem | null>(null);
  const [searchQuery, setSearchQuery] = useState('');
  const [filterCategory, setFilterCategory] = useState<string>('all');

  useEffect(() => {
    // Initialize with sample knowledge items based on component data
    const sampleItems: KnowledgeItem[] = [
      {
        id: 'kb001',
        title: 'Sample Collection Protocols',
        content: 'Standard operating procedures for biological sample collection, including blood, urine, and tissue samples.',
        category: 'PROTOCOLS',
        tags: ['collection', 'blood', 'urine', 'tissue'],
        lastUpdated: new Date().toISOString()
      },
      {
        id: 'kb002',
        title: 'Quality Control Standards',
        content: 'Laboratory quality control standards and acceptance criteria for analytical testing.',
        category: 'STANDARDS',
        tags: ['quality', 'control', 'standards', 'acceptance'],
        lastUpdated: new Date().toISOString()
      },
      {
        id: 'kb003',
        title: 'FDA Regulations 21 CFR Part 11',
        content: 'Electronic records and signatures compliance requirements for laboratory systems.',
        category: 'REGULATIONS',
        tags: ['FDA', 'CFR', 'electronic', 'signatures'],
        lastUpdated: new Date().toISOString()
      },
      {
        id: 'kb004',
        title: 'Analytical Method Validation',
        content: 'Guidelines for validation of analytical methods including accuracy, precision, and specificity.',
        category: 'PROCEDURES',
        tags: ['validation', 'accuracy', 'precision', 'methods'],
        lastUpdated: new Date().toISOString()
      }
    ];

    // Add relevance scoring based on component context
    const itemsWithRelevance = sampleItems.map(item => ({
      ...item,
      relevanceScore: calculateRelevance(item, component.data)
    }));

    setKnowledgeItems(itemsWithRelevance.sort((a, b) => (b.relevanceScore || 0) - (a.relevanceScore || 0)));
  }, [component.data]);

  const calculateRelevance = (item: KnowledgeItem, componentData: ComponentData): number => {
    let score = 0;
    
    // Score based on component data properties
    const dataString = JSON.stringify(componentData).toLowerCase();
    item.tags.forEach(tag => {
      if (dataString.includes(tag.toLowerCase())) {
        score += 10;
      }
    });
    if (dataString.includes(item.title.toLowerCase())) {
      score += 20;
    }

    return score;
  };

  const filteredItems = knowledgeItems.filter(item => {
    const matchesSearch = searchQuery === '' || 
      item.title.toLowerCase().includes(searchQuery.toLowerCase()) ||
      item.content.toLowerCase().includes(searchQuery.toLowerCase()) ||
      item.tags.some(tag => tag.toLowerCase().includes(searchQuery.toLowerCase()));
    
    const matchesCategory = filterCategory === 'all' || item.category === filterCategory;
    
    return matchesSearch && matchesCategory;
  });

  const getCategoryColor = (category: KnowledgeItem['category']) => {
    switch (category) {
      case 'PROTOCOLS': return 'bg-blue-100 text-blue-800';
      case 'PROCEDURES': return 'bg-green-100 text-green-800';
      case 'REFERENCES': return 'bg-purple-100 text-purple-800';
      case 'STANDARDS': return 'bg-orange-100 text-orange-800';
      case 'REGULATIONS': return 'bg-red-100 text-red-800';
      default: return 'bg-gray-100 text-gray-800';
    }
  };

  const handleItemSelect = (item: KnowledgeItem) => {
    setSelectedItem(item);
    if (onAction) {
      onAction({
        type: 'KNOWLEDGE_ITEM_SELECTED',
        data: { itemId: item.id, title: item.title }
      });
    }
  };

  return (
    <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-4">
      <div className="flex items-center justify-between mb-4">
        <h3 className="text-lg font-semibold text-gray-900 flex items-center">
          <span className="mr-2">📚</span>
          Knowledge Base
        </h3>
        <span className="text-sm text-gray-500">
          {filteredItems.length} items
        </span>
      </div>

      {/* Search and Filter Controls */}
      <div className="mb-4 space-y-3">
        <div>
          <input
            type="text"
            placeholder="Search knowledge base..."
            value={searchQuery}
            onChange={(e) => setSearchQuery(e.target.value)}
            className="w-full px-3 py-2 border border-gray-300 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500"
          />
        </div>
        
        <div>
          <select
            value={filterCategory}
            onChange={(e) => setFilterCategory(e.target.value)}
            className="w-full px-3 py-2 border border-gray-300 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500"
          >
            <option value="all">All Categories</option>
            <option value="PROTOCOLS">Protocols</option>
            <option value="PROCEDURES">Procedures</option>
            <option value="REFERENCES">References</option>
            <option value="STANDARDS">Standards</option>
            <option value="REGULATIONS">Regulations</option>
          </select>
        </div>
      </div>

      {/* Knowledge Items List */}
      <div className="space-y-3 max-h-80 overflow-y-auto">
        {filteredItems.map((item) => (
          <div
            key={item.id}
            className={`p-3 border rounded-lg cursor-pointer transition-colors ${
              selectedItem?.id === item.id
                ? 'border-blue-500 bg-blue-50'
                : 'border-gray-200 hover:border-gray-300'
            }`}
            onClick={() => handleItemSelect(item)}
          >
            <div className="flex items-start justify-between mb-2">
              <h4 className="font-medium text-gray-900 flex-1">{item.title}</h4>
              <span className={`px-2 py-1 rounded-full text-xs font-medium ${getCategoryColor(item.category)}`}>
                {item.category}
              </span>
            </div>
            
            <p className="text-sm text-gray-600 mb-2 line-clamp-2">
              {item.content}
            </p>
            
            <div className="flex items-center justify-between">
              <div className="flex flex-wrap gap-1">
                {item.tags.slice(0, 3).map((tag) => (
                  <span
                    key={tag}
                    className="px-2 py-1 bg-gray-100 text-gray-600 rounded-full text-xs"
                  >
                    #{tag}
                  </span>
                ))}
                {item.tags.length > 3 && (
                  <span className="text-xs text-gray-500">
                    +{item.tags.length - 3} more
                  </span>
                )}
              </div>
              
              {item.relevanceScore && item.relevanceScore > 0 && (
                <div className="flex items-center text-xs text-green-600">
                  <span className="mr-1">⭐</span>
                  Relevant
                </div>
              )}
            </div>
          </div>
        ))}
      </div>

      {filteredItems.length === 0 && (
        <div className="text-center py-8 text-gray-500">
          <span className="block text-2xl mb-2">🔍</span>
          No knowledge items found
          {searchQuery && (
            <div className="text-sm">
              Try adjusting your search terms or category filter
            </div>
          )}
        </div>
      )}

      {/* Selected Item Details */}
      {selectedItem && (
        <div className="mt-4 p-3 bg-gray-50 rounded-lg">
          <div className="flex items-center justify-between mb-2">
            <h4 className="font-medium text-gray-900">{selectedItem.title}</h4>
            <button
              onClick={() => setSelectedItem(null)}
              className="text-gray-400 hover:text-gray-600"
            >
              ✕
            </button>
          </div>
          <p className="text-sm text-gray-700 mb-3">{selectedItem.content}</p>
          <div className="flex items-center justify-between text-xs text-gray-500">
            <div className="flex flex-wrap gap-1">
              {selectedItem.tags.map((tag) => (
                <span key={tag} className="px-2 py-1 bg-white rounded-full">
                  #{tag}
                </span>
              ))}
            </div>
            <span>Updated: {new Date(selectedItem.lastUpdated).toLocaleDateString()}</span>
          </div>
        </div>
      )}
    </div>
  );
};

export default KnowledgeBaseComponent;
