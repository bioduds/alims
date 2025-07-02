"""
ALims Multimodal Processing System
Handles image analysis, data processing, code analysis, and visual content generation
for Gemma 3:4b multimodal capabilities
"""

import base64
import io
import json
import logging
import os
import tempfile
from datetime import datetime
from typing import Dict, Any, List, Tuple
from pathlib import Path

import cv2
import numpy as np
import pandas as pd
from PIL import Image

logger = logging.getLogger(__name__)


class MultimodalProcessor:
    """Handles multimodal content processing for ALims AI system"""
    
    def __init__(self):
        self.supported_image_formats = {'.jpg', '.jpeg', '.png', '.bmp', '.tiff', '.webp'}
        self.supported_data_formats = {'.csv', '.json', '.xlsx', '.tsv'}
        self.supported_code_formats = {'.py', '.js', '.ts', '.html', '.css', '.yaml', '.yml', '.md'}
        self.supported_document_formats = {'.pdf', '.txt'}
        
        logger.info("MultimodalProcessor initialized")
    
    async def process_file(self, file_path: str, file_content: bytes, 
                          filename: str) -> Dict[str, Any]:
        """Process uploaded file based on its type"""
        try:
            file_ext = Path(filename).suffix.lower()
            
            if file_ext in self.supported_image_formats:
                return await self.process_image(file_content, filename)
            elif file_ext in self.supported_data_formats:
                return await self.process_data_file(file_content, filename)
            elif file_ext in self.supported_code_formats:
                return await self.process_code_file(file_content, filename)
            elif file_ext in self.supported_document_formats:
                return await self.process_document_file(file_content, filename)
            else:
                return {
                    "success": False,
                    "error": f"Unsupported file format: {file_ext}",
                    "supported_formats": {
                        "images": list(self.supported_image_formats),
                        "data": list(self.supported_data_formats),
                        "code": list(self.supported_code_formats),
                        "documents": list(self.supported_document_formats)
                    }
                }
                
        except Exception as e:
            logger.error(f"File processing error: {e}")
            return {"success": False, "error": str(e)}
    
    async def process_image(self, image_content: bytes, filename: str) -> Dict[str, Any]:
        """Process and analyze images"""
        try:
            # Convert bytes to PIL Image
            image = Image.open(io.BytesIO(image_content))
            
            # Basic image analysis
            width, height = image.size
            mode = image.mode
            format_info = image.format
            
            # Convert to OpenCV format for advanced analysis
            cv_image = cv2.cvtColor(np.array(image), cv2.COLOR_RGB2BGR)
            
            # Extract basic features
            analysis = {
                "basic_info": {
                    "filename": filename,
                    "dimensions": {"width": width, "height": height},
                    "mode": mode,
                    "format": format_info,
                    "size_bytes": len(image_content)
                },
                "visual_analysis": await self._analyze_image_content(cv_image),
                "data_extraction": await self._extract_chart_data(cv_image),
                "base64_thumbnail": self._create_thumbnail(image)
            }
            
            return {
                "success": True,
                "type": "image",
                "analysis": analysis,
                "ai_prompt": self._generate_image_analysis_prompt(analysis)
            }
            
        except Exception as e:
            logger.error(f"Image processing error: {e}")
            return {"success": False, "error": str(e)}
    
    async def process_data_file(self, file_content: bytes, filename: str) -> Dict[str, Any]:
        """Process CSV, JSON, and other data files"""
        try:
            file_ext = Path(filename).suffix.lower()
            
            if file_ext == '.csv':
                df = pd.read_csv(io.BytesIO(file_content))
            elif file_ext == '.json':
                data = json.loads(file_content.decode('utf-8'))
                df = pd.json_normalize(data) if isinstance(data, list) else pd.DataFrame([data])
            elif file_ext == '.xlsx':
                df = pd.read_excel(io.BytesIO(file_content))
            elif file_ext == '.tsv':
                df = pd.read_csv(io.BytesIO(file_content), sep='\t')
            else:
                raise ValueError(f"Unsupported data format: {file_ext}")
            
            # Data analysis with JSON-safe conversion
            analysis = {
                "basic_info": {
                    "filename": filename,
                    "rows": int(len(df)),
                    "columns": int(len(df.columns)),
                    "size_bytes": len(file_content),
                    "column_names": df.columns.tolist()
                },
                "data_types": {k: str(v) for k, v in df.dtypes.to_dict().items()},
                "summary_stats": self._convert_to_json_safe(df.describe().to_dict()) if len(df) > 0 else {},
                "missing_values": {k: int(v) for k, v in df.isnull().sum().to_dict().items()},
                "sample_data": self._convert_to_json_safe(df.head(5).to_dict('records')),
                "visualization_suggestions": self._suggest_visualizations(df)
            }
            
            return {
                "success": True,
                "type": "data",
                "analysis": analysis,
                "dataframe_info": {
                    "shape": [int(df.shape[0]), int(df.shape[1])],
                    "memory_usage": int(df.memory_usage(deep=True).sum())
                },
                "ai_prompt": self._generate_data_analysis_prompt(analysis)
            }
            
        except Exception as e:
            logger.error(f"Data processing error: {e}")
            return {"success": False, "error": str(e)}
    
    async def process_code_file(self, file_content: bytes, filename: str) -> Dict[str, Any]:
        """Process code files for analysis and documentation"""
        try:
            code = file_content.decode('utf-8')
            file_ext = Path(filename).suffix.lower()
            
            analysis = {
                "basic_info": {
                    "filename": filename,
                    "language": self._detect_language(file_ext),
                    "lines": len(code.split('\n')),
                    "size_bytes": len(file_content),
                    "extension": file_ext
                },
                "code_metrics": self._analyze_code_metrics(code, file_ext),
                "structure": self._analyze_code_structure(code, file_ext),
                "preview": code[:1000] + "..." if len(code) > 1000 else code
            }
            
            return {
                "success": True,
                "type": "code",
                "analysis": analysis,
                "ai_prompt": self._generate_code_analysis_prompt(analysis, code)
            }
            
        except Exception as e:
            logger.error(f"Code processing error: {e}")
            return {"success": False, "error": str(e)}
    
    async def process_document_file(self, file_content: bytes, filename: str) -> Dict[str, Any]:
        """Process PDF and text documents"""
        try:
            file_ext = Path(filename).suffix.lower()
            
            if file_ext == '.pdf':
                try:
                    import PyPDF2
                    pdf_reader = PyPDF2.PdfReader(io.BytesIO(file_content))
                    text_content = ""
                    for page in pdf_reader.pages:
                        text_content += page.extract_text() + "\n"
                except Exception as e:
                    logger.error(f"PDF processing error: {e}")
                    text_content = f"Error extracting text from PDF: {str(e)}"
            elif file_ext == '.txt':
                text_content = file_content.decode('utf-8')
            else:
                raise ValueError(f"Unsupported document format: {file_ext}")
            
            # Document analysis
            analysis = {
                "basic_info": {
                    "filename": filename,
                    "document_type": file_ext,
                    "size_bytes": len(file_content),
                    "character_count": len(text_content),
                    "word_count": len(text_content.split()),
                    "line_count": len(text_content.split('\n'))
                },
                "content_preview": text_content[:500] + "..." if len(text_content) > 500 else text_content,
                "content_analysis": self._analyze_document_content(text_content)
            }
            
            return {
                "success": True,
                "type": "document",
                "analysis": analysis,
                "ai_prompt": self._generate_document_analysis_prompt(analysis, text_content)
            }
            
        except Exception as e:
            logger.error(f"Document processing error: {e}")
            return {"success": False, "error": str(e)}
    
    async def capture_screenshot(self) -> Dict[str, Any]:
        """Capture and analyze desktop screenshot"""
        try:
            # For macOS, use screencapture command
            import subprocess
            
            with tempfile.NamedTemporaryFile(suffix='.png', delete=False) as temp_file:
                temp_path = temp_file.name
            
            # Capture screenshot
            result = subprocess.run(['screencapture', '-x', temp_path], 
                                  capture_output=True, text=True)
            
            if result.returncode != 0:
                return {"success": False, "error": "Screenshot capture failed"}
            
            # Process the screenshot
            with open(temp_path, 'rb') as f:
                screenshot_content = f.read()
            
            # Clean up temp file
            os.unlink(temp_path)
            
            # Analyze screenshot
            result = await self.process_image(screenshot_content, "screenshot.png")
            result["capture_timestamp"] = datetime.now().isoformat()
            
            return result
            
        except Exception as e:
            logger.error(f"Screenshot capture error: {e}")
            return {"success": False, "error": str(e)}
    
    def generate_mermaid_diagram(self, diagram_type: str, content: str) -> str:
        """Generate Mermaid diagram syntax"""
        try:
            if diagram_type == "flowchart":
                return f"""
graph TD
    A[Start] --> B{{Decision}}
    B -->|Yes| C[Process]
    B -->|No| D[Alternative]
    C --> E[End]
    D --> E
"""
            elif diagram_type == "sequence":
                return f"""
sequenceDiagram
    participant User
    participant ALims
    participant Gemma3
    
    User->>ALims: Send Message
    ALims->>Gemma3: Process Request
    Gemma3->>ALims: Generate Response
    ALims->>User: Display Result
"""
            elif diagram_type == "class":
                return f"""
classDiagram
    class MultimodalProcessor {{
        +process_file()
        +process_image()
        +process_data()
        +capture_screenshot()
    }}
    
    class ALimsAI {{
        +chat_with_ai()
        +generate_visualization()
    }}
    
    MultimodalProcessor --> ALimsAI
"""
            else:
                return f"graph LR\n    A[{content}] --> B[Generated Diagram]"
                
        except Exception as e:
            logger.error(f"Mermaid generation error: {e}")
            return f"graph LR\n    A[Error] --> B[{str(e)}]"
    
    async def _analyze_image_content(self, cv_image: np.ndarray) -> Dict[str, Any]:
        """Analyze image content using OpenCV"""
        try:
            # Color analysis
            mean_color = cv2.mean(cv_image)[:3]
            
            # Edge detection
            gray = cv2.cvtColor(cv_image, cv2.COLOR_BGR2GRAY)
            edges = cv2.Canny(gray, 50, 150)
            edge_density = np.sum(edges > 0) / edges.size
            
            # Brightness analysis
            brightness = np.mean(gray)
            
            return {
                "dominant_colors": {
                    "blue": float(mean_color[0]),
                    "green": float(mean_color[1]),
                    "red": float(mean_color[2])
                },
                "edge_density": float(edge_density),
                "brightness": float(brightness),
                "complexity": "high" if edge_density > 0.1 else "medium" if edge_density > 0.05 else "low"
            }
            
        except Exception as e:
            logger.error(f"Image content analysis error: {e}")
            return {"error": str(e)}
    
    async def _extract_chart_data(self, cv_image: np.ndarray) -> Dict[str, Any]:
        """Attempt to extract data from charts/graphs"""
        try:
            # Simple chart detection (this is a basic implementation)
            gray = cv2.cvtColor(cv_image, cv2.COLOR_BGR2GRAY)
            
            # Look for rectangular regions (potential chart areas)
            contours, _ = cv2.findContours(gray, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
            
            chart_regions = []
            for contour in contours:
                area = cv2.contourArea(contour)
                if area > 1000:  # Filter small regions
                    x, y, w, h = cv2.boundingRect(contour)
                    chart_regions.append({"x": x, "y": y, "width": w, "height": h, "area": area})
            
            return {
                "potential_charts": len(chart_regions),
                "chart_regions": chart_regions[:5],  # Limit to top 5
                "analysis": "Basic chart detection - advanced OCR needed for data extraction"
            }
            
        except Exception as e:
            logger.error(f"Chart data extraction error: {e}")
            return {"error": str(e)}
    
    def _create_thumbnail(self, image: Image.Image, size: Tuple[int, int] = (150, 150)) -> str:
        """Create base64 encoded thumbnail"""
        try:
            thumbnail = image.copy()
            thumbnail.thumbnail(size, Image.Resampling.LANCZOS)
            
            buffer = io.BytesIO()
            thumbnail.save(buffer, format='PNG')
            buffer.seek(0)
            
            return base64.b64encode(buffer.getvalue()).decode('utf-8')
            
        except Exception as e:
            logger.error(f"Thumbnail creation error: {e}")
            return ""
    
    def _convert_to_json_safe(self, obj):
        """Convert numpy types and other non-JSON-serializable objects to JSON-safe types"""
        if isinstance(obj, dict):
            return {k: self._convert_to_json_safe(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [self._convert_to_json_safe(item) for item in obj]
        elif isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif pd.isna(obj):
            return None
        else:
            return obj
    
    def _suggest_visualizations(self, df: pd.DataFrame) -> List[Dict[str, Any]]:
        """Suggest appropriate visualizations for the dataset"""
        suggestions = []
        
        numeric_cols = df.select_dtypes(include=[np.number]).columns.tolist()
        categorical_cols = df.select_dtypes(include=['object']).columns.tolist()
        
        if len(numeric_cols) >= 2:
            suggestions.append({
                "type": "scatter",
                "description": f"Scatter plot of {numeric_cols[0]} vs {numeric_cols[1]}",
                "columns": numeric_cols[:2]
            })
        
        if len(numeric_cols) >= 1 and len(categorical_cols) >= 1:
            suggestions.append({
                "type": "bar",
                "description": f"Bar chart of {numeric_cols[0]} by {categorical_cols[0]}",
                "columns": [categorical_cols[0], numeric_cols[0]]
            })
        
        if len(numeric_cols) >= 1:
            suggestions.append({
                "type": "histogram",
                "description": f"Distribution of {numeric_cols[0]}",
                "columns": [numeric_cols[0]]
            })
        
        return suggestions
    
    def _detect_language(self, file_ext: str) -> str:
        """Detect programming language from file extension"""
        language_map = {
            '.py': 'Python',
            '.js': 'JavaScript',
            '.ts': 'TypeScript',
            '.html': 'HTML',
            '.css': 'CSS',
            '.yaml': 'YAML',
            '.yml': 'YAML',
            '.md': 'Markdown',
            '.json': 'JSON'
        }
        return language_map.get(file_ext, 'Unknown')
    
    def _analyze_code_metrics(self, code: str, file_ext: str) -> Dict[str, Any]:
        """Analyze basic code metrics"""
        lines = code.split('\n')
        
        return {
            "total_lines": len(lines),
            "non_empty_lines": len([line for line in lines if line.strip()]),
            "comment_lines": len([line for line in lines if line.strip().startswith('#')]),
            "average_line_length": sum(len(line) for line in lines) / len(lines) if lines else 0
        }
    
    def _analyze_code_structure(self, code: str, file_ext: str) -> Dict[str, Any]:
        """Analyze code structure (basic implementation)"""
        if file_ext == '.py':
            return self._analyze_python_structure(code)
        elif file_ext in ['.js', '.ts']:
            return self._analyze_javascript_structure(code)
        else:
            return {"functions": 0, "classes": 0, "imports": 0}
    
    def _analyze_python_structure(self, code: str) -> Dict[str, Any]:
        """Analyze Python code structure"""
        lines = code.split('\n')
        
        functions = len([line for line in lines if line.strip().startswith('def ')])
        classes = len([line for line in lines if line.strip().startswith('class ')])
        imports = len([line for line in lines if line.strip().startswith(('import ', 'from '))])
        
        return {
            "functions": functions,
            "classes": classes,
            "imports": imports,
            "language_specific": {
                "decorators": len([line for line in lines if line.strip().startswith('@')])
            }
        }
    
    def _analyze_javascript_structure(self, code: str) -> Dict[str, Any]:
        """Analyze JavaScript/TypeScript code structure"""
        functions = code.count('function ') + code.count('=> ')
        classes = code.count('class ')
        imports = code.count('import ') + code.count('require(')
        
        return {
            "functions": functions,
            "classes": classes,
            "imports": imports,
            "language_specific": {
                "arrow_functions": code.count('=> ')
            }
        }
    
    def _generate_image_analysis_prompt(self, analysis: Dict[str, Any]) -> str:
        """Generate AI prompt for image analysis"""
        basic = analysis.get("basic_info", {})
        visual = analysis.get("visual_analysis", {})
        dimensions = basic.get("dimensions", {})
        
        return f"""
I've analyzed an image with the following characteristics:
- Dimensions: {dimensions.get('width', 0)}x{dimensions.get('height', 0)} pixels
- Format: {basic.get('format', 'unknown')}
- File size: {basic.get('size_bytes', 0)} bytes
- Brightness level: {visual.get('brightness', 0):.1f}
- Complexity: {visual.get('complexity', 'unknown')}
- Edge density: {visual.get('edge_density', 0):.3f}

Please provide insights about this image and suggest how it might be used or what it represents.
If it appears to be a chart or graph, help extract or interpret the data it contains.
"""
    
    def _generate_data_analysis_prompt(self, analysis: Dict[str, Any]) -> str:
        """Generate AI prompt for data analysis"""
        basic = analysis.get("basic_info", {})
        
        return f"""
I've loaded a dataset with the following characteristics:
- Rows: {basic.get('rows', 0)}
- Columns: {basic.get('columns', 0)}
- Column names: {', '.join(basic.get('column_names', []))}

Sample data preview:
{json.dumps(analysis.get('sample_data', [])[:3], indent=2)}

Please analyze this dataset and provide insights. Suggest appropriate visualizations and identify interesting patterns or relationships in the data.
"""
    
    def _generate_code_analysis_prompt(self, analysis: Dict[str, Any], code: str) -> str:
        """Generate AI prompt for code analysis"""
        basic = analysis.get("basic_info", {})
        metrics = analysis.get("code_metrics", {})
        structure = analysis.get("structure", {})
        
        return f"""
I've analyzed a {basic.get('language', 'code')} file with the following characteristics:
- Lines of code: {metrics.get('total_lines', 0)}
- Functions: {structure.get('functions', 0)}
- Classes: {structure.get('classes', 0)}
- Imports: {structure.get('imports', 0)}

Code preview:
```{basic.get('language', '').lower()}
{analysis.get('preview', '')}
```

Please analyze this code and provide insights about its structure, purpose, and quality. Suggest improvements or documentation if needed.
"""
    
    def _analyze_document_content(self, text: str) -> Dict[str, Any]:
        """Analyze document content for key themes and structure"""
        words = text.lower().split()
        
        # Simple keyword analysis
        keywords = {}
        for word in words:
            if len(word) > 4:  # Only count longer words
                keywords[word] = keywords.get(word, 0) + 1
        
        # Get top keywords
        top_keywords = sorted(keywords.items(), key=lambda x: x[1], reverse=True)[:10]
        
        return {
            "top_keywords": [{"word": word, "count": count} for word, count in top_keywords],
            "sentence_count": len([s for s in text.split('.') if s.strip()]),
            "paragraph_count": len([p for p in text.split('\n\n') if p.strip()]),
            "readability": "medium"  # Simplified readability assessment
        }
    
    def _generate_document_analysis_prompt(self, analysis: Dict[str, Any], text: str) -> str:
        """Generate AI prompt for document analysis"""
        basic = analysis.get("basic_info", {})
        content = analysis.get("content_analysis", {})
        
        return f"""
I've analyzed a {basic.get('document_type', 'document')} file with the following characteristics:
- Word count: {basic.get('word_count', 0)}
- Character count: {basic.get('character_count', 0)}
- Sentences: {content.get('sentence_count', 0)}
- Paragraphs: {content.get('paragraph_count', 0)}

Top keywords: {', '.join([kw['word'] for kw in content.get('top_keywords', [])[:5]])}

Document preview:
{analysis.get('content_preview', '')}

Please analyze this document and provide insights about its content, purpose, and key themes. Summarize the main points and suggest any relevant actions or follow-ups.
"""


# Global instance
multimodal_processor = MultimodalProcessor() 