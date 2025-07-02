# ALims Event Persistence System 🗄️

The ALims Event Persistence System provides comprehensive, high-performance storage for all captured events, enabling true long-term memory for your AI Operating System.

## 🌟 Features

### Core Capabilities
- **SQLite Database**: High-performance, ACID-compliant storage
- **Batch Processing**: Optimized writes with configurable batching
- **Automatic Compression**: Large events compressed with gzip
- **Event Deduplication**: Hash-based duplicate prevention
- **Background Cleanup**: Automatic old event removal
- **Thread Safety**: Concurrent access from multiple components
- **Recovery Support**: System restart recovery with persistent data

### Performance Optimizations
- **Write-Ahead Logging (WAL)**: Non-blocking concurrent reads
- **Memory Mapping**: 256MB mmap for faster access
- **Indexed Queries**: Optimized search by timestamp, type, source
- **Batch Transactions**: Up to 100 events per transaction
- **Connection Pooling**: Thread-local database connections

## 📊 Database Schema

### Events Table
```sql
CREATE TABLE events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp REAL NOT NULL,
    event_type TEXT NOT NULL,
    action TEXT,
    source TEXT NOT NULL,
    data_json TEXT,
    data_compressed BLOB,
    hash TEXT UNIQUE,
    processed BOOLEAN DEFAULT FALSE,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
);
```

### Patterns Table
```sql
CREATE TABLE patterns (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    event_id INTEGER,
    pattern_type TEXT NOT NULL,
    confidence REAL NOT NULL,
    pattern_data TEXT NOT NULL,
    embryo_id TEXT,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (event_id) REFERENCES events (id)
);
```

### System Stats Table
```sql
CREATE TABLE system_stats (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp REAL NOT NULL,
    total_events INTEGER,
    events_per_second REAL,
    active_embryos INTEGER,
    avg_fitness REAL,
    storage_mb REAL,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
);
```

## 🚀 Getting Started

### Automatic Integration
Persistence is **enabled by default** when you run ALims:

```bash
# Headless mode with persistence
python alims.py

# Full macOS integration with persistence
python alims_tray.py
```

### Configuration
The system uses these default settings:
```python
{
    "enable_persistence": True,
    "persistence": {
        "database_path": "data/events.db",
        "batch_size": 100,
        "batch_timeout": 5.0,
        "retention_days": 30,
        "cleanup_interval_hours": 24
    }
}
```

## 🛠️ Command Line Tools

### Events CLI Tool
Query and analyze your event data:

```bash
# Show database statistics
python tools/alims_events.py stats

# List recent events
python tools/alims_events.py list --hours 2 --limit 50

# Search for specific events
python tools/alims_events.py search "chrome" --limit 10

# Export events to JSON
python tools/alims_events.py export events_backup.json --hours 24
```

### Real-Time Dashboard
Monitor your system in real-time:

```bash
# Launch the dashboard
python tools/alims_dashboard.py

# Use custom database path
python tools/alims_dashboard.py --db /path/to/events.db
```

The dashboard shows:
- 📊 Event capture statistics
- 🧠 AI learning status
- ⚡ Performance metrics
- 📈 Real-time event rates
- 📋 Event type breakdowns

## 📈 Performance Metrics

### Typical Performance
- **Event Storage**: 1000+ events/second
- **Database Size**: ~1MB per 10,000 events
- **Query Speed**: Sub-millisecond for indexed queries
- **Memory Usage**: <50MB for persistence layer
- **Compression**: 60-80% size reduction for large events

### Optimization Features
- **Batch Writes**: Groups events for efficient storage
- **Lazy Compression**: Only compresses events >1KB
- **Smart Indexing**: Optimized for common query patterns
- **Background Processing**: Non-blocking event storage
- **Connection Reuse**: Thread-local connection pooling

## 🔧 Advanced Configuration

### Custom Configuration
```python
persistence_config = {
    "database_path": "custom/path/events.db",
    "batch_size": 200,           # Events per batch
    "batch_timeout": 3.0,        # Max seconds before flush
    "retention_days": 60,        # Keep events for 60 days
    "cleanup_interval_hours": 12 # Cleanup every 12 hours
}
```

### Manual Integration
```python
from app.system.event_persistence import create_event_persistence

# Create persistence manager
persistence = create_event_persistence(config)

# Start the manager
await persistence.start()

# Queue events for storage
persistence.queue_event(event_dict)
persistence.queue_events_batch(event_list)

# Stop gracefully
await persistence.stop()
```

## 📊 Monitoring & Analytics

### Database Statistics
```python
stats = persistence.get_stats()
print(f"Total stored: {stats['total_stored']}")
print(f"Queue size: {stats['queue_size']}")
print(f"Database size: {stats['database_stats']['database_size_mb']} MB")
```

### Event Retrieval
```python
# Get recent events
events = persistence.get_events(
    start_time=time.time() - 3600,  # Last hour
    event_type="file_op",           # File operations only
    limit=100                       # Max 100 events
)

# Search by time range
yesterday = time.time() - 86400
events = persistence.get_events(
    start_time=yesterday,
    end_time=time.time()
)
```

## 🧹 Maintenance

### Automatic Cleanup
- **Daily Cleanup**: Removes events older than retention period
- **Database Vacuum**: Reclaims disk space automatically
- **Index Maintenance**: Keeps queries fast
- **Log Rotation**: Prevents log files from growing too large

### Manual Maintenance
```bash
# Check database integrity
sqlite3 data/events.db "PRAGMA integrity_check;"

# Analyze database statistics
sqlite3 data/events.db "ANALYZE;"

# Manual vacuum (if needed)
sqlite3 data/events.db "VACUUM;"
```

## 🔍 Troubleshooting

### Common Issues

**Database locked error:**
```bash
# Check for other processes using the database
lsof data/events.db

# If needed, restart ALims
pkill -f alims
python alims_tray.py
```

**High disk usage:**
```bash
# Check database size
ls -lh data/events.db

# Reduce retention period in config
# Or run manual cleanup
python -c "
from app.system.event_persistence import EventDatabase
db = EventDatabase('data/events.db')
db.cleanup_old_events(7)  # Keep only 7 days
"
```

**Slow queries:**
```bash
# Check if indexes exist
sqlite3 data/events.db ".indexes"

# Rebuild indexes if needed
sqlite3 data/events.db "REINDEX;"
```

### Performance Tuning

**For high event rates (>1000/sec):**
```python
config = {
    "batch_size": 500,      # Larger batches
    "batch_timeout": 1.0,   # Faster flushes
}
```

**For low memory systems:**
```python
config = {
    "batch_size": 50,       # Smaller batches
    "batch_timeout": 10.0,  # Less frequent writes
}
```

## 🔮 Future Enhancements

### Planned Features
- **Event Replay**: Replay historical events for testing
- **Pattern Analytics**: Advanced pattern detection and analysis
- **Data Export**: Export to various formats (CSV, Parquet, etc.)
- **Distributed Storage**: Multi-node event storage
- **Real-time Streaming**: WebSocket event streaming
- **Machine Learning**: Built-in ML model training on events

### Integration Roadmap
- **Elasticsearch**: Full-text search capabilities
- **InfluxDB**: Time-series analytics
- **Grafana**: Advanced visualization dashboards
- **Apache Kafka**: Event streaming architecture

## 📚 API Reference

### EventDatabase Class
```python
class EventDatabase:
    def __init__(self, db_path: str)
    def store_event(self, event: Dict) -> int
    def store_events_batch(self, events: List[Dict]) -> List[int]
    def get_events(self, start_time=None, end_time=None, 
                   event_type=None, limit=1000) -> List[Dict]
    def get_database_stats(self) -> Dict
    def cleanup_old_events(self, days_to_keep: int = 30)
```

### EventPersistenceManager Class
```python
class EventPersistenceManager:
    def __init__(self, config: Dict)
    async def start(self)
    async def stop(self)
    def queue_event(self, event: Dict)
    def queue_events_batch(self, events: List[Dict])
    def get_stats(self) -> Dict
    def get_events(self, **kwargs) -> List[Dict]
```

## 🤝 Contributing

The persistence system is designed to be extensible. Key areas for contribution:

1. **Storage Backends**: Add support for other databases
2. **Compression Algorithms**: Implement better compression
3. **Query Optimization**: Improve query performance
4. **Analytics Tools**: Build analysis and visualization tools
5. **Export Formats**: Add support for more export formats

## 📄 License

Part of the ALims AI Operating System project. See main project license for details.

---

**🧠 Your AI Operating System now has perfect memory!** 

Every interaction, every pattern, every learning moment is preserved for your AI agents to build upon. The future of computing is learning from the past! 🚀 