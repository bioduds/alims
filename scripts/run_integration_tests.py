#!/usr/bin/env python3
"""
Integration Test Runner for Sample Testing Agent

This script helps set up and run integration tests for the Sample Testing Agent.
It handles database setup, test execution, and cleanup.

Usage:
    python run_integration_tests.py [--setup-db] [--cleanup] [--verbose]
    
Options:
    --setup-db: Create test database and schema
    --cleanup: Clean up test database after tests
    --verbose: Run tests with verbose output
    --db-url: Custom database URL (default: postgresql://postgres:postgres@localhost:5432/alims_test)
"""

import argparse
import asyncio
import asyncpg
import sys
import os
from pathlib import Path

# Add the project root to the Python path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))


async def setup_test_database(db_url: str):
    """Set up test database and schema"""
    print("Setting up test database...")
    
    # Extract database name from URL
    db_name = db_url.split('/')[-1]
    admin_url = db_url.replace(f'/{db_name}', '/postgres')
    
    try:
        # Connect to postgres admin database
        admin_conn = await asyncpg.connect(admin_url)
        
        # Create test database if it doesn't exist
        try:
            await admin_conn.execute(f'CREATE DATABASE {db_name}')
            print(f"Created database: {db_name}")
        except asyncpg.exceptions.DuplicateDatabaseError:
            print(f"Database {db_name} already exists")
        
        await admin_conn.close()
        
        # Connect to test database and create schema
        test_conn = await asyncpg.connect(db_url)
        
        await test_conn.execute("""
            CREATE SCHEMA IF NOT EXISTS lims;
            
            CREATE TABLE IF NOT EXISTS lims.test_execution (
                test_id SERIAL PRIMARY KEY,
                sample_id INTEGER NOT NULL,
                test_type VARCHAR(50) NOT NULL,
                state VARCHAR(20) NOT NULL DEFAULT 'SCHEDULED',
                result VARCHAR(100),
                retry_count INTEGER DEFAULT 0,
                instrument_id INTEGER,
                scheduled_time TIMESTAMP,
                completed_time TIMESTAMP,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            
            CREATE TABLE IF NOT EXISTS lims.equipment (
                instrument_id SERIAL PRIMARY KEY,
                name VARCHAR(100) NOT NULL,
                type VARCHAR(50) NOT NULL,
                status VARCHAR(20) NOT NULL DEFAULT 'AVAILABLE',
                location VARCHAR(100),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            
            CREATE TABLE IF NOT EXISTS lims.samples (
                sample_id SERIAL PRIMARY KEY,
                barcode VARCHAR(50) UNIQUE NOT NULL,
                status VARCHAR(20) NOT NULL DEFAULT 'RECEIVED',
                priority INTEGER DEFAULT 1,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            
            CREATE INDEX IF NOT EXISTS idx_test_execution_state ON lims.test_execution(state);
            CREATE INDEX IF NOT EXISTS idx_test_execution_retry ON lims.test_execution(state, retry_count);
            CREATE INDEX IF NOT EXISTS idx_equipment_status ON lims.equipment(status);
        """)
        
        await test_conn.close()
        print("Database schema created successfully")
        
    except Exception as e:
        print(f"Error setting up database: {e}")
        return False
    
    return True


async def cleanup_test_database(db_url: str):
    """Clean up test database"""
    print("Cleaning up test database...")
    
    db_name = db_url.split('/')[-1]
    admin_url = db_url.replace(f'/{db_name}', '/postgres')
    
    try:
        admin_conn = await asyncpg.connect(admin_url)
        
        # Terminate connections to the test database
        await admin_conn.execute(f"""
            SELECT pg_terminate_backend(pg_stat_activity.pid)
            FROM pg_stat_activity
            WHERE pg_stat_activity.datname = '{db_name}'
              AND pid <> pg_backend_pid()
        """)
        
        # Drop the test database
        await admin_conn.execute(f'DROP DATABASE IF EXISTS {db_name}')
        await admin_conn.close()
        
        print(f"Dropped database: {db_name}")
        
    except Exception as e:
        print(f"Error cleaning up database: {e}")
        return False
    
    return True


def run_integration_tests(verbose: bool = False):
    """Run integration tests using pytest"""
    import subprocess
    
    cmd = [
        sys.executable, '-m', 'pytest',
        'tests/test_sample_testing_agent_integration.py',
        '-v' if verbose else '',
        '--tb=short',
        '--durations=10'
    ]
    
    # Filter out empty strings
    cmd = [c for c in cmd if c]
    
    print(f"Running command: {' '.join(cmd)}")
    result = subprocess.run(cmd, cwd=project_root)
    return result.returncode == 0


async def main():
    parser = argparse.ArgumentParser(description='Integration Test Runner for Sample Testing Agent')
    parser.add_argument('--setup-db', action='store_true', help='Create test database and schema')
    parser.add_argument('--cleanup', action='store_true', help='Clean up test database after tests')
    parser.add_argument('--verbose', action='store_true', help='Run tests with verbose output')
    parser.add_argument('--db-url', default='postgresql://postgres:postgres@localhost:5432/alims_test',
                       help='Database URL for tests')
    
    args = parser.parse_args()
    
    # Set environment variable for tests
    os.environ['TEST_DATABASE_URL'] = args.db_url
    
    success = True
    
    if args.setup_db:
        success = await setup_test_database(args.db_url)
        if not success:
            print("Database setup failed")
            sys.exit(1)
    
    # Run tests
    print("Running integration tests...")
    test_success = run_integration_tests(args.verbose)
    
    if not test_success:
        print("Integration tests failed")
        success = False
    
    if args.cleanup:
        cleanup_success = await cleanup_test_database(args.db_url)
        if not cleanup_success:
            print("Database cleanup failed")
            success = False
    
    if success:
        print("All integration tests completed successfully!")
        sys.exit(0)
    else:
        print("Some operations failed")
        sys.exit(1)


if __name__ == '__main__':
    asyncio.run(main())
