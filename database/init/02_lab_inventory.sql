-- LIMS Lab Inventory and Equipment Database Schema
-- Comprehensive PostgreSQL schema for lab inventory, equipment, and scheduling
-- Supports the TLA+ verified scheduling agent implementation

-- Enable required extensions
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";
CREATE EXTENSION IF NOT EXISTS "pg_trgm";

-- Create LIMS schema
CREATE SCHEMA IF NOT EXISTS lims;

-- ===== CORE SAMPLE MANAGEMENT =====

-- Sample types and categories
CREATE TABLE IF NOT EXISTS lims.sample_types (
    sample_type_id SERIAL PRIMARY KEY,
    sample_type_code VARCHAR(20) UNIQUE NOT NULL,
    sample_type_name VARCHAR(100) NOT NULL,
    description TEXT,
    default_collection_volume_ml INTEGER,
    default_collection_container VARCHAR(50),
    storage_temperature_celsius INTEGER,
    max_storage_days INTEGER,
    special_handling_requirements TEXT[],
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Main samples table
CREATE TABLE IF NOT EXISTS lims.samples (
    sample_id SERIAL PRIMARY KEY,
    sample_barcode VARCHAR(50) UNIQUE NOT NULL,
    sample_type_id INTEGER REFERENCES lims.sample_types(sample_type_id),
    patient_id VARCHAR(50),
    collection_date TIMESTAMP WITH TIME ZONE,
    collection_time TIME,
    received_date TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    current_state VARCHAR(20) DEFAULT 'RECEIVED',
    priority VARCHAR(10) DEFAULT 'ROUTINE',
    special_instructions TEXT,
    collection_volume_ml INTEGER,
    collection_container VARCHAR(50),
    collector_id VARCHAR(50),
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    CONSTRAINT valid_state CHECK (current_state IN ('RECEIVED', 'ACCESSIONED', 'SCHEDULED', 'IN_PROGRESS', 'COMPLETED', 'REJECTED', 'CANCELLED')),
    CONSTRAINT valid_priority CHECK (priority IN ('STAT', 'URGENT', 'ROUTINE'))
);

-- ===== TEST MANAGEMENT =====

-- Test types and capabilities
CREATE TABLE IF NOT EXISTS lims.test_types (
    test_type_id SERIAL PRIMARY KEY,
    test_code VARCHAR(20) UNIQUE NOT NULL,
    test_name VARCHAR(100) NOT NULL,
    department VARCHAR(50) NOT NULL,
    category VARCHAR(50),
    description TEXT,
    estimated_duration_minutes INTEGER NOT NULL,
    sample_volume_required_ml INTEGER,
    result_type VARCHAR(20) DEFAULT 'NUMERIC',
    reference_range_min DECIMAL(10,4),
    reference_range_max DECIMAL(10,4),
    units VARCHAR(20),
    methodology TEXT,
    quality_control_required BOOLEAN DEFAULT TRUE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Test orders and requests
CREATE TABLE IF NOT EXISTS lims.test_orders (
    order_id SERIAL PRIMARY KEY,
    sample_id INTEGER REFERENCES lims.samples(sample_id),
    test_type_id INTEGER REFERENCES lims.test_types(test_type_id),
    order_date TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    priority VARCHAR(10) DEFAULT 'ROUTINE',
    requested_by VARCHAR(50),
    special_requirements TEXT[],
    order_status VARCHAR(20) DEFAULT 'PENDING',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    CONSTRAINT valid_order_priority CHECK (priority IN ('STAT', 'URGENT', 'ROUTINE')),
    CONSTRAINT valid_order_status CHECK (order_status IN ('PENDING', 'SCHEDULED', 'IN_PROGRESS', 'COMPLETED', 'CANCELLED'))
);

-- ===== EQUIPMENT MANAGEMENT =====

-- Equipment categories and types
CREATE TABLE IF NOT EXISTS lims.equipment_categories (
    category_id SERIAL PRIMARY KEY,
    category_name VARCHAR(50) UNIQUE NOT NULL,
    description TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Main equipment table
CREATE TABLE IF NOT EXISTS lims.equipment (
    equipment_id SERIAL PRIMARY KEY,
    equipment_name VARCHAR(100) UNIQUE NOT NULL,
    equipment_type VARCHAR(50) NOT NULL,
    category_id INTEGER REFERENCES lims.equipment_categories(category_id),
    model VARCHAR(100),
    serial_number VARCHAR(100),
    manufacturer VARCHAR(100),
    install_date DATE,
    last_calibration_date DATE,
    next_calibration_date DATE,
    status VARCHAR(20) DEFAULT 'AVAILABLE',
    location VARCHAR(100),
    max_concurrent_tests INTEGER DEFAULT 1,
    current_test_count INTEGER DEFAULT 0,
    maintenance_schedule TEXT,
    operating_temperature_min INTEGER,
    operating_temperature_max INTEGER,
    operating_humidity_min INTEGER,
    operating_humidity_max INTEGER,
    special_requirements TEXT[],
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    CONSTRAINT valid_equipment_status CHECK (status IN ('AVAILABLE', 'IN_USE', 'MAINTENANCE', 'CALIBRATION', 'OUT_OF_SERVICE')),
    CONSTRAINT valid_concurrent_tests CHECK (max_concurrent_tests >= 0),
    CONSTRAINT valid_current_count CHECK (current_test_count >= 0 AND current_test_count <= max_concurrent_tests)
);

-- Equipment capabilities (what tests can be performed)
CREATE TABLE IF NOT EXISTS lims.equipment_capabilities (
    capability_id SERIAL PRIMARY KEY,
    equipment_id INTEGER REFERENCES lims.equipment(equipment_id),
    test_type_id INTEGER REFERENCES lims.test_types(test_type_id),
    efficiency_factor DECIMAL(3,2) DEFAULT 1.0,
    setup_time_minutes INTEGER DEFAULT 0,
    cleanup_time_minutes INTEGER DEFAULT 0,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    UNIQUE(equipment_id, test_type_id)
);

-- ===== CONSUMABLES AND INVENTORY =====

-- Consumable types and categories
CREATE TABLE IF NOT EXISTS lims.consumable_categories (
    category_id SERIAL PRIMARY KEY,
    category_name VARCHAR(50) UNIQUE NOT NULL,
    description TEXT,
    storage_requirements TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Consumable items (reagents, supplies, etc.)
CREATE TABLE IF NOT EXISTS lims.consumables (
    consumable_id SERIAL PRIMARY KEY,
    item_code VARCHAR(50) UNIQUE NOT NULL,
    item_name VARCHAR(100) NOT NULL,
    category_id INTEGER REFERENCES lims.consumable_categories(category_id),
    description TEXT,
    manufacturer VARCHAR(100),
    catalog_number VARCHAR(100),
    unit_of_measure VARCHAR(20),
    unit_cost DECIMAL(10,2),
    storage_temperature_celsius INTEGER,
    storage_conditions TEXT,
    shelf_life_days INTEGER,
    minimum_stock_level INTEGER DEFAULT 0,
    reorder_level INTEGER DEFAULT 0,
    hazmat_class VARCHAR(20),
    special_handling TEXT[],
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Inventory items (actual stock)
CREATE TABLE IF NOT EXISTS lims.inventory_items (
    inventory_id SERIAL PRIMARY KEY,
    consumable_id INTEGER REFERENCES lims.consumables(consumable_id),
    lot_number VARCHAR(50),
    received_date DATE DEFAULT CURRENT_DATE,
    expiration_date DATE,
    quantity_received INTEGER NOT NULL,
    quantity_available INTEGER NOT NULL,
    quantity_reserved INTEGER DEFAULT 0,
    quantity_used INTEGER DEFAULT 0,
    status VARCHAR(20) DEFAULT 'AVAILABLE',
    location VARCHAR(100),
    supplier VARCHAR(100),
    purchase_order VARCHAR(50),
    unit_cost DECIMAL(10,2),
    storage_conditions_actual TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    CONSTRAINT valid_inventory_status CHECK (status IN ('AVAILABLE', 'RESERVED', 'EXPIRED', 'DAMAGED', 'RECALLED')),
    CONSTRAINT valid_quantities CHECK (
        quantity_received >= 0 AND 
        quantity_available >= 0 AND 
        quantity_reserved >= 0 AND 
        quantity_used >= 0 AND
        quantity_available = quantity_received - quantity_used AND
        quantity_reserved <= quantity_available
    )
);

-- Test consumable requirements
CREATE TABLE IF NOT EXISTS lims.test_consumable_requirements (
    requirement_id SERIAL PRIMARY KEY,
    test_type_id INTEGER REFERENCES lims.test_types(test_type_id),
    consumable_id INTEGER REFERENCES lims.consumables(consumable_id),
    quantity_required INTEGER NOT NULL,
    is_critical BOOLEAN DEFAULT TRUE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    UNIQUE(test_type_id, consumable_id)
);

-- ===== SCHEDULING SYSTEM =====

-- Sample scheduling table
CREATE TABLE IF NOT EXISTS lims.sample_scheduling (
    scheduling_id SERIAL PRIMARY KEY,
    sample_id INTEGER REFERENCES lims.samples(sample_id),
    test_type_id INTEGER REFERENCES lims.test_types(test_type_id),
    equipment_id INTEGER REFERENCES lims.equipment(equipment_id),
    priority VARCHAR(10) NOT NULL,
    scheduled_date DATE,
    estimated_start_time TIME,
    estimated_end_time TIME,
    actual_start_time TIMESTAMP WITH TIME ZONE,
    actual_end_time TIMESTAMP WITH TIME ZONE,
    status VARCHAR(20) DEFAULT 'PENDING',
    retry_count INTEGER DEFAULT 0,
    notes TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    CONSTRAINT valid_scheduling_priority CHECK (priority IN ('STAT', 'URGENT', 'ROUTINE')),
    CONSTRAINT valid_scheduling_status CHECK (status IN ('PENDING', 'SCHEDULED', 'IN_PROGRESS', 'COMPLETED', 'FAILED', 'CANCELLED')),
    CONSTRAINT valid_retry_count CHECK (retry_count >= 0)
);

-- Resource reservations
CREATE TABLE IF NOT EXISTS lims.resource_reservations (
    reservation_id SERIAL PRIMARY KEY,
    scheduling_id INTEGER REFERENCES lims.sample_scheduling(scheduling_id),
    inventory_id INTEGER REFERENCES lims.inventory_items(inventory_id),
    quantity_reserved INTEGER NOT NULL,
    reservation_date TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    expiration_date TIMESTAMP WITH TIME ZONE,
    status VARCHAR(20) DEFAULT 'ACTIVE',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    CONSTRAINT valid_reservation_status CHECK (status IN ('ACTIVE', 'USED', 'CANCELLED', 'EXPIRED')),
    CONSTRAINT valid_reservation_quantity CHECK (quantity_reserved > 0)
);

-- ===== QUALITY CONTROL =====

-- Quality control samples
CREATE TABLE IF NOT EXISTS lims.quality_control_samples (
    qc_sample_id SERIAL PRIMARY KEY,
    qc_sample_code VARCHAR(50) UNIQUE NOT NULL,
    qc_type VARCHAR(20) NOT NULL,
    test_type_id INTEGER REFERENCES lims.test_types(test_type_id),
    expected_value DECIMAL(10,4),
    acceptable_range_min DECIMAL(10,4),
    acceptable_range_max DECIMAL(10,4),
    lot_number VARCHAR(50),
    expiration_date DATE,
    frequency_hours INTEGER DEFAULT 24,
    last_run_date TIMESTAMP WITH TIME ZONE,
    next_run_date TIMESTAMP WITH TIME ZONE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    
    CONSTRAINT valid_qc_type CHECK (qc_type IN ('BLANK', 'CONTROL', 'CALIBRATOR', 'PROFICIENCY'))
);

-- ===== INDEXES FOR PERFORMANCE =====

-- Sample indexes
CREATE INDEX IF NOT EXISTS idx_samples_barcode ON lims.samples(sample_barcode);
CREATE INDEX IF NOT EXISTS idx_samples_state ON lims.samples(current_state);
CREATE INDEX IF NOT EXISTS idx_samples_priority ON lims.samples(priority);
CREATE INDEX IF NOT EXISTS idx_samples_received_date ON lims.samples(received_date);

-- Test indexes
CREATE INDEX IF NOT EXISTS idx_test_types_code ON lims.test_types(test_code);
CREATE INDEX IF NOT EXISTS idx_test_types_department ON lims.test_types(department);
CREATE INDEX IF NOT EXISTS idx_test_orders_sample_id ON lims.test_orders(sample_id);
CREATE INDEX IF NOT EXISTS idx_test_orders_status ON lims.test_orders(order_status);

-- Equipment indexes
CREATE INDEX IF NOT EXISTS idx_equipment_status ON lims.equipment(status);
CREATE INDEX IF NOT EXISTS idx_equipment_type ON lims.equipment(equipment_type);
CREATE INDEX IF NOT EXISTS idx_equipment_capabilities_equipment_id ON lims.equipment_capabilities(equipment_id);
CREATE INDEX IF NOT EXISTS idx_equipment_capabilities_test_type_id ON lims.equipment_capabilities(test_type_id);

-- Inventory indexes
CREATE INDEX IF NOT EXISTS idx_inventory_consumable_id ON lims.inventory_items(consumable_id);
CREATE INDEX IF NOT EXISTS idx_inventory_status ON lims.inventory_items(status);
CREATE INDEX IF NOT EXISTS idx_inventory_expiration ON lims.inventory_items(expiration_date);
CREATE INDEX IF NOT EXISTS idx_consumables_code ON lims.consumables(item_code);

-- Scheduling indexes
CREATE INDEX IF NOT EXISTS idx_scheduling_sample_id ON lims.sample_scheduling(sample_id);
CREATE INDEX IF NOT EXISTS idx_scheduling_status ON lims.sample_scheduling(status);
CREATE INDEX IF NOT EXISTS idx_scheduling_priority ON lims.sample_scheduling(priority);
CREATE INDEX IF NOT EXISTS idx_scheduling_date ON lims.sample_scheduling(scheduled_date);
CREATE INDEX IF NOT EXISTS idx_scheduling_equipment_id ON lims.sample_scheduling(equipment_id);

-- Resource reservation indexes
CREATE INDEX IF NOT EXISTS idx_reservations_scheduling_id ON lims.resource_reservations(scheduling_id);
CREATE INDEX IF NOT EXISTS idx_reservations_inventory_id ON lims.resource_reservations(inventory_id);
CREATE INDEX IF NOT EXISTS idx_reservations_status ON lims.resource_reservations(status);

-- ===== TRIGGERS FOR AUTOMATIC UPDATES =====

-- Updated_at trigger function
CREATE OR REPLACE FUNCTION lims.update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = NOW();
    RETURN NEW;
END;
$$ language 'plpgsql';

-- Apply updated_at triggers
CREATE TRIGGER update_samples_updated_at BEFORE UPDATE ON lims.samples FOR EACH ROW EXECUTE FUNCTION lims.update_updated_at_column();
CREATE TRIGGER update_test_types_updated_at BEFORE UPDATE ON lims.test_types FOR EACH ROW EXECUTE FUNCTION lims.update_updated_at_column();
CREATE TRIGGER update_test_orders_updated_at BEFORE UPDATE ON lims.test_orders FOR EACH ROW EXECUTE FUNCTION lims.update_updated_at_column();
CREATE TRIGGER update_equipment_updated_at BEFORE UPDATE ON lims.equipment FOR EACH ROW EXECUTE FUNCTION lims.update_updated_at_column();
CREATE TRIGGER update_consumables_updated_at BEFORE UPDATE ON lims.consumables FOR EACH ROW EXECUTE FUNCTION lims.update_updated_at_column();
CREATE TRIGGER update_inventory_updated_at BEFORE UPDATE ON lims.inventory_items FOR EACH ROW EXECUTE FUNCTION lims.update_updated_at_column();
CREATE TRIGGER update_scheduling_updated_at BEFORE UPDATE ON lims.sample_scheduling FOR EACH ROW EXECUTE FUNCTION lims.update_updated_at_column();
CREATE TRIGGER update_qc_samples_updated_at BEFORE UPDATE ON lims.quality_control_samples FOR EACH ROW EXECUTE FUNCTION lims.update_updated_at_column();

-- ===== SAMPLE DATA FOR TESTING =====

-- Insert sample types
INSERT INTO lims.sample_types (sample_type_code, sample_type_name, default_collection_volume_ml, storage_temperature_celsius, max_storage_days) VALUES
    ('BLOOD', 'Whole Blood', 5, 4, 7),
    ('SERUM', 'Serum', 3, -20, 30),
    ('PLASMA', 'Plasma', 3, -20, 30),
    ('URINE', 'Urine', 10, 4, 2),
    ('TISSUE', 'Tissue Biopsy', 1, -80, 365)
ON CONFLICT (sample_type_code) DO NOTHING;

-- Insert equipment categories
INSERT INTO lims.equipment_categories (category_name, description) VALUES
    ('CHEMISTRY', 'Chemistry analyzers and related equipment'),
    ('HEMATOLOGY', 'Hematology analyzers and cell counters'),
    ('MICROBIOLOGY', 'Microbiology culture and identification equipment'),
    ('MOLECULAR', 'Molecular diagnostic and PCR equipment'),
    ('IMMUNOLOGY', 'Immunoassay and serology equipment')
ON CONFLICT (category_name) DO NOTHING;

-- Insert test types
INSERT INTO lims.test_types (test_code, test_name, department, category, estimated_duration_minutes) VALUES
    ('CBC', 'Complete Blood Count', 'HEMATOLOGY', 'ROUTINE', 15),
    ('BMP', 'Basic Metabolic Panel', 'CHEMISTRY', 'ROUTINE', 20),
    ('CMP', 'Comprehensive Metabolic Panel', 'CHEMISTRY', 'ROUTINE', 25),
    ('LIPID', 'Lipid Panel', 'CHEMISTRY', 'ROUTINE', 18),
    ('TSH', 'Thyroid Stimulating Hormone', 'IMMUNOLOGY', 'HORMONE', 30),
    ('GLUCOSE', 'Glucose', 'CHEMISTRY', 'ROUTINE', 10),
    ('TROPONIN', 'Troponin I', 'CHEMISTRY', 'CARDIAC', 20),
    ('PT_INR', 'Prothrombin Time/INR', 'HEMATOLOGY', 'COAGULATION', 12)
ON CONFLICT (test_code) DO NOTHING;

-- Insert equipment
INSERT INTO lims.equipment (equipment_name, equipment_type, category_id, status, max_concurrent_tests, location) VALUES
    ('CHEM-001', 'Chemistry Analyzer', 1, 'AVAILABLE', 4, 'Lab A'),
    ('CHEM-002', 'Chemistry Analyzer', 1, 'AVAILABLE', 4, 'Lab A'),
    ('HEMA-001', 'Hematology Analyzer', 2, 'AVAILABLE', 2, 'Lab B'),
    ('HEMA-002', 'Hematology Analyzer', 2, 'AVAILABLE', 2, 'Lab B'),
    ('IMMUNO-001', 'Immunoassay Analyzer', 5, 'AVAILABLE', 3, 'Lab C')
ON CONFLICT (equipment_name) DO NOTHING;

-- Insert equipment capabilities
INSERT INTO lims.equipment_capabilities (equipment_id, test_type_id) VALUES
    (1, 2), (1, 3), (1, 4), (1, 6), (1, 7), -- CHEM-001
    (2, 2), (2, 3), (2, 4), (2, 6), (2, 7), -- CHEM-002
    (3, 1), (3, 8), -- HEMA-001
    (4, 1), (4, 8), -- HEMA-002
    (5, 5) -- IMMUNO-001
ON CONFLICT (equipment_id, test_type_id) DO NOTHING;

-- Insert consumable categories
INSERT INTO lims.consumable_categories (category_name, description) VALUES
    ('REAGENTS', 'Chemical reagents and solutions'),
    ('SUPPLIES', 'Laboratory supplies and disposables'),
    ('CALIBRATORS', 'Calibration standards and controls'),
    ('QUALITY_CONTROL', 'Quality control materials')
ON CONFLICT (category_name) DO NOTHING;

-- Insert consumables
INSERT INTO lims.consumables (item_code, item_name, category_id, unit_of_measure, minimum_stock_level) VALUES
    ('CHEM-REG-001', 'Chemistry Reagent Pack A', 1, 'PACK', 5),
    ('CHEM-REG-002', 'Chemistry Reagent Pack B', 1, 'PACK', 5),
    ('HEMA-REG-001', 'Hematology Diluent', 1, 'LITER', 10),
    ('SUPPLIES-001', 'Sample Cups', 2, 'EACH', 100),
    ('SUPPLIES-002', 'Pipette Tips', 2, 'PACK', 20),
    ('QC-001', 'Normal Control Level 1', 4, 'VIAL', 3),
    ('QC-002', 'Abnormal Control Level 2', 4, 'VIAL', 3)
ON CONFLICT (item_code) DO NOTHING;

-- Insert inventory items
INSERT INTO lims.inventory_items (consumable_id, lot_number, expiration_date, quantity_received, quantity_available, location) VALUES
    (1, 'LOT001', '2024-12-31', 10, 10, 'Reagent Fridge A'),
    (2, 'LOT002', '2024-12-31', 10, 10, 'Reagent Fridge A'),
    (3, 'LOT003', '2024-08-31', 50, 50, 'Reagent Room'),
    (4, 'LOT004', '2025-06-30', 500, 500, 'Supply Cabinet'),
    (5, 'LOT005', '2025-06-30', 100, 100, 'Supply Cabinet'),
    (6, 'LOT006', '2024-09-30', 10, 10, 'QC Fridge'),
    (7, 'LOT007', '2024-09-30', 10, 10, 'QC Fridge');

-- Insert test consumable requirements
INSERT INTO lims.test_consumable_requirements (test_type_id, consumable_id, quantity_required) VALUES
    (2, 1, 1), (2, 4, 2), (2, 6, 1), -- BMP
    (3, 1, 1), (3, 2, 1), (3, 4, 2), (3, 6, 1), -- CMP
    (4, 1, 1), (4, 4, 2), (4, 6, 1), -- LIPID
    (6, 1, 1), (6, 4, 2), (6, 6, 1), -- GLUCOSE
    (7, 1, 1), (7, 4, 2), (7, 6, 1), -- TROPONIN
    (1, 3, 1), (1, 4, 2), (1, 6, 1), -- CBC
    (8, 3, 1), (8, 4, 2), (8, 6, 1) -- PT_INR
ON CONFLICT (test_type_id, consumable_id) DO NOTHING;

-- Insert sample data for testing
INSERT INTO lims.samples (sample_barcode, sample_type_id, patient_id, collection_date, current_state, priority) VALUES
    ('SAMPLE001', 1, 'PAT001', '2024-07-11 08:00:00', 'ACCESSIONED', 'ROUTINE'),
    ('SAMPLE002', 1, 'PAT002', '2024-07-11 08:15:00', 'ACCESSIONED', 'URGENT'),
    ('SAMPLE003', 2, 'PAT003', '2024-07-11 08:30:00', 'ACCESSIONED', 'STAT'),
    ('SAMPLE004', 3, 'PAT004', '2024-07-11 08:45:00', 'ACCESSIONED', 'ROUTINE'),
    ('SAMPLE005', 4, 'PAT005', '2024-07-11 09:00:00', 'ACCESSIONED', 'URGENT')
ON CONFLICT (sample_barcode) DO NOTHING;

-- Insert test orders
INSERT INTO lims.test_orders (sample_id, test_type_id, priority, requested_by) VALUES
    (1, 1, 'ROUTINE', 'DR_SMITH'), -- CBC
    (1, 2, 'ROUTINE', 'DR_SMITH'), -- BMP
    (2, 3, 'URGENT', 'DR_JONES'), -- CMP
    (2, 7, 'URGENT', 'DR_JONES'), -- TROPONIN
    (3, 6, 'STAT', 'DR_WILLIAMS'), -- GLUCOSE
    (4, 4, 'ROUTINE', 'DR_BROWN'), -- LIPID
    (5, 5, 'URGENT', 'DR_DAVIS') -- TSH
ON CONFLICT DO NOTHING;

-- Insert quality control samples
INSERT INTO lims.quality_control_samples (qc_sample_code, qc_type, test_type_id, expected_value, acceptable_range_min, acceptable_range_max) VALUES
    ('QC-CBC-001', 'CONTROL', 1, 12.5, 11.0, 14.0),
    ('QC-BMP-001', 'CONTROL', 2, 95.0, 90.0, 100.0),
    ('QC-CMP-001', 'CONTROL', 3, 95.0, 90.0, 100.0),
    ('QC-LIPID-001', 'CONTROL', 4, 200.0, 180.0, 220.0),
    ('QC-TSH-001', 'CONTROL', 5, 2.5, 2.0, 3.0)
ON CONFLICT (qc_sample_code) DO NOTHING;

-- Log successful initialization
INSERT INTO workflow_manager.workflow_events (workflow_id, event_type, metadata) VALUES
    ('lims-initialization', 'SCHEMA_CREATED', '{"message": "LIMS inventory schema initialized successfully", "timestamp": "' || NOW() || '"}')
ON CONFLICT DO NOTHING;
