-- LIMS PostgreSQL Database Schema
-- Physical Lab Inventory, Equipment, and Resource Management

-- ==========================================
-- PHYSICAL LAB INFRASTRUCTURE
-- ==========================================

-- Locations within the lab
CREATE TABLE locations (
    location_id SERIAL PRIMARY KEY,
    location_name VARCHAR(100) NOT NULL UNIQUE,
    location_type VARCHAR(50) NOT NULL, -- 'ROOM', 'BENCH', 'WORKSTATION', 'STORAGE'
    parent_location_id INTEGER REFERENCES locations(location_id),
    capacity INTEGER DEFAULT 1,
    is_active BOOLEAN DEFAULT TRUE,
    temperature_controlled BOOLEAN DEFAULT FALSE,
    min_temperature_celsius DECIMAL(4,2),
    max_temperature_celsius DECIMAL(4,2),
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Equipment and instruments
CREATE TABLE equipment (
    equipment_id SERIAL PRIMARY KEY,
    equipment_name VARCHAR(100) NOT NULL,
    equipment_type VARCHAR(50) NOT NULL, -- 'ANALYZER', 'MICROSCOPE', 'CENTRIFUGE', 'INCUBATOR'
    manufacturer VARCHAR(100),
    model VARCHAR(100),
    serial_number VARCHAR(100) UNIQUE,
    location_id INTEGER REFERENCES locations(location_id),
    status VARCHAR(20) DEFAULT 'AVAILABLE', -- 'AVAILABLE', 'IN_USE', 'MAINTENANCE', 'OUT_OF_ORDER'
    max_concurrent_tests INTEGER DEFAULT 1,
    current_test_count INTEGER DEFAULT 0,
    calibration_due_date DATE,
    last_maintenance_date DATE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    CONSTRAINT check_current_test_count CHECK (current_test_count >= 0),
    CONSTRAINT check_max_concurrent CHECK (current_test_count <= max_concurrent_tests)
);

-- Test types and their requirements
CREATE TABLE test_types (
    test_type_id SERIAL PRIMARY KEY,
    test_code VARCHAR(20) NOT NULL UNIQUE, -- 'CBC', 'BMP', 'LIPID', etc.
    test_name VARCHAR(100) NOT NULL,
    department VARCHAR(50) NOT NULL, -- 'HEMATOLOGY', 'CHEMISTRY', 'MICROBIOLOGY'
    estimated_duration_minutes INTEGER NOT NULL,
    requires_special_handling BOOLEAN DEFAULT FALSE,
    sample_volume_ml DECIMAL(5,2) DEFAULT 1.0,
    storage_temperature_celsius DECIMAL(4,2),
    stability_hours INTEGER DEFAULT 24,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Equipment capabilities (which tests can be run on which equipment)
CREATE TABLE equipment_capabilities (
    capability_id SERIAL PRIMARY KEY,
    equipment_id INTEGER REFERENCES equipment(equipment_id),
    test_type_id INTEGER REFERENCES test_types(test_type_id),
    efficiency_factor DECIMAL(3,2) DEFAULT 1.0, -- 1.0 = normal, >1.0 = faster, <1.0 = slower
    quality_score INTEGER DEFAULT 100, -- 0-100 quality rating
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(equipment_id, test_type_id)
);

-- ==========================================
-- CONSUMABLES AND REAGENTS
-- ==========================================

-- Consumable items (tubes, reagents, etc.)
CREATE TABLE consumables (
    consumable_id SERIAL PRIMARY KEY,
    item_name VARCHAR(100) NOT NULL,
    item_type VARCHAR(50) NOT NULL, -- 'TUBE', 'REAGENT', 'CONTROL', 'CALIBRATOR'
    manufacturer VARCHAR(100),
    catalog_number VARCHAR(50),
    unit_of_measure VARCHAR(20) NOT NULL, -- 'EACH', 'ML', 'VIAL', 'KIT'
    cost_per_unit DECIMAL(10,2),
    requires_refrigeration BOOLEAN DEFAULT FALSE,
    expiration_tracking BOOLEAN DEFAULT TRUE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Inventory management
CREATE TABLE inventory_items (
    inventory_id SERIAL PRIMARY KEY,
    consumable_id INTEGER REFERENCES consumables(consumable_id),
    location_id INTEGER REFERENCES locations(location_id),
    lot_number VARCHAR(50),
    expiration_date DATE,
    quantity_available INTEGER NOT NULL,
    quantity_reserved INTEGER DEFAULT 0,
    quantity_minimum INTEGER DEFAULT 0,
    status VARCHAR(20) DEFAULT 'AVAILABLE', -- 'AVAILABLE', 'RESERVED', 'EXPIRED', 'RECALLED'
    received_date DATE DEFAULT CURRENT_DATE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    CONSTRAINT check_quantity_available CHECK (quantity_available >= 0),
    CONSTRAINT check_quantity_reserved CHECK (quantity_reserved >= 0),
    CONSTRAINT check_quantity_logical CHECK (quantity_reserved <= quantity_available)
);

-- Test requirements for consumables
CREATE TABLE test_consumable_requirements (
    requirement_id SERIAL PRIMARY KEY,
    test_type_id INTEGER REFERENCES test_types(test_type_id),
    consumable_id INTEGER REFERENCES consumables(consumable_id),
    quantity_required INTEGER NOT NULL,
    is_optional BOOLEAN DEFAULT FALSE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ==========================================
-- SCHEDULING AND RESOURCE MANAGEMENT
-- ==========================================

-- Scheduling slots
CREATE TABLE scheduling_slots (
    slot_id SERIAL PRIMARY KEY,
    equipment_id INTEGER REFERENCES equipment(equipment_id),
    scheduled_date DATE NOT NULL,
    start_time TIME NOT NULL,
    end_time TIME NOT NULL,
    status VARCHAR(20) DEFAULT 'AVAILABLE', -- 'AVAILABLE', 'RESERVED', 'OCCUPIED', 'BLOCKED'
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(equipment_id, scheduled_date, start_time)
);

-- Sample scheduling
CREATE TABLE sample_scheduling (
    scheduling_id SERIAL PRIMARY KEY,
    sample_id INTEGER NOT NULL, -- References samples from main LIMS
    test_type_id INTEGER REFERENCES test_types(test_type_id),
    equipment_id INTEGER REFERENCES equipment(equipment_id),
    slot_id INTEGER REFERENCES scheduling_slots(slot_id),
    priority VARCHAR(20) NOT NULL, -- 'STAT', 'URGENT', 'ROUTINE'
    scheduled_date DATE NOT NULL,
    estimated_start_time TIME,
    estimated_end_time TIME,
    actual_start_time TIMESTAMP,
    actual_end_time TIMESTAMP,
    status VARCHAR(20) DEFAULT 'SCHEDULED', -- 'SCHEDULED', 'IN_PROGRESS', 'COMPLETED', 'CANCELLED'
    technician_id VARCHAR(50), -- Could reference staff table
    notes TEXT,
    retry_count INTEGER DEFAULT 0,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Resource reservations
CREATE TABLE resource_reservations (
    reservation_id SERIAL PRIMARY KEY,
    scheduling_id INTEGER REFERENCES sample_scheduling(scheduling_id),
    inventory_id INTEGER REFERENCES inventory_items(inventory_id),
    quantity_reserved INTEGER NOT NULL,
    reservation_date DATE DEFAULT CURRENT_DATE,
    expiration_date DATE,
    status VARCHAR(20) DEFAULT 'ACTIVE', -- 'ACTIVE', 'CONSUMED', 'EXPIRED', 'CANCELLED'
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ==========================================
-- QUALITY CONTROL AND MAINTENANCE
-- ==========================================

-- Equipment maintenance log
CREATE TABLE equipment_maintenance (
    maintenance_id SERIAL PRIMARY KEY,
    equipment_id INTEGER REFERENCES equipment(equipment_id),
    maintenance_type VARCHAR(50) NOT NULL, -- 'PREVENTIVE', 'CORRECTIVE', 'CALIBRATION'
    performed_by VARCHAR(100),
    performed_date DATE NOT NULL,
    description TEXT,
    cost DECIMAL(10,2),
    next_maintenance_date DATE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Quality control results
CREATE TABLE quality_control (
    qc_id SERIAL PRIMARY KEY,
    equipment_id INTEGER REFERENCES equipment(equipment_id),
    test_type_id INTEGER REFERENCES test_types(test_type_id),
    control_lot VARCHAR(50),
    run_date DATE NOT NULL,
    expected_value DECIMAL(10,4),
    actual_value DECIMAL(10,4),
    tolerance_range DECIMAL(10,4),
    pass_fail VARCHAR(10) NOT NULL, -- 'PASS', 'FAIL'
    technician_id VARCHAR(50),
    notes TEXT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ==========================================
-- VIEWS FOR SCHEDULING AGENT
-- ==========================================

-- Available equipment for scheduling
CREATE VIEW available_equipment AS
SELECT 
    e.equipment_id,
    e.equipment_name,
    e.equipment_type,
    e.location_id,
    l.location_name,
    e.max_concurrent_tests,
    e.current_test_count,
    (e.max_concurrent_tests - e.current_test_count) AS available_capacity,
    e.status
FROM equipment e
JOIN locations l ON e.location_id = l.location_id
WHERE e.status = 'AVAILABLE' 
  AND e.current_test_count < e.max_concurrent_tests
  AND l.is_active = TRUE;

-- Test scheduling summary
CREATE VIEW scheduling_summary AS
SELECT 
    ss.scheduling_id,
    ss.sample_id,
    tt.test_code,
    tt.test_name,
    tt.department,
    e.equipment_name,
    l.location_name,
    ss.priority,
    ss.scheduled_date,
    ss.estimated_start_time,
    ss.status,
    ss.retry_count
FROM sample_scheduling ss
JOIN test_types tt ON ss.test_type_id = tt.test_type_id
JOIN equipment e ON ss.equipment_id = e.equipment_id
JOIN locations l ON e.location_id = l.location_id
ORDER BY ss.scheduled_date, ss.estimated_start_time;

-- Resource availability
CREATE VIEW resource_availability AS
SELECT 
    c.item_name,
    c.item_type,
    c.unit_of_measure,
    l.location_name,
    ii.lot_number,
    ii.expiration_date,
    ii.quantity_available,
    ii.quantity_reserved,
    (ii.quantity_available - ii.quantity_reserved) AS quantity_free,
    ii.status
FROM inventory_items ii
JOIN consumables c ON ii.consumable_id = c.consumable_id
JOIN locations l ON ii.location_id = l.location_id
WHERE ii.status = 'AVAILABLE'
  AND ii.expiration_date > CURRENT_DATE
  AND (ii.quantity_available - ii.quantity_reserved) > 0
ORDER BY ii.expiration_date;

-- ==========================================
-- FUNCTIONS AND TRIGGERS
-- ==========================================

-- Function to update equipment usage count
CREATE OR REPLACE FUNCTION update_equipment_usage()
RETURNS TRIGGER AS $$
BEGIN
    -- When scheduling status changes, update equipment usage
    IF TG_OP = 'INSERT' AND NEW.status = 'IN_PROGRESS' THEN
        UPDATE equipment 
        SET current_test_count = current_test_count + 1,
            updated_at = CURRENT_TIMESTAMP
        WHERE equipment_id = NEW.equipment_id;
    ELSIF TG_OP = 'UPDATE' THEN
        IF OLD.status = 'IN_PROGRESS' AND NEW.status = 'COMPLETED' THEN
            UPDATE equipment 
            SET current_test_count = current_test_count - 1,
                updated_at = CURRENT_TIMESTAMP
            WHERE equipment_id = NEW.equipment_id;
        END IF;
    END IF;
    
    RETURN COALESCE(NEW, OLD);
END;
$$ LANGUAGE plpgsql;

-- Trigger to automatically update equipment usage
CREATE TRIGGER trigger_update_equipment_usage
    AFTER INSERT OR UPDATE ON sample_scheduling
    FOR EACH ROW
    EXECUTE FUNCTION update_equipment_usage();

-- Function to reserve resources
CREATE OR REPLACE FUNCTION reserve_resources(
    p_scheduling_id INTEGER,
    p_inventory_id INTEGER,
    p_quantity INTEGER
) RETURNS BOOLEAN AS $$
DECLARE
    available_quantity INTEGER;
BEGIN
    -- Check availability
    SELECT (quantity_available - quantity_reserved) 
    INTO available_quantity
    FROM inventory_items 
    WHERE inventory_id = p_inventory_id;
    
    IF available_quantity >= p_quantity THEN
        -- Reserve the resources
        UPDATE inventory_items 
        SET quantity_reserved = quantity_reserved + p_quantity,
            updated_at = CURRENT_TIMESTAMP
        WHERE inventory_id = p_inventory_id;
        
        -- Create reservation record
        INSERT INTO resource_reservations (
            scheduling_id, inventory_id, quantity_reserved
        ) VALUES (
            p_scheduling_id, p_inventory_id, p_quantity
        );
        
        RETURN TRUE;
    ELSE
        RETURN FALSE;
    END IF;
END;
$$ LANGUAGE plpgsql;

-- ==========================================
-- INDEXES FOR PERFORMANCE
-- ==========================================

-- Scheduling and resource lookup indexes
CREATE INDEX idx_equipment_status ON equipment(status);
CREATE INDEX idx_equipment_location ON equipment(location_id);
CREATE INDEX idx_sample_scheduling_date ON sample_scheduling(scheduled_date);
CREATE INDEX idx_sample_scheduling_priority ON sample_scheduling(priority);
CREATE INDEX idx_sample_scheduling_status ON sample_scheduling(status);
CREATE INDEX idx_inventory_status ON inventory_items(status);
CREATE INDEX idx_inventory_expiration ON inventory_items(expiration_date);
CREATE INDEX idx_resource_reservations_status ON resource_reservations(status);

-- Composite indexes for scheduling queries
CREATE INDEX idx_equipment_capabilities_lookup ON equipment_capabilities(equipment_id, test_type_id);
CREATE INDEX idx_scheduling_summary ON sample_scheduling(scheduled_date, priority, status);
CREATE INDEX idx_resource_availability ON inventory_items(status, expiration_date);

-- ==========================================
-- INITIAL DATA SETUP
-- ==========================================

-- Insert default locations
INSERT INTO locations (location_name, location_type, capacity) VALUES
('Main Lab', 'ROOM', 50),
('Hematology Bench', 'BENCH', 10),
('Chemistry Bench', 'BENCH', 10),
('Microbiology Bench', 'BENCH', 8),
('Sample Storage', 'STORAGE', 1000),
('Reagent Refrigerator', 'STORAGE', 200);

-- Insert default equipment
INSERT INTO equipment (equipment_name, equipment_type, manufacturer, model, location_id, max_concurrent_tests) VALUES
('Hematology Analyzer 1', 'ANALYZER', 'Sysmex', 'XN-1000', 2, 3),
('Chemistry Analyzer 1', 'ANALYZER', 'Roche', 'Cobas 6000', 3, 5),
('Microscope 1', 'MICROSCOPE', 'Olympus', 'BX51', 4, 1),
('Centrifuge 1', 'CENTRIFUGE', 'Eppendorf', '5810R', 2, 2);

-- Insert default test types
INSERT INTO test_types (test_code, test_name, department, estimated_duration_minutes) VALUES
('CBC', 'Complete Blood Count', 'HEMATOLOGY', 15),
('BMP', 'Basic Metabolic Panel', 'CHEMISTRY', 20),
('LIPID', 'Lipid Panel', 'CHEMISTRY', 25),
('DIFF', 'Differential Count', 'HEMATOLOGY', 30),
('GLUCOSE', 'Glucose', 'CHEMISTRY', 10),
('CULTURE', 'Blood Culture', 'MICROBIOLOGY', 60);

-- Insert equipment capabilities
INSERT INTO equipment_capabilities (equipment_id, test_type_id) VALUES
(1, 1), -- Hematology Analyzer can do CBC
(1, 4), -- Hematology Analyzer can do DIFF
(2, 2), -- Chemistry Analyzer can do BMP
(2, 3), -- Chemistry Analyzer can do LIPID
(2, 5), -- Chemistry Analyzer can do GLUCOSE
(3, 4), -- Microscope can do DIFF
(4, 1), -- Centrifuge can assist with CBC
(4, 2); -- Centrifuge can assist with BMP

-- Insert basic consumables
INSERT INTO consumables (item_name, item_type, unit_of_measure) VALUES
('EDTA Tube', 'TUBE', 'EACH'),
('Serum Separator Tube', 'TUBE', 'EACH'),
('CBC Reagent', 'REAGENT', 'ML'),
('Chemistry Reagent Kit', 'REAGENT', 'KIT'),
('Quality Control Material', 'CONTROL', 'VIAL');

-- Insert initial inventory
INSERT INTO inventory_items (consumable_id, location_id, lot_number, expiration_date, quantity_available) VALUES
(1, 5, 'LOT001', '2025-12-31', 1000),
(2, 5, 'LOT002', '2025-12-31', 1000),
(3, 6, 'LOT003', '2025-08-31', 500),
(4, 6, 'LOT004', '2025-09-30', 100),
(5, 6, 'LOT005', '2025-07-31', 50);

COMMIT;
