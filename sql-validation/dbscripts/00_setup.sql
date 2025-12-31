-- Setup script for Grain Inference Experiments
-- This script sets up the experiments schema and helper functions

-- Ensure we're using the experiments schema
SET search_path TO experiments, public;

-- Create helper function to check for duplicates in result tables
CREATE OR REPLACE FUNCTION check_grain_uniqueness(
    table_name TEXT,
    grain_columns TEXT[]
) RETURNS TABLE(
    total_rows BIGINT,
    unique_grain_rows BIGINT,
    has_duplicates BOOLEAN
) AS $$
DECLARE
    col_list TEXT;
BEGIN
    -- Build column list for the query
    col_list := array_to_string(grain_columns, ', ');
    
    RETURN QUERY EXECUTE format('
        SELECT 
            COUNT(*) as total_rows,
            COUNT(DISTINCT (%s)) as unique_grain_rows,
            (COUNT(*) > COUNT(DISTINCT (%s))) as has_duplicates
        FROM %I
    ', col_list, col_list, table_name);
END;
$$ LANGUAGE plpgsql;

-- Create helper function to verify grain columns exist
CREATE OR REPLACE FUNCTION verify_grain_columns(
    table_name TEXT,
    expected_columns TEXT[]
) RETURNS TABLE(
    column_exists BOOLEAN,
    missing_columns TEXT[]
) AS $$
DECLARE
    missing TEXT[];
    col TEXT;
BEGIN
    missing := ARRAY[]::TEXT[];
    
    FOREACH col IN ARRAY expected_columns
    LOOP
        IF NOT EXISTS (
            SELECT 1 
            FROM information_schema.columns 
            WHERE table_schema = 'experiments' 
            AND table_name = verify_grain_columns.table_name
            AND column_name = col
        ) THEN
            missing := array_append(missing, col);
        END IF;
    END LOOP;
    
    RETURN QUERY SELECT 
        (array_length(missing, 1) IS NULL) as column_exists,
        missing as missing_columns;
END;
$$ LANGUAGE plpgsql;

-- Log setup completion
DO $$
BEGIN
    RAISE NOTICE 'Setup completed: Helper functions created';
END $$;







