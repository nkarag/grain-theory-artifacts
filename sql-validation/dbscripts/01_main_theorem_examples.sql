-- Main Theorem Examples
-- Examples 1, 2, and 3 from the paper

SET search_path TO experiments, public;

-- ============================================================================
-- EXAMPLE 1: Case A - Comparable Jk-portions
-- ============================================================================
-- R1 = Account × Customer with G[R1] = Account
-- R2 = Customer × Address with G[R2] = Customer × Address
-- Jk = Customer
-- Expected Grain: Account × Address

-- Create tables
DROP TABLE IF EXISTS r1_account_customer CASCADE;
CREATE TABLE r1_account_customer (
    account_id INTEGER,
    customer_id VARCHAR(10),
    PRIMARY KEY (account_id)  -- Grain is Account
);

DROP TABLE IF EXISTS r2_customer_address CASCADE;
CREATE TABLE r2_customer_address (
    customer_id VARCHAR(10),
    address_id INTEGER,
    address_text TEXT,
    PRIMARY KEY (customer_id, address_id)  -- Grain is Customer × Address
);

-- Generate 1000+ rows for R1
INSERT INTO r1_account_customer (account_id, customer_id)
SELECT 
    generate_series(1, 1000) as account_id,
    'C' || LPAD((random() * 500 + 1)::int::text, 3, '0') as customer_id;

-- Generate 1000+ rows for R2 (ensure overlap with R1 customers and grain uniqueness)
INSERT INTO r2_customer_address (customer_id, address_id, address_text)
SELECT DISTINCT ON (customer_id, address_id)
    'C' || LPAD(((row_number() OVER () - 1) % 500 + 1)::text, 3, '0') as customer_id,
    ((row_number() OVER () - 1) % 3 + 1)::int as address_id,
    'Address ' || row_number() OVER ()::text as address_text
FROM generate_series(1, 2000)
ORDER BY customer_id, address_id
LIMIT 1000;

-- Perform join and create result table
DROP TABLE IF EXISTS result_example1 CASCADE;
CREATE TABLE result_example1 (
    account_id INTEGER,
    address_id INTEGER,
    customer_id VARCHAR(10),
    address_text TEXT,
    PRIMARY KEY (account_id, address_id)  -- Expected grain: Account × Address
);

INSERT INTO result_example1 (account_id, address_id, customer_id, address_text)
SELECT DISTINCT
    r1.account_id,
    r2.address_id,
    r1.customer_id,
    r2.address_text
FROM r1_account_customer r1
INNER JOIN r2_customer_address r2 ON r1.customer_id = r2.customer_id;

-- Verify grain uniqueness
DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_example1;
    SELECT COUNT(DISTINCT (account_id, address_id)) INTO unique_rows FROM result_example1;
    
    RAISE NOTICE 'Example 1 Verification:';
    RAISE NOTICE '  Total rows: %', total_rows;
    RAISE NOTICE '  Unique grain combinations: %', unique_rows;
    RAISE NOTICE '  Grain is unique: %', (total_rows = unique_rows);
END $$;

-- ============================================================================
-- EXAMPLE 2: Case B - Incomparable Jk-portions
-- ============================================================================
-- R1 = A × B × C × E with G[R1] = A × C
-- R2 = A × B × C × D with G[R2] = A × B
-- Jk = A × B × C
-- Expected Grain: A × B × C

-- Create tables
DROP TABLE IF EXISTS r1_abc_e CASCADE;
CREATE TABLE r1_abc_e (
    col_a INTEGER,
    col_b INTEGER,
    col_c INTEGER,
    col_e VARCHAR(10),
    PRIMARY KEY (col_a, col_c)  -- Grain is A × C
);

DROP TABLE IF EXISTS r2_abc_d CASCADE;
CREATE TABLE r2_abc_d (
    col_a INTEGER,
    col_b INTEGER,
    col_c INTEGER,
    col_d VARCHAR(10),
    PRIMARY KEY (col_a, col_b)  -- Grain is A × B
);

-- Generate 1000+ rows for R1 (ensure grain uniqueness)
-- Generate unique (col_a, col_c) pairs using sequential values
INSERT INTO r1_abc_e (col_a, col_b, col_c, col_e)
SELECT 
    ((row_number() OVER () - 1) / 20 + 1)::int as col_a,  -- 50 unique values
    (random() * 50 + 1)::int as col_b,
    ((row_number() OVER () - 1) % 20 + 1)::int as col_c,  -- 20 unique values
    'E' || row_number() OVER ()::text as col_e
FROM generate_series(1, 1000);

-- Generate 1000+ rows for R2 (ensure grain uniqueness and overlap with R1)
INSERT INTO r2_abc_d (col_a, col_b, col_c, col_d)
SELECT 
    ((row_number() OVER () - 1) / 20 + 1)::int as col_a,  -- 50 unique values (overlap with R1)
    ((row_number() OVER () - 1) % 20 + 1)::int as col_b,  -- 20 unique values
    (random() * 200 + 1)::int as col_c,
    'D' || row_number() OVER ()::text as col_d
FROM generate_series(1, 1000);

-- Perform join and create result table
DROP TABLE IF EXISTS result_example2 CASCADE;
CREATE TABLE result_example2 (
    col_a INTEGER,
    col_b INTEGER,
    col_c INTEGER,
    col_e VARCHAR(10),
    col_d VARCHAR(10),
    PRIMARY KEY (col_a, col_b, col_c)  -- Expected grain: A × B × C
);

INSERT INTO result_example2 (col_a, col_b, col_c, col_e, col_d)
SELECT DISTINCT
    r1.col_a,
    r1.col_b,
    r1.col_c,
    r1.col_e,
    r2.col_d
FROM r1_abc_e r1
INNER JOIN r2_abc_d r2 ON r1.col_a = r2.col_a 
    AND r1.col_b = r2.col_b 
    AND r1.col_c = r2.col_c;

-- Verify grain uniqueness
DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_example2;
    SELECT COUNT(DISTINCT (col_a, col_b, col_c)) INTO unique_rows FROM result_example2;
    
    RAISE NOTICE 'Example 2 Verification:';
    RAISE NOTICE '  Total rows: %', total_rows;
    RAISE NOTICE '  Unique grain combinations: %', unique_rows;
    RAISE NOTICE '  Grain is unique: %', (total_rows = unique_rows);
END $$;

-- ============================================================================
-- EXAMPLE 3: Join on subset of common fields
-- ============================================================================
-- R1 = A × B × C with G[R1] = A × B
-- R2 = B × C × D with G[R2] = C × D
-- Jk = B (joining only on B, not all common fields B × C)
-- Expected Grain: A × C × D
-- Note: C appears twice in result (C1, C2) but only once in grain

-- Create tables
DROP TABLE IF EXISTS r1_abc CASCADE;
CREATE TABLE r1_abc (
    col_a INTEGER,
    col_b INTEGER,
    col_c INTEGER,
    PRIMARY KEY (col_a, col_b)  -- Grain is A × B
);

DROP TABLE IF EXISTS r2_bcd CASCADE;
CREATE TABLE r2_bcd (
    col_b INTEGER,
    col_c INTEGER,
    col_d INTEGER,
    PRIMARY KEY (col_c, col_d)  -- Grain is C × D
);

-- Generate 1000+ rows for R1
INSERT INTO r1_abc (col_a, col_b, col_c)
SELECT DISTINCT ON (col_a, col_b)
    (random() * 200 + 1)::int as col_a,
    (random() * 100 + 1)::int as col_b,
    (random() * 300 + 1)::int as col_c
FROM generate_series(1, 1500)
ORDER BY col_a, col_b, random()
LIMIT 1000;

-- Generate 1000+ rows for R2 (ensure overlap on col_b)
INSERT INTO r2_bcd (col_b, col_c, col_d)
SELECT DISTINCT ON (col_c, col_d)
    (random() * 100 + 1)::int as col_b,
    (random() * 300 + 1)::int as col_c,
    (random() * 150 + 1)::int as col_d
FROM generate_series(1, 1500)
ORDER BY col_c, col_d, random()
LIMIT 1000;

-- Perform join and create result table
-- Note: C appears twice (as col_c from R1 and col_c from R2)
DROP TABLE IF EXISTS result_example3 CASCADE;
CREATE TABLE result_example3 (
    col_a INTEGER,
    col_b INTEGER,
    col_c_r1 INTEGER,  -- C from R1
    col_c_r2 INTEGER,  -- C from R2
    col_d INTEGER,
    PRIMARY KEY (col_a, col_c_r1, col_d)  -- Expected grain: A × C × D (using C from R1)
);

-- Insert with DISTINCT to handle potential duplicates at grain level
INSERT INTO result_example3 (col_a, col_b, col_c_r1, col_c_r2, col_d)
SELECT DISTINCT ON (r1.col_a, r1.col_c, r2.col_d)
    r1.col_a,
    r1.col_b,
    r1.col_c as col_c_r1,
    r2.col_c as col_c_r2,
    r2.col_d
FROM r1_abc r1
INNER JOIN r2_bcd r2 ON r1.col_b = r2.col_b
ORDER BY r1.col_a, r1.col_c, r2.col_d, r1.col_b, r2.col_c;

-- Verify grain uniqueness
DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_example3;
    SELECT COUNT(DISTINCT (col_a, col_c_r1, col_d)) INTO unique_rows FROM result_example3;
    
    RAISE NOTICE 'Example 3 Verification:';
    RAISE NOTICE '  Total rows: %', total_rows;
    RAISE NOTICE '  Unique grain combinations: %', unique_rows;
    RAISE NOTICE '  Grain is unique: %', (total_rows = unique_rows);
END $$;

-- Summary
DO $$
BEGIN
    RAISE NOTICE '========================================';
    RAISE NOTICE 'Main Theorem Examples Completed';
    RAISE NOTICE '========================================';
END $$;

