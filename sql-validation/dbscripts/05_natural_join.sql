-- Natural Join Examples
-- Cases A and B from the paper

SET search_path TO experiments, public;

-- ============================================================================
-- CASE A: Comparable Jk-portions
-- ============================================================================
-- Customer (R1 = CustomerId × CustomerName × RegionId, G[R1] = CustomerId × RegionId)
-- CustomerSegment (R2 = CustomerId × RegionId × SegmentId, G[R2] = CustomerId × RegionId)
-- Natural Join: ON all common fields (CustomerId, RegionId)
-- Expected Grain: CustomerId × RegionId

DROP TABLE IF EXISTS customer_natural_casea CASCADE;
CREATE TABLE customer_natural_casea (
    customer_id INTEGER,
    customer_name VARCHAR(100),
    region_id INTEGER,
    PRIMARY KEY (customer_id, region_id)  -- Grain: CustomerId × RegionId
);

DROP TABLE IF EXISTS customer_segment_natural_casea CASCADE;
CREATE TABLE customer_segment_natural_casea (
    customer_id INTEGER,
    region_id INTEGER,
    segment_id INTEGER,
    segment_name VARCHAR(50),
    PRIMARY KEY (customer_id, region_id)  -- Grain: CustomerId × RegionId
);

-- Generate 1000+ rows (ensure grain uniqueness)
INSERT INTO customer_natural_casea (customer_id, customer_name, region_id)
SELECT 
    ((row_number() OVER () - 1) / 10 + 1)::int as customer_id,  -- 100 unique customers
    'Customer ' || row_number() OVER ()::text as customer_name,
    ((row_number() OVER () - 1) % 10 + 1)::int as region_id     -- 10 regions
FROM generate_series(1, 1000);

INSERT INTO customer_segment_natural_casea (customer_id, region_id, segment_id, segment_name)
SELECT 
    ((row_number() OVER () - 1) / 10 + 1)::int as customer_id,  -- 100 unique customers (overlap)
    ((row_number() OVER () - 1) % 10 + 1)::int as region_id,     -- 10 regions (overlap)
    ((row_number() OVER () - 1) % 5 + 1)::int as segment_id,     -- 5 segments
    'Segment ' || row_number() OVER ()::text as segment_name
FROM generate_series(1, 1000);

DROP TABLE IF EXISTS result_natural_join_casea CASCADE;
CREATE TABLE result_natural_join_casea (
    customer_id INTEGER,
    region_id INTEGER,
    customer_name VARCHAR(100),
    segment_id INTEGER,
    segment_name VARCHAR(50),
    PRIMARY KEY (customer_id, region_id)  -- Expected grain: CustomerId × RegionId
);

-- Natural join: joins on all common columns (customer_id, region_id)
INSERT INTO result_natural_join_casea 
SELECT DISTINCT
    c.customer_id,
    c.region_id,
    c.customer_name,
    cs.segment_id,
    cs.segment_name
FROM customer_natural_casea c
INNER JOIN customer_segment_natural_casea cs 
    ON c.customer_id = cs.customer_id 
    AND c.region_id = cs.region_id;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_natural_join_casea;
    SELECT COUNT(DISTINCT (customer_id, region_id)) INTO unique_rows FROM result_natural_join_casea;
    RAISE NOTICE 'Natural Join Case A: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- ============================================================================
-- CASE B: Incomparable Jk-portions
-- ============================================================================
-- R1 = A × B × C with G[R1] = A × B
-- R2 = B × C × D with G[R2] = C × D
-- Natural Join: ON (B, C)
-- Expected Grain: A × D × B × C

DROP TABLE IF EXISTS r1_abc_natural_caseb CASCADE;
CREATE TABLE r1_abc_natural_caseb (
    col_a INTEGER,
    col_b INTEGER,
    col_c INTEGER,
    PRIMARY KEY (col_a, col_b)  -- Grain: A × B
);

DROP TABLE IF EXISTS r2_bcd_natural_caseb CASCADE;
CREATE TABLE r2_bcd_natural_caseb (
    col_b INTEGER,
    col_c INTEGER,
    col_d INTEGER,
    PRIMARY KEY (col_c, col_d)  -- Grain: C × D
);

-- Generate 1000+ rows
INSERT INTO r1_abc_natural_caseb (col_a, col_b, col_c)
SELECT DISTINCT ON (col_a, col_b)
    (random() * 200 + 1)::int as col_a,
    (random() * 100 + 1)::int as col_b,
    (random() * 300 + 1)::int as col_c
FROM generate_series(1, 2000)
ORDER BY col_a, col_b, random()
LIMIT 1000;

INSERT INTO r2_bcd_natural_caseb (col_b, col_c, col_d)
SELECT DISTINCT ON (col_c, col_d)
    (random() * 100 + 1)::int as col_b,
    (random() * 300 + 1)::int as col_c,
    (random() * 150 + 1)::int as col_d
FROM generate_series(1, 2000)
ORDER BY col_c, col_d, random()
LIMIT 1000;

DROP TABLE IF EXISTS result_natural_join_caseb CASCADE;
CREATE TABLE result_natural_join_caseb (
    col_a INTEGER,
    col_d INTEGER,
    col_b INTEGER,
    col_c INTEGER,
    PRIMARY KEY (col_a, col_d, col_b, col_c)  -- Expected grain: A × D × B × C
);

-- Natural join: joins on all common columns (col_b, col_c)
INSERT INTO result_natural_join_caseb 
SELECT DISTINCT
    r1.col_a,
    r2.col_d,
    r1.col_b,
    r1.col_c
FROM r1_abc_natural_caseb r1
INNER JOIN r2_bcd_natural_caseb r2 
    ON r1.col_b = r2.col_b 
    AND r1.col_c = r2.col_c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_natural_join_caseb;
    SELECT COUNT(DISTINCT (col_a, col_d, col_b, col_c)) INTO unique_rows FROM result_natural_join_caseb;
    RAISE NOTICE 'Natural Join Case B: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

DO $$
BEGIN
    RAISE NOTICE '========================================';
    RAISE NOTICE 'Natural Join Examples Completed';
    RAISE NOTICE '========================================';
END $$;

