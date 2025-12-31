-- Equal Grains Examples (One-to-One Joins)
-- Cases 1-4 from the paper

SET search_path TO experiments, public;

-- ============================================================================
-- CASE 1: Jk = Grain
-- ============================================================================
-- Customer (G = CustomerId) and LoyalCustomer (G = CustomerId)
-- Join: ON CustomerId
-- Expected Grain: CustomerId

DROP TABLE IF EXISTS customer_case1 CASCADE;
CREATE TABLE customer_case1 (
    customer_id INTEGER PRIMARY KEY,
    customer_name VARCHAR(100),
    registration_date DATE
);

DROP TABLE IF EXISTS loyal_customer_case1 CASCADE;
CREATE TABLE loyal_customer_case1 (
    customer_id INTEGER PRIMARY KEY,
    loyalty_points INTEGER,
    loyalty_tier VARCHAR(20)
);

-- Generate 1000+ rows
INSERT INTO customer_case1 (customer_id, customer_name, registration_date)
SELECT 
    generate_series(1, 1000) as customer_id,
    'Customer ' || generate_series(1, 1000)::text as customer_name,
    '2020-01-01'::date + (random() * 1825)::int as registration_date;

-- Generate loyal customers (subset of customers, 60% overlap)
INSERT INTO loyal_customer_case1 (customer_id, loyalty_points, loyalty_tier)
SELECT 
    generate_series(1, 600) as customer_id,
    (random() * 10000)::int as loyalty_points,
    CASE (random() * 3)::int
        WHEN 0 THEN 'Bronze'
        WHEN 1 THEN 'Silver'
        ELSE 'Gold'
    END as loyalty_tier;

DROP TABLE IF EXISTS result_equal_grains_case1 CASCADE;
CREATE TABLE result_equal_grains_case1 (
    customer_id INTEGER PRIMARY KEY,  -- Expected grain: CustomerId
    customer_name VARCHAR(100),
    registration_date DATE,
    loyalty_points INTEGER,
    loyalty_tier VARCHAR(20)
);

INSERT INTO result_equal_grains_case1 
SELECT 
    c.customer_id,
    c.customer_name,
    c.registration_date,
    l.loyalty_points,
    l.loyalty_tier
FROM customer_case1 c
INNER JOIN loyal_customer_case1 l ON c.customer_id = l.customer_id;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_equal_grains_case1;
    SELECT COUNT(DISTINCT customer_id) INTO unique_rows FROM result_equal_grains_case1;
    RAISE NOTICE 'Equal Grains Case 1: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- ============================================================================
-- CASE 2: Jk ⊂ Grain (proper subset)
-- ============================================================================
-- Customer (G = CustomerId × RegionId) and CustomerSegment (G = CustomerId × SegmentId)
-- Join: ON CustomerId
-- Expected Grain: RegionId × SegmentId × CustomerId

DROP TABLE IF EXISTS customer_region_case2 CASCADE;
CREATE TABLE customer_region_case2 (
    customer_id INTEGER,
    region_id INTEGER,
    customer_name VARCHAR(100),
    PRIMARY KEY (customer_id, region_id)  -- Grain: CustomerId × RegionId
);

DROP TABLE IF EXISTS customer_segment_case2 CASCADE;
CREATE TABLE customer_segment_case2 (
    customer_id INTEGER,
    segment_id INTEGER,
    segment_name VARCHAR(50),
    PRIMARY KEY (customer_id, segment_id)  -- Grain: CustomerId × SegmentId
);

-- Generate 1000+ rows for customer_region (ensure grain uniqueness)
INSERT INTO customer_region_case2 (customer_id, region_id, customer_name)
SELECT 
    ((row_number() OVER () - 1) / 10 + 1)::int as customer_id,  -- 100 unique customers
    ((row_number() OVER () - 1) % 10 + 1)::int as region_id,     -- 10 regions
    'Customer ' || row_number() OVER ()::text as customer_name
FROM generate_series(1, 1000);

-- Generate 1000+ rows for customer_segment (ensure grain uniqueness)
INSERT INTO customer_segment_case2 (customer_id, segment_id, segment_name)
SELECT 
    ((row_number() OVER () - 1) / 5 + 1)::int as customer_id,   -- 200 unique customers
    ((row_number() OVER () - 1) % 5 + 1)::int as segment_id,     -- 5 segments
    'Segment ' || row_number() OVER ()::text as segment_name
FROM generate_series(1, 1000);

DROP TABLE IF EXISTS result_equal_grains_case2 CASCADE;
CREATE TABLE result_equal_grains_case2 (
    region_id INTEGER,
    segment_id INTEGER,
    customer_id INTEGER,
    customer_name VARCHAR(100),
    segment_name VARCHAR(50),
    PRIMARY KEY (region_id, segment_id, customer_id)  -- Expected grain: RegionId × SegmentId × CustomerId
);

INSERT INTO result_equal_grains_case2 
SELECT DISTINCT
    cr.region_id,
    cs.segment_id,
    cr.customer_id,
    cr.customer_name,
    cs.segment_name
FROM customer_region_case2 cr
INNER JOIN customer_segment_case2 cs ON cr.customer_id = cs.customer_id;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_equal_grains_case2;
    SELECT COUNT(DISTINCT (region_id, segment_id, customer_id)) INTO unique_rows FROM result_equal_grains_case2;
    RAISE NOTICE 'Equal Grains Case 2: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- ============================================================================
-- CASE 3: Jk ∩ Grain ≠ ∅ but Jk ⊄ Grain
-- ============================================================================
-- Customer (G = CustomerId × RegionId, ProductId is non-grain) 
-- Order (G = OrderId × OrderDate, ProductId is non-grain)
-- Join: ON CustomerId × ProductId
-- Expected Grain: RegionId × OrderDate × CustomerId

DROP TABLE IF EXISTS customer_product_case3 CASCADE;
CREATE TABLE customer_product_case3 (
    customer_id INTEGER,
    region_id INTEGER,
    product_id INTEGER,
    customer_name VARCHAR(100),
    PRIMARY KEY (customer_id, region_id)  -- Grain: CustomerId × RegionId
);

DROP TABLE IF EXISTS order_product_case3 CASCADE;
CREATE TABLE order_product_case3 (
    order_id INTEGER,
    customer_id INTEGER,
    order_date DATE,
    product_id INTEGER,
    order_amount DECIMAL(10,2),
    PRIMARY KEY (order_id, order_date)  -- Grain: OrderId × OrderDate
);

-- Generate 1000+ rows for customer_product (ensure grain uniqueness)
INSERT INTO customer_product_case3 (customer_id, region_id, product_id, customer_name)
SELECT 
    ((row_number() OVER () - 1) / 10 + 1)::int as customer_id,  -- 100 unique customers
    ((row_number() OVER () - 1) % 10 + 1)::int as region_id,     -- 10 regions
    (random() * 50 + 1)::int as product_id,
    'Customer ' || row_number() OVER ()::text as customer_name
FROM generate_series(1, 1000);

-- Generate 1000+ rows for order_product
INSERT INTO order_product_case3 (order_id, customer_id, order_date, product_id, order_amount)
SELECT DISTINCT ON (order_id, order_date)
    generate_series(1, 1000) as order_id,
    (random() * 400 + 1)::int as customer_id,
    '2020-01-01'::date + (random() * 1825)::int as order_date,
    (random() * 50 + 1)::int as product_id,
    (random() * 1000 + 10)::decimal as order_amount
FROM generate_series(1, 1500)
ORDER BY order_id, order_date, random()
LIMIT 1000;

DROP TABLE IF EXISTS result_equal_grains_case3 CASCADE;
CREATE TABLE result_equal_grains_case3 (
    region_id INTEGER,
    order_date DATE,
    customer_id INTEGER,
    product_id INTEGER,
    customer_name VARCHAR(100),
    order_id INTEGER,
    order_amount DECIMAL(10,2),
    PRIMARY KEY (region_id, order_date, customer_id)  -- Expected grain: RegionId × OrderDate × CustomerId
);

INSERT INTO result_equal_grains_case3 
SELECT DISTINCT
    cp.region_id,
    op.order_date,
    cp.customer_id,
    cp.product_id,
    cp.customer_name,
    op.order_id,
    op.order_amount
FROM customer_product_case3 cp
INNER JOIN order_product_case3 op ON cp.customer_id = op.customer_id 
    AND cp.product_id = op.product_id;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_equal_grains_case3;
    SELECT COUNT(DISTINCT (region_id, order_date, customer_id)) INTO unique_rows FROM result_equal_grains_case3;
    RAISE NOTICE 'Equal Grains Case 3: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- ============================================================================
-- CASE 4: Jk ∩ Grain = ∅
-- ============================================================================
-- Customer (G = CustomerId) and LoyaltyCustomer (G = CustomerId)
-- Join: ON Email (non-grain field)
-- Expected Grain: CustomerId × CustomerId (requires distinct column names)

DROP TABLE IF EXISTS customer_email_case4 CASCADE;
CREATE TABLE customer_email_case4 (
    customer_id INTEGER PRIMARY KEY,  -- Grain: CustomerId
    email VARCHAR(100),
    customer_name VARCHAR(100)
);

DROP TABLE IF EXISTS loyalty_customer_email_case4 CASCADE;
CREATE TABLE loyalty_customer_email_case4 (
    customer_id INTEGER PRIMARY KEY,  -- Grain: CustomerId
    email VARCHAR(100),
    loyalty_points INTEGER
);

-- Generate 1000+ rows
INSERT INTO customer_email_case4 (customer_id, email, customer_name)
SELECT 
    generate_series(1, 1000) as customer_id,
    'customer' || generate_series(1, 1000)::text || '@example.com' as email,
    'Customer ' || generate_series(1, 1000)::text as customer_name;

-- Generate loyalty customers with overlapping emails (some customers share emails)
INSERT INTO loyalty_customer_email_case4 (customer_id, email, loyalty_points)
SELECT 
    generate_series(1, 800) as customer_id,
    'customer' || ((random() * 600 + 1)::int)::text || '@example.com' as email,
    (random() * 10000)::int as loyalty_points;

DROP TABLE IF EXISTS result_equal_grains_case4 CASCADE;
CREATE TABLE result_equal_grains_case4 (
    customer_id_r1 INTEGER,
    customer_id_r2 INTEGER,
    email VARCHAR(100),
    customer_name VARCHAR(100),
    loyalty_points INTEGER,
    PRIMARY KEY (customer_id_r1, customer_id_r2)  -- Expected grain: CustomerId × CustomerId
);

INSERT INTO result_equal_grains_case4 
SELECT DISTINCT
    c.customer_id as customer_id_r1,
    l.customer_id as customer_id_r2,
    c.email,
    c.customer_name,
    l.loyalty_points
FROM customer_email_case4 c
INNER JOIN loyalty_customer_email_case4 l ON c.email = l.email;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_equal_grains_case4;
    SELECT COUNT(DISTINCT (customer_id_r1, customer_id_r2)) INTO unique_rows FROM result_equal_grains_case4;
    RAISE NOTICE 'Equal Grains Case 4: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

DO $$
BEGIN
    RAISE NOTICE '========================================';
    RAISE NOTICE 'Equal Grains Examples Completed';
    RAISE NOTICE '========================================';
END $$;

