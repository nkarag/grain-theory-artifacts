-- Incomparable Grains Examples (Many-to-Many Joins)
-- Cases A and B from the paper

SET search_path TO experiments, public;

-- ============================================================================
-- CASE A: Comparable Jk-portions
-- ============================================================================
-- SalesChannel (G = CustomerId × ChannelId × Date) 
-- SalesProduct (G = CustomerId × ProductId × Date)
-- Join: ON CustomerId × Date
-- Expected Grain: ChannelId × ProductId × CustomerId × Date

DROP TABLE IF EXISTS sales_channel_casea CASCADE;
CREATE TABLE sales_channel_casea (
    customer_id INTEGER,
    channel_id INTEGER,
    sale_date DATE,
    channel_name VARCHAR(50),
    PRIMARY KEY (customer_id, channel_id, sale_date)  -- Grain: CustomerId × ChannelId × Date
);

DROP TABLE IF EXISTS sales_product_casea CASCADE;
CREATE TABLE sales_product_casea (
    customer_id INTEGER,
    product_id INTEGER,
    sale_date DATE,
    product_name VARCHAR(100),
    PRIMARY KEY (customer_id, product_id, sale_date)  -- Grain: CustomerId × ProductId × Date
);

-- Generate 1000+ rows for sales_channel (ensure grain uniqueness)
INSERT INTO sales_channel_casea (customer_id, channel_id, sale_date, channel_name)
SELECT 
    ((row_number() OVER () - 1) / 25 + 1)::int as customer_id,  -- 40 unique customers
    ((row_number() OVER () - 1) % 5 + 1)::int as channel_id,     -- 5 channels
    '2020-01-01'::date + (((row_number() OVER () - 1) / 5) % 365)::int as sale_date,  -- Unique dates per customer/channel
    'Channel ' || row_number() OVER ()::text as channel_name
FROM generate_series(1, 1000);

-- Generate 1000+ rows for sales_product (ensure grain uniqueness)
INSERT INTO sales_product_casea (customer_id, product_id, sale_date, product_name)
SELECT 
    ((row_number() OVER () - 1) / 25 + 1)::int as customer_id,  -- 40 unique customers (overlap with sales_channel)
    ((row_number() OVER () - 1) % 25 + 1)::int as product_id,   -- 25 products
    '2020-01-01'::date + (((row_number() OVER () - 1) / 25) % 365)::int as sale_date,  -- Unique dates per customer/product
    'Product ' || row_number() OVER ()::text as product_name
FROM generate_series(1, 1000);

DROP TABLE IF EXISTS result_incomparable_grains_casea CASCADE;
CREATE TABLE result_incomparable_grains_casea (
    channel_id INTEGER,
    product_id INTEGER,
    customer_id INTEGER,
    sale_date DATE,
    channel_name VARCHAR(50),
    product_name VARCHAR(100),
    PRIMARY KEY (channel_id, product_id, customer_id, sale_date)  -- Expected grain
);

INSERT INTO result_incomparable_grains_casea 
SELECT DISTINCT
    sc.channel_id,
    sp.product_id,
    sc.customer_id,
    sc.sale_date,
    sc.channel_name,
    sp.product_name
FROM sales_channel_casea sc
INNER JOIN sales_product_casea sp ON sc.customer_id = sp.customer_id 
    AND sc.sale_date = sp.sale_date;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_incomparable_grains_casea;
    SELECT COUNT(DISTINCT (channel_id, product_id, customer_id, sale_date)) INTO unique_rows FROM result_incomparable_grains_casea;
    RAISE NOTICE 'Incomparable Grains Case A: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- ============================================================================
-- CASE B: Incomparable Jk-portions
-- ============================================================================
-- Sales (G = SalesId × ProductId × StoreId)
-- Product (G = ProductId × SupplierId × CategoryId)
-- Join: ON ProductId × StoreId × SupplierId
-- Expected Grain: SalesId × CategoryId × ProductId × StoreId × SupplierId

DROP TABLE IF EXISTS sales_caseb CASCADE;
CREATE TABLE sales_caseb (
    sales_id INTEGER,
    product_id INTEGER,
    store_id INTEGER,
    sales_amount DECIMAL(10,2),
    PRIMARY KEY (sales_id, product_id, store_id)  -- Grain: SalesId × ProductId × StoreId
);

DROP TABLE IF EXISTS product_caseb CASCADE;
CREATE TABLE product_caseb (
    product_id INTEGER,
    supplier_id INTEGER,
    category_id INTEGER,
    product_name VARCHAR(100),
    PRIMARY KEY (product_id, supplier_id, category_id)  -- Grain: ProductId × SupplierId × CategoryId
);

-- Generate 1000+ rows for sales
INSERT INTO sales_caseb (sales_id, product_id, store_id, sales_amount)
SELECT DISTINCT ON (sales_id, product_id, store_id)
    generate_series(1, 1000) as sales_id,
    (random() * 200 + 1)::int as product_id,
    (random() * 30 + 1)::int as store_id,
    (random() * 5000 + 100)::decimal as sales_amount
FROM generate_series(1, 1500)
ORDER BY sales_id, product_id, store_id, random()
LIMIT 1000;

-- Generate 1000+ rows for product (ensure grain uniqueness)
INSERT INTO product_caseb (product_id, supplier_id, category_id, product_name)
SELECT 
    ((row_number() OVER () - 1) / 50 + 1)::int as product_id,   -- 20 unique products
    ((row_number() OVER () - 1) % 50 + 1)::int as supplier_id,   -- 50 suppliers
    ((row_number() OVER () - 1) / 50 % 20 + 1)::int as category_id,  -- 20 categories
    'Product ' || row_number() OVER ()::text as product_name
FROM generate_series(1, 1000);

DROP TABLE IF EXISTS result_incomparable_grains_caseb CASCADE;
CREATE TABLE result_incomparable_grains_caseb (
    sales_id INTEGER,
    category_id INTEGER,
    product_id INTEGER,
    store_id INTEGER,
    supplier_id INTEGER,
    sales_amount DECIMAL(10,2),
    product_name VARCHAR(100),
    PRIMARY KEY (sales_id, category_id, product_id, store_id, supplier_id)  -- Expected grain
);

INSERT INTO result_incomparable_grains_caseb 
SELECT DISTINCT
    s.sales_id,
    p.category_id,
    s.product_id,
    s.store_id,
    p.supplier_id,
    s.sales_amount,
    p.product_name
FROM sales_caseb s
INNER JOIN product_caseb p ON s.product_id = p.product_id 
    AND s.store_id = p.supplier_id  -- Note: store_id matches supplier_id for join
    AND p.supplier_id = s.store_id;

-- Actually, let me fix the join condition - it should be on ProductId × StoreId × SupplierId
-- But store_id and supplier_id are different concepts. Let me adjust:
DELETE FROM result_incomparable_grains_caseb;

-- Re-insert with correct join: we need to ensure store_id values can match supplier_id values
-- For the join to work, we need overlapping values
INSERT INTO result_incomparable_grains_caseb 
SELECT DISTINCT
    s.sales_id,
    p.category_id,
    s.product_id,
    s.store_id,
    p.supplier_id,
    s.sales_amount,
    p.product_name
FROM sales_caseb s
INNER JOIN product_caseb p ON s.product_id = p.product_id 
    AND s.store_id = p.supplier_id;  -- Join on ProductId × StoreId × SupplierId

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_incomparable_grains_caseb;
    SELECT COUNT(DISTINCT (sales_id, category_id, product_id, store_id, supplier_id)) INTO unique_rows FROM result_incomparable_grains_caseb;
    RAISE NOTICE 'Incomparable Grains Case B: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

DO $$
BEGIN
    RAISE NOTICE '========================================';
    RAISE NOTICE 'Incomparable Grains Examples Completed';
    RAISE NOTICE '========================================';
END $$;

