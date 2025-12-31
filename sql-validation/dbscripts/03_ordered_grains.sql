-- Ordered Grains Examples (One-to-Many Joins)
-- Cases 1-4 from the paper

SET search_path TO experiments, public;

-- ============================================================================
-- CASE 1: G[R2] ⊆ Jk
-- ============================================================================
-- OrderDetail (G = OrderId × LineItemId) and Order (G = OrderId)
-- Join: ON OrderId
-- Expected Grain: OrderId × LineItemId

DROP TABLE IF EXISTS order_detail_case1 CASCADE;
CREATE TABLE order_detail_case1 (
    order_id INTEGER,
    line_item_id INTEGER,
    product_id INTEGER,
    quantity INTEGER,
    PRIMARY KEY (order_id, line_item_id)  -- Grain: OrderId × LineItemId
);

DROP TABLE IF EXISTS order_case1 CASCADE;
CREATE TABLE order_case1 (
    order_id INTEGER PRIMARY KEY,  -- Grain: OrderId
    order_date DATE,
    total_amount DECIMAL(10,2)
);

-- Generate 1000+ rows for orders
INSERT INTO order_case1 (order_id, order_date, total_amount)
SELECT 
    generate_series(1, 1000) as order_id,
    '2020-01-01'::date + (random() * 1825)::int as order_date,
    (random() * 5000 + 100)::decimal as total_amount;

-- Generate order details (multiple line items per order)
INSERT INTO order_detail_case1 (order_id, line_item_id, product_id, quantity)
SELECT DISTINCT ON (order_id, line_item_id)
    (random() * 1000 + 1)::int as order_id,
    (random() * 5 + 1)::int as line_item_id,
    (random() * 100 + 1)::int as product_id,
    (random() * 10 + 1)::int as quantity
FROM generate_series(1, 2000)
ORDER BY order_id, line_item_id, random()
LIMIT 1000;

DROP TABLE IF EXISTS result_ordered_grains_case1 CASCADE;
CREATE TABLE result_ordered_grains_case1 (
    order_id INTEGER,
    line_item_id INTEGER,
    product_id INTEGER,
    quantity INTEGER,
    order_date DATE,
    total_amount DECIMAL(10,2),
    PRIMARY KEY (order_id, line_item_id)  -- Expected grain: OrderId × LineItemId
);

INSERT INTO result_ordered_grains_case1 
SELECT DISTINCT
    od.order_id,
    od.line_item_id,
    od.product_id,
    od.quantity,
    o.order_date,
    o.total_amount
FROM order_detail_case1 od
INNER JOIN order_case1 o ON od.order_id = o.order_id;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_ordered_grains_case1;
    SELECT COUNT(DISTINCT (order_id, line_item_id)) INTO unique_rows FROM result_ordered_grains_case1;
    RAISE NOTICE 'Ordered Grains Case 1: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- ============================================================================
-- CASE 2: Jk ⊂ G[R2]
-- ============================================================================
-- OrderLineItem (G = OrderId × LineItemId × ProductId) and OrderDetail (G = OrderId × LineItemId)
-- Join: ON OrderId
-- Expected Grain: LineItemId × ProductId × LineItemId × OrderId
-- Note: LineItemId appears twice (from both sides)

DROP TABLE IF EXISTS order_line_item_case2 CASCADE;
CREATE TABLE order_line_item_case2 (
    order_id INTEGER,
    line_item_id INTEGER,
    product_id INTEGER,
    quantity INTEGER,
    unit_price DECIMAL(10,2),
    PRIMARY KEY (order_id, line_item_id, product_id)  -- Grain: OrderId × LineItemId × ProductId
);

DROP TABLE IF EXISTS order_detail_case2 CASCADE;
CREATE TABLE order_detail_case2 (
    order_id INTEGER,
    line_item_id INTEGER,
    discount DECIMAL(5,2),
    PRIMARY KEY (order_id, line_item_id)  -- Grain: OrderId × LineItemId
);

-- Generate 1000+ rows for order_line_item
INSERT INTO order_line_item_case2 (order_id, line_item_id, product_id, quantity, unit_price)
SELECT DISTINCT ON (order_id, line_item_id, product_id)
    (random() * 500 + 1)::int as order_id,
    (random() * 10 + 1)::int as line_item_id,
    (random() * 100 + 1)::int as product_id,
    (random() * 10 + 1)::int as quantity,
    (random() * 100 + 10)::decimal as unit_price
FROM generate_series(1, 2000)
ORDER BY order_id, line_item_id, product_id, random()
LIMIT 1000;

-- Generate order details
INSERT INTO order_detail_case2 (order_id, line_item_id, discount)
SELECT DISTINCT ON (order_id, line_item_id)
    (random() * 500 + 1)::int as order_id,
    (random() * 10 + 1)::int as line_item_id,
    (random() * 20)::decimal as discount
FROM generate_series(1, 1500)
ORDER BY order_id, line_item_id, random()
LIMIT 1000;

DROP TABLE IF EXISTS result_ordered_grains_case2 CASCADE;
CREATE TABLE result_ordered_grains_case2 (
    line_item_id_r1 INTEGER,
    product_id INTEGER,
    line_item_id_r2 INTEGER,
    order_id INTEGER,
    quantity INTEGER,
    unit_price DECIMAL(10,2),
    discount DECIMAL(5,2),
    PRIMARY KEY (line_item_id_r1, product_id, line_item_id_r2, order_id)  -- Expected grain
);

INSERT INTO result_ordered_grains_case2 
SELECT DISTINCT
    oli.line_item_id as line_item_id_r1,
    oli.product_id,
    od.line_item_id as line_item_id_r2,
    oli.order_id,
    oli.quantity,
    oli.unit_price,
    od.discount
FROM order_line_item_case2 oli
INNER JOIN order_detail_case2 od ON oli.order_id = od.order_id;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_ordered_grains_case2;
    SELECT COUNT(DISTINCT (line_item_id_r1, product_id, line_item_id_r2, order_id)) INTO unique_rows FROM result_ordered_grains_case2;
    RAISE NOTICE 'Ordered Grains Case 2: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- ============================================================================
-- CASE 3: Partial overlap
-- ============================================================================
-- OrderDetail (G = OrderId × LineItemId) and Order (G = OrderId × OrderDate)
-- Join: ON OrderId × CustomerId (where CustomerId is non-grain)
-- Expected Grain: LineItemId × OrderDate × OrderId

DROP TABLE IF EXISTS order_detail_case3 CASCADE;
CREATE TABLE order_detail_case3 (
    order_id INTEGER,
    line_item_id INTEGER,
    customer_id INTEGER,
    product_id INTEGER,
    quantity INTEGER,
    PRIMARY KEY (order_id, line_item_id)  -- Grain: OrderId × LineItemId
);

DROP TABLE IF EXISTS order_with_date_case3 CASCADE;
CREATE TABLE order_with_date_case3 (
    order_id INTEGER,
    order_date DATE,
    customer_id INTEGER,
    total_amount DECIMAL(10,2),
    PRIMARY KEY (order_id, order_date)  -- Grain: OrderId × OrderDate
);

-- Generate 1000+ rows
INSERT INTO order_detail_case3 (order_id, line_item_id, customer_id, product_id, quantity)
SELECT DISTINCT ON (order_id, line_item_id)
    (random() * 600 + 1)::int as order_id,
    (random() * 5 + 1)::int as line_item_id,
    (random() * 200 + 1)::int as customer_id,
    (random() * 100 + 1)::int as product_id,
    (random() * 10 + 1)::int as quantity
FROM generate_series(1, 2000)
ORDER BY order_id, line_item_id, random()
LIMIT 1000;

INSERT INTO order_with_date_case3 (order_id, order_date, customer_id, total_amount)
SELECT DISTINCT ON (order_id, order_date)
    (random() * 600 + 1)::int as order_id,
    '2020-01-01'::date + (random() * 1825)::int as order_date,
    (random() * 200 + 1)::int as customer_id,
    (random() * 5000 + 100)::decimal as total_amount
FROM generate_series(1, 1500)
ORDER BY order_id, order_date, random()
LIMIT 1000;

DROP TABLE IF EXISTS result_ordered_grains_case3 CASCADE;
CREATE TABLE result_ordered_grains_case3 (
    line_item_id INTEGER,
    order_date DATE,
    order_id INTEGER,
    customer_id INTEGER,
    product_id INTEGER,
    quantity INTEGER,
    total_amount DECIMAL(10,2),
    PRIMARY KEY (line_item_id, order_date, order_id)  -- Expected grain: LineItemId × OrderDate × OrderId
);

INSERT INTO result_ordered_grains_case3 
SELECT DISTINCT
    od.line_item_id,
    ow.order_date,
    od.order_id,
    od.customer_id,
    od.product_id,
    od.quantity,
    ow.total_amount
FROM order_detail_case3 od
INNER JOIN order_with_date_case3 ow ON od.order_id = ow.order_id 
    AND od.customer_id = ow.customer_id;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_ordered_grains_case3;
    SELECT COUNT(DISTINCT (line_item_id, order_date, order_id)) INTO unique_rows FROM result_ordered_grains_case3;
    RAISE NOTICE 'Ordered Grains Case 3: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- ============================================================================
-- CASE 4: Jk ∩ G[R2] = ∅
-- ============================================================================
-- OrderDetail (G = OrderId × LineItemId) and Order (G = OrderId)
-- Join: ON CustomerId (non-grain)
-- Expected Grain: OrderId × LineItemId × OrderId

DROP TABLE IF EXISTS order_detail_case4 CASCADE;
CREATE TABLE order_detail_case4 (
    order_id INTEGER,
    line_item_id INTEGER,
    customer_id INTEGER,
    product_id INTEGER,
    PRIMARY KEY (order_id, line_item_id)  -- Grain: OrderId × LineItemId
);

DROP TABLE IF EXISTS order_customer_case4 CASCADE;
CREATE TABLE order_customer_case4 (
    order_id INTEGER PRIMARY KEY,  -- Grain: OrderId
    customer_id INTEGER,
    order_date DATE
);

-- Generate 1000+ rows
INSERT INTO order_detail_case4 (order_id, line_item_id, customer_id, product_id)
SELECT DISTINCT ON (order_id, line_item_id)
    (random() * 800 + 1)::int as order_id,
    (random() * 5 + 1)::int as line_item_id,
    (random() * 300 + 1)::int as customer_id,
    (random() * 100 + 1)::int as product_id
FROM generate_series(1, 2000)
ORDER BY order_id, line_item_id, random()
LIMIT 1000;

INSERT INTO order_customer_case4 (order_id, customer_id, order_date)
SELECT 
    generate_series(1, 1000) as order_id,
    (random() * 300 + 1)::int as customer_id,
    '2020-01-01'::date + (random() * 1825)::int as order_date;

DROP TABLE IF EXISTS result_ordered_grains_case4 CASCADE;
CREATE TABLE result_ordered_grains_case4 (
    order_id_r1 INTEGER,
    line_item_id INTEGER,
    order_id_r2 INTEGER,
    customer_id INTEGER,
    product_id INTEGER,
    order_date DATE,
    PRIMARY KEY (order_id_r1, line_item_id, order_id_r2)  -- Expected grain: OrderId × LineItemId × OrderId
);

INSERT INTO result_ordered_grains_case4 
SELECT DISTINCT
    od.order_id as order_id_r1,
    od.line_item_id,
    oc.order_id as order_id_r2,
    od.customer_id,
    od.product_id,
    oc.order_date
FROM order_detail_case4 od
INNER JOIN order_customer_case4 oc ON od.customer_id = oc.customer_id;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM result_ordered_grains_case4;
    SELECT COUNT(DISTINCT (order_id_r1, line_item_id, order_id_r2)) INTO unique_rows FROM result_ordered_grains_case4;
    RAISE NOTICE 'Ordered Grains Case 4: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

DO $$
BEGIN
    RAISE NOTICE '========================================';
    RAISE NOTICE 'Ordered Grains Examples Completed';
    RAISE NOTICE '========================================';
END $$;







