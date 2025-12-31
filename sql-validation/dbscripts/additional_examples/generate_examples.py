#!/usr/bin/env python3
"""
Generate 85 additional examples covering all equi-join cases
Organized by category with systematic variations
"""

import os

def generate_main_theorem_examples():
    """Generate 15 additional main theorem examples (4-18)"""
    examples = []
    
    # Case A variations
    for i in range(4, 10):
        examples.append(f"""
-- Example {i}: Case A variation
DROP TABLE IF EXISTS r1_ex{i} CASCADE;
CREATE TABLE r1_ex{i} (
    a INTEGER, b INTEGER, c INTEGER, d INTEGER,
    PRIMARY KEY (a, b)  -- Grain: A × B
);

DROP TABLE IF EXISTS r2_ex{i} CASCADE;
CREATE TABLE r2_ex{i} (
    a INTEGER, b INTEGER, e INTEGER,
    PRIMARY KEY (a, b, e)  -- Grain: A × B × E
);

INSERT INTO r1_ex{i} (a, b, c, d) SELECT 
    ((row_number() OVER () - 1) / 20 + 1)::int,
    ((row_number() OVER () - 1) % 20 + 1)::int,
    (random() * 100)::int,
    (random() * 100)::int
FROM generate_series(1, 1000);

INSERT INTO r2_ex{i} (a, b, e) SELECT 
    ((row_number() OVER () - 1) / 20 + 1)::int,
    ((row_number() OVER () - 1) % 20 + 1)::int,
    ((row_number() OVER () - 1) % 10 + 1)::int
FROM generate_series(1, 1000);

DROP TABLE IF EXISTS result_ex{i} CASCADE;
CREATE TABLE result_ex{i} (
    a INTEGER, b INTEGER, c INTEGER, d INTEGER, e INTEGER,
    PRIMARY KEY (a, b, e)  -- Expected: A × B × E (Case A)
);

INSERT INTO result_ex{i} SELECT DISTINCT r1.a, r1.b, r1.c, r1.d, r2.e
FROM r1_ex{i} r1 INNER JOIN r2_ex{i} r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*), COUNT(DISTINCT (a, b, e)) INTO total_rows, unique_rows FROM result_ex{i};
    RAISE NOTICE 'Example {i}: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;
""")
    
    # Case B variations
    for i in range(10, 18):
        examples.append(f"""
-- Example {i}: Case B variation
DROP TABLE IF EXISTS r1_ex{i} CASCADE;
CREATE TABLE r1_ex{i} (
    a INTEGER, b INTEGER, c INTEGER, d INTEGER,
    PRIMARY KEY (a, c)  -- Grain: A × C
);

DROP TABLE IF EXISTS r2_ex{i} CASCADE;
CREATE TABLE r2_ex{i} (
    a INTEGER, b INTEGER, c INTEGER, e INTEGER,
    PRIMARY KEY (b, c)  -- Grain: B × C
);

INSERT INTO r1_ex{i} (a, b, c, d) SELECT 
    ((row_number() OVER () - 1) / 10 + 1)::int,
    (random() * 50 + 1)::int,
    ((row_number() OVER () - 1) % 10 + 1)::int,
    (random() * 100)::int
FROM generate_series(1, 1000);

INSERT INTO r2_ex{i} (a, b, c, e) SELECT 
    (random() * 100 + 1)::int,
    ((row_number() OVER () - 1) / 10 + 1)::int,
    ((row_number() OVER () - 1) % 10 + 1)::int,
    (random() * 100)::int
FROM generate_series(1, 1000);

DROP TABLE IF EXISTS result_ex{i} CASCADE;
CREATE TABLE result_ex{i} (
    a INTEGER, b INTEGER, c INTEGER, d INTEGER, e INTEGER,
    PRIMARY KEY (a, b, c)  -- Expected: A × B × C (Case B)
);

INSERT INTO result_ex{i} SELECT DISTINCT r1.a, r1.b, r1.c, r1.d, r2.e
FROM r1_ex{i} r1 INNER JOIN r2_ex{i} r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*), COUNT(DISTINCT (a, b, c)) INTO total_rows, unique_rows FROM result_ex{i};
    RAISE NOTICE 'Example {i}: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;
""")
    
    return examples

# This approach is getting too complex. Let me create SQL files directly with systematic examples.







