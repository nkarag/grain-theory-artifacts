-- Additional Main Theorem Examples (Examples 4-20)
-- Covering various combinations of grain sizes, join key relationships, and overlap patterns

SET search_path TO experiments, public;

-- Example 4: Case A - R1 grain larger than R2 grain, Jk subset of both
DROP TABLE IF EXISTS r1_ex4 CASCADE;
CREATE TABLE r1_ex4 (
    a INTEGER, b INTEGER, c INTEGER, d INTEGER,
    PRIMARY KEY (a, b, c)  -- Grain: A × B × C
);

DROP TABLE IF EXISTS r2_ex4 CASCADE;
CREATE TABLE r2_ex4 (
    a INTEGER, b INTEGER, e INTEGER,
    PRIMARY KEY (a, b)  -- Grain: A × B
);

INSERT INTO r1_ex4 (a, b, c, d) SELECT 
    ((row_number() OVER () - 1) / 20 + 1)::int,
    ((row_number() OVER () - 1) % 20 + 1)::int,
    ((row_number() OVER () - 1) % 5 + 1)::int,
    (random() * 100)::int
FROM generate_series(1, 1000);

INSERT INTO r2_ex4 (a, b, e) SELECT 
    ((row_number() OVER () - 1) / 20 + 1)::int,
    ((row_number() OVER () - 1) % 20 + 1)::int,
    (random() * 100)::int
FROM generate_series(1, 1000);

DROP TABLE IF EXISTS result_ex4 CASCADE;
CREATE TABLE result_ex4 (
    a INTEGER, b INTEGER, c INTEGER, d INTEGER, e INTEGER,
    PRIMARY KEY (a, b, c)  -- Expected: A × B × C (Case A, Jk = A × B)
);

INSERT INTO result_ex4 SELECT DISTINCT r1.a, r1.b, r1.c, r1.d, r2.e
FROM r1_ex4 r1 INNER JOIN r2_ex4 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*), COUNT(DISTINCT (a, b, c)) INTO total_rows, unique_rows FROM result_ex4;
    RAISE NOTICE 'Example 4: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- Example 5: Case B - Incomparable grains with larger join key
DROP TABLE IF EXISTS r1_ex5 CASCADE;
CREATE TABLE r1_ex5 (
    a INTEGER, b INTEGER, c INTEGER, d INTEGER,
    PRIMARY KEY (a, c)  -- Grain: A × C
);

DROP TABLE IF EXISTS r2_ex5 CASCADE;
CREATE TABLE r2_ex5 (
    a INTEGER, b INTEGER, c INTEGER, e INTEGER,
    PRIMARY KEY (b, c)  -- Grain: B × C
);

INSERT INTO r1_ex5 (a, b, c, d) SELECT 
    ((row_number() OVER () - 1) / 10 + 1)::int,
    (random() * 50 + 1)::int,
    ((row_number() OVER () - 1) % 10 + 1)::int,
    (random() * 100)::int
FROM generate_series(1, 1000);

INSERT INTO r2_ex5 (a, b, c, e) SELECT 
    (random() * 100 + 1)::int,
    ((row_number() OVER () - 1) / 10 + 1)::int,
    ((row_number() OVER () - 1) % 10 + 1)::int,
    (random() * 100)::int
FROM generate_series(1, 1000);

DROP TABLE IF EXISTS result_ex5 CASCADE;
CREATE TABLE result_ex5 (
    a INTEGER, b INTEGER, c INTEGER, d INTEGER, e INTEGER,
    PRIMARY KEY (a, b, c)  -- Expected: A × B × C (Case B, Jk = A × B × C)
);

INSERT INTO result_ex5 SELECT DISTINCT r1.a, r1.b, r1.c, r1.d, r2.e
FROM r1_ex5 r1 INNER JOIN r2_ex5 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    SELECT COUNT(*), COUNT(DISTINCT (a, b, c)) INTO total_rows, unique_rows FROM result_ex5;
    RAISE NOTICE 'Example 5: Total=% Unique=% Match=%', total_rows, unique_rows, (total_rows = unique_rows);
END $$;

-- Continue with more examples... (I'll create multiple files to cover all 85)







