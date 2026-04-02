-- ==========================================================================
-- Grain Formula Revalidation: Paper vs Corrected Formula (100 Examples)
-- ==========================================================================
--
-- Tests Theorem 6.1 from the PODS 2027 paper against the corrected formula.
-- For each example:
--   1. Paper grain tested for uniqueness and minimality
--   2. Corrected grain tested for uniqueness and minimality
--
-- Expected: paper formula fails minimality on Case B examples (27/100);
--           corrected formula passes both uniqueness and minimality on all 100.
-- ==========================================================================

CREATE SCHEMA IF NOT EXISTS revalidation;
SET search_path TO revalidation, public;
SELECT setseed(0.42);  -- reproducible random values

DROP TABLE IF EXISTS revalidation.test_results CASCADE;
CREATE TABLE revalidation.test_results (
    example_id      INTEGER,
    category        TEXT,
    case_type       CHAR(1),
    description     TEXT,
    result_rows     BIGINT,
    paper_grain     TEXT,
    paper_unique    BOOLEAN,
    paper_minimal   BOOLEAN,
    paper_removable TEXT,
    corrected_grain TEXT,
    corrected_unique  BOOLEAN,
    corrected_minimal BOOLEAN,
    corrected_removable TEXT DEFAULT '-'
);

\echo '========================================================'
\echo 'Grain Formula Revalidation — 100 Examples'
\echo '========================================================'
\echo ''

\echo '── Main Theorem (22 examples) ──'
-- Example 1: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v1]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex1 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex1 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex1 CASCADE;
CREATE TABLE revalidation.r1_ex1 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex1 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex1 (a, b, c, e)
SELECT ((i / 20) % 50 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 20 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex1 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex1 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex1 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex1
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex1 r1
INNER JOIN revalidation.r2_ex1 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex1;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            1, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v1]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 1: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex1;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex1', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex1;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex1', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        1, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v1]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        1, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        1, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v1]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 1, SQLERRM;
END $$;

-- Example 2: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v2]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex2 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex2 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex2 CASCADE;
CREATE TABLE revalidation.r1_ex2 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex2 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex2 (a, b, c, e)
SELECT ((i / 25) % 40 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 25 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex2 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex2 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex2 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex2
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex2 r1
INNER JOIN revalidation.r2_ex2 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex2;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            2, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v2]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 2: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex2;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex2', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex2;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex2', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        2, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v2]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        2, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        2, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v2]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 2, SQLERRM;
END $$;

-- Example 3: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v3]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex3 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex3 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex3 CASCADE;
CREATE TABLE revalidation.r1_ex3 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex3 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex3 (a, b, c, e)
SELECT ((i / 10) % 100 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex3 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex3 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex3 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex3
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex3 r1
INNER JOIN revalidation.r2_ex3 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex3;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            3, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v3]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 3: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex3;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex3', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex3;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex3', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        3, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v3]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        3, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        3, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v3]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 3, SQLERRM;
END $$;

-- Example 4: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v4]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex4 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex4 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex4 CASCADE;
CREATE TABLE revalidation.r1_ex4 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex4 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex4 (a, b, c, e)
SELECT ((i / 40) % 25 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 40 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex4 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex4 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex4 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex4
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex4 r1
INNER JOIN revalidation.r2_ex4 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex4;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            4, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v4]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 4: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex4;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex4', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex4;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex4', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        4, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v4]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        4, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        4, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v4]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 4, SQLERRM;
END $$;

-- Example 5: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v5]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex5 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex5 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex5 CASCADE;
CREATE TABLE revalidation.r1_ex5 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex5 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex5 (a, b, c, e)
SELECT ((i / 50) % 20 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 50 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex5 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex5 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex5 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex5
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex5 r1
INNER JOIN revalidation.r2_ex5 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex5;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            5, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v5]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 5: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex5;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex5', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex5;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex5', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        5, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v5]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        5, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        5, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v5]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 5, SQLERRM;
END $$;

-- Example 6: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v6]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex6 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex6 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex6 CASCADE;
CREATE TABLE revalidation.r1_ex6 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex6 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex6 (a, b, c, e)
SELECT ((i / 100) % 10 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 100 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex6 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex6 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex6 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex6
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex6 r1
INNER JOIN revalidation.r2_ex6 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex6;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            6, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v6]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 6: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex6;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex6', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex6;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex6', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        6, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v6]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        6, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        6, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v6]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 6, SQLERRM;
END $$;

-- Example 7: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v7]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex7 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex7 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex7 CASCADE;
CREATE TABLE revalidation.r1_ex7 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex7 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex7 (a, b, c, e)
SELECT ((i / 30) % 30 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 30 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex7 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex7 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex7 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex7
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex7 r1
INNER JOIN revalidation.r2_ex7 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex7;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            7, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v7]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 7: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex7;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex7', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex7;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex7', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        7, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v7]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        7, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        7, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v7]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 7, SQLERRM;
END $$;

-- Example 8: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v8]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex8 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex8 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex8 CASCADE;
CREATE TABLE revalidation.r1_ex8 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex8 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex8 (a, b, c, e)
SELECT ((i / 5) % 200 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex8 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex8 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex8 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex8
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex8 r1
INNER JOIN revalidation.r2_ex8 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex8;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            8, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v8]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 8: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex8;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex8', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex8;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex8', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        8, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v8]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        8, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        8, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v8]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 8, SQLERRM;
END $$;

-- Example 9: Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v9]
-- Category: Main Theorem, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex9 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex9 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex9 CASCADE;
CREATE TABLE revalidation.r1_ex9 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex9 (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex9 (a, b, c, e)
SELECT ((i / 200) % 5 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 200 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex9 (a, b, c, d)
SELECT r1.a, r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex9 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex9 (a INTEGER, b INTEGER, c INTEGER, e INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex9
SELECT DISTINCT r1.a, r1.b, r1.c, r1.e, r2.d
FROM revalidation.r1_ex9 r1
INNER JOIN revalidation.r2_ex9 r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex9;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            9, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v9]',
            0, 'a, b, c', FALSE, FALSE, 'NO DATA',
            'a, c', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 9: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c)) INTO unique_count FROM revalidation.result_ex9;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex9', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c)) INTO unique_count FROM revalidation.result_ex9;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex9', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        9, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v9]',
        total_rows, 'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        9, total_rows,
        'a, b, c', p_unique, p_minimal, p_removable,
        'a, c', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        9, 'Main Theorem', 'B', 'Case B — Jk={a,b,c}, G1={a,c}, G2={a,b} [v9]',
        -1, 'a, b, c', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 9, SQLERRM;
END $$;

-- Example 28: Case A — Jk={a,b}, G1={a}, G2={a,b} [v1]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex28 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex28 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex28 CASCADE;
CREATE TABLE revalidation.r1_ex28 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex28 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex28 (a, b, v1)
SELECT ((i / 1) % 1000 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex28 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex28 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex28 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex28
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex28 r1
INNER JOIN revalidation.r2_ex28 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex28;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            28, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v1]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 28: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex28;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex28', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex28;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex28', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        28, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v1]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        28, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        28, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v1]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 28, SQLERRM;
END $$;

-- Example 29: Case A — Jk={a,b}, G1={a}, G2={a,b} [v2]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex29 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex29 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex29 CASCADE;
CREATE TABLE revalidation.r1_ex29 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex29 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex29 (a, b, v1)
SELECT ((i / 1) % 500 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex29 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex29 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex29 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex29
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex29 r1
INNER JOIN revalidation.r2_ex29 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex29;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            29, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v2]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 29: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex29;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex29', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex29;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex29', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        29, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v2]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        29, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        29, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v2]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 29, SQLERRM;
END $$;

-- Example 30: Case A — Jk={a,b}, G1={a}, G2={a,b} [v3]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex30 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex30 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex30 CASCADE;
CREATE TABLE revalidation.r1_ex30 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex30 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex30 (a, b, v1)
SELECT ((i / 1) % 200 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex30 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex30 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex30 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex30
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex30 r1
INNER JOIN revalidation.r2_ex30 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex30;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            30, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v3]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 30: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex30;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex30', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex30;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex30', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        30, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v3]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        30, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        30, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v3]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 30, SQLERRM;
END $$;

-- Example 31: Case A — Jk={a,b}, G1={a}, G2={a,b} [v4]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex31 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex31 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex31 CASCADE;
CREATE TABLE revalidation.r1_ex31 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex31 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex31 (a, b, v1)
SELECT ((i / 1) % 100 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex31 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex31 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex31 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex31
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex31 r1
INNER JOIN revalidation.r2_ex31 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex31;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            31, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v4]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 31: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex31;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex31', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex31;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex31', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        31, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v4]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        31, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        31, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v4]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 31, SQLERRM;
END $$;

-- Example 32: Case A — Jk={a,b}, G1={a}, G2={a,b} [v5]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex32 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex32 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex32 CASCADE;
CREATE TABLE revalidation.r1_ex32 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex32 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex32 (a, b, v1)
SELECT ((i / 1) % 50 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex32 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex32 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex32 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex32
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex32 r1
INNER JOIN revalidation.r2_ex32 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex32;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            32, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v5]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 32: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex32;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex32', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex32;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex32', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        32, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v5]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        32, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        32, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v5]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 32, SQLERRM;
END $$;

-- Example 33: Case A — Jk={a,b}, G1={a}, G2={a,b} [v6]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex33 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex33 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex33 CASCADE;
CREATE TABLE revalidation.r1_ex33 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex33 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex33 (a, b, v1)
SELECT ((i / 1) % 1000 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex33 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex33 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex33 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex33
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex33 r1
INNER JOIN revalidation.r2_ex33 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex33;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            33, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v6]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 33: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex33;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex33', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex33;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex33', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        33, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v6]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        33, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        33, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v6]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 33, SQLERRM;
END $$;

-- Example 34: Case A — Jk={a,b}, G1={a}, G2={a,b} [v7]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex34 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex34 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex34 CASCADE;
CREATE TABLE revalidation.r1_ex34 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex34 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex34 (a, b, v1)
SELECT ((i / 1) % 500 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex34 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex34 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex34 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex34
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex34 r1
INNER JOIN revalidation.r2_ex34 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex34;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            34, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v7]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 34: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex34;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex34', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex34;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex34', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        34, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v7]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        34, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        34, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v7]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 34, SQLERRM;
END $$;

-- Example 35: Case A — Jk={a,b}, G1={a}, G2={a,b} [v8]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex35 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex35 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex35 CASCADE;
CREATE TABLE revalidation.r1_ex35 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex35 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex35 (a, b, v1)
SELECT ((i / 1) % 200 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex35 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex35 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex35 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex35
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex35 r1
INNER JOIN revalidation.r2_ex35 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex35;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            35, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v8]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 35: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex35;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex35', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex35;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex35', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        35, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v8]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        35, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        35, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v8]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 35, SQLERRM;
END $$;

-- Example 36: Case A — Jk={a,b}, G1={a}, G2={a,b} [v9]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex36 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex36 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex36 CASCADE;
CREATE TABLE revalidation.r1_ex36 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex36 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex36 (a, b, v1)
SELECT ((i / 1) % 100 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex36 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex36 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex36 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex36
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex36 r1
INNER JOIN revalidation.r2_ex36 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex36;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            36, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v9]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 36: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex36;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex36', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex36;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex36', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        36, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v9]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        36, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        36, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v9]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 36, SQLERRM;
END $$;

-- Example 37: Case A — Jk={a,b}, G1={a}, G2={a,b} [v10]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex37 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex37 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex37 CASCADE;
CREATE TABLE revalidation.r1_ex37 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex37 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex37 (a, b, v1)
SELECT ((i / 1) % 50 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex37 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex37 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex37 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex37
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex37 r1
INNER JOIN revalidation.r2_ex37 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex37;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            37, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v10]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 37: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex37;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex37', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex37;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex37', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        37, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v10]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        37, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        37, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v10]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 37, SQLERRM;
END $$;

-- Example 38: Case A — Jk={a,b}, G1={a}, G2={a,b} [v11]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex38 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex38 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex38 CASCADE;
CREATE TABLE revalidation.r1_ex38 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex38 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex38 (a, b, v1)
SELECT ((i / 1) % 1000 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex38 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex38 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex38 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex38
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex38 r1
INNER JOIN revalidation.r2_ex38 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex38;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            38, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v11]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 38: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex38;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex38', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex38;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex38', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        38, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v11]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        38, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        38, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v11]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 38, SQLERRM;
END $$;

-- Example 39: Case A — Jk={a,b}, G1={a}, G2={a,b} [v12]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex39 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex39 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex39 CASCADE;
CREATE TABLE revalidation.r1_ex39 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex39 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex39 (a, b, v1)
SELECT ((i / 1) % 500 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex39 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex39 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex39 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex39
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex39 r1
INNER JOIN revalidation.r2_ex39 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex39;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            39, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v12]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 39: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex39;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex39', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex39;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex39', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        39, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v12]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        39, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        39, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v12]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 39, SQLERRM;
END $$;

-- Example 40: Case A — Jk={a,b}, G1={a}, G2={a,b} [v13]
-- Category: Main Theorem, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex40 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex40 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex40 CASCADE;
CREATE TABLE revalidation.r1_ex40 (a INTEGER, b INTEGER, v1 INTEGER, PRIMARY KEY (a));
CREATE TABLE revalidation.r2_ex40 (a INTEGER, b INTEGER, v2 INTEGER, PRIMARY KEY (a, b));
INSERT INTO revalidation.r1_ex40 (a, b, v1)
SELECT ((i / 1) % 200 + 1)::int, ((i * 10) % 47 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a) DO NOTHING;
INSERT INTO revalidation.r2_ex40 (a, b, v2)
SELECT r1.a, r1.b, (random() * 100 + 1)::int
FROM revalidation.r1_ex40 r1
ORDER BY random()
ON CONFLICT (a, b) DO NOTHING;
CREATE TABLE revalidation.result_ex40 (a INTEGER, b INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex40
SELECT DISTINCT r1.a, r1.b, r1.v1, r2.v2
FROM revalidation.r1_ex40 r1
INNER JOIN revalidation.r2_ex40 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex40;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            40, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v13]',
            0, 'a', FALSE, FALSE, 'NO DATA',
            'a', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 40: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex40;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex40', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a)) INTO unique_count FROM revalidation.result_ex40;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex40', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        40, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v13]',
        total_rows, 'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        40, total_rows,
        'a', p_unique, p_minimal, p_removable,
        'a', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        40, 'Main Theorem', 'A', 'Case A — Jk={a,b}, G1={a}, G2={a,b} [v13]',
        -1, 'a', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 40, SQLERRM;
END $$;


\echo '── Incomparable Grains (16 examples) ──'
-- Example 10: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v1]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex10 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex10 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex10 CASCADE;
CREATE TABLE revalidation.r1_ex10 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex10 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex10 (a, b, c, v1)
SELECT ((i / 20) % 50 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 20 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex10 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex10 r1
    CROSS JOIN generate_series(1, 20) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex10 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex10
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex10 r1
INNER JOIN revalidation.r2_ex10 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex10;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            10, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v1]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 10: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex10;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex10', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex10;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex10', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        10, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v1]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        10, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        10, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v1]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 10, SQLERRM;
END $$;

-- Example 11: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v2]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex11 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex11 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex11 CASCADE;
CREATE TABLE revalidation.r1_ex11 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex11 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex11 (a, b, c, v1)
SELECT ((i / 25) % 40 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 25 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex11 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex11 r1
    CROSS JOIN generate_series(1, 25) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex11 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex11
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex11 r1
INNER JOIN revalidation.r2_ex11 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex11;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            11, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v2]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 11: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex11;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex11', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex11;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex11', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        11, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v2]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        11, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        11, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v2]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 11, SQLERRM;
END $$;

-- Example 12: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v3]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex12 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex12 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex12 CASCADE;
CREATE TABLE revalidation.r1_ex12 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex12 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex12 (a, b, c, v1)
SELECT ((i / 10) % 100 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex12 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex12 r1
    CROSS JOIN generate_series(1, 10) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex12 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex12
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex12 r1
INNER JOIN revalidation.r2_ex12 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex12;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            12, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v3]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 12: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex12;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex12', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex12;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex12', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        12, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v3]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        12, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        12, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v3]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 12, SQLERRM;
END $$;

-- Example 13: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v4]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex13 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex13 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex13 CASCADE;
CREATE TABLE revalidation.r1_ex13 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex13 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex13 (a, b, c, v1)
SELECT ((i / 40) % 25 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 40 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex13 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex13 r1
    CROSS JOIN generate_series(1, 40) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex13 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex13
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex13 r1
INNER JOIN revalidation.r2_ex13 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex13;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            13, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v4]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 13: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex13;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex13', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex13;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex13', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        13, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v4]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        13, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        13, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v4]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 13, SQLERRM;
END $$;

-- Example 14: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v5]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex14 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex14 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex14 CASCADE;
CREATE TABLE revalidation.r1_ex14 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex14 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex14 (a, b, c, v1)
SELECT ((i / 50) % 20 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 50 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex14 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex14 r1
    CROSS JOIN generate_series(1, 50) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex14 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex14
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex14 r1
INNER JOIN revalidation.r2_ex14 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex14;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            14, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v5]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 14: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex14;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex14', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex14;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex14', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        14, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v5]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        14, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        14, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v5]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 14, SQLERRM;
END $$;

-- Example 15: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v6]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex15 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex15 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex15 CASCADE;
CREATE TABLE revalidation.r1_ex15 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex15 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex15 (a, b, c, v1)
SELECT ((i / 100) % 10 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 100 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex15 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex15 r1
    CROSS JOIN generate_series(1, 100) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex15 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex15
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex15 r1
INNER JOIN revalidation.r2_ex15 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex15;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            15, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v6]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 15: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex15;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex15', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex15;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex15', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        15, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v6]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        15, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        15, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v6]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 15, SQLERRM;
END $$;

-- Example 16: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v7]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex16 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex16 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex16 CASCADE;
CREATE TABLE revalidation.r1_ex16 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex16 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex16 (a, b, c, v1)
SELECT ((i / 30) % 30 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 30 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex16 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex16 r1
    CROSS JOIN generate_series(1, 30) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex16 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex16
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex16 r1
INNER JOIN revalidation.r2_ex16 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex16;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            16, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v7]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 16: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex16;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex16', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex16;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex16', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        16, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v7]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        16, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        16, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v7]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 16, SQLERRM;
END $$;

-- Example 17: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v8]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex17 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex17 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex17 CASCADE;
CREATE TABLE revalidation.r1_ex17 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex17 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex17 (a, b, c, v1)
SELECT ((i / 5) % 200 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex17 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex17 r1
    CROSS JOIN generate_series(1, 5) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex17 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex17
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex17 r1
INNER JOIN revalidation.r2_ex17 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex17;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            17, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v8]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 17: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex17;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex17', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex17;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex17', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        17, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v8]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        17, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        17, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v8]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 17, SQLERRM;
END $$;

-- Example 18: Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v9]
-- Category: Incomparable Grains, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex18 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex18 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex18 CASCADE;
CREATE TABLE revalidation.r1_ex18 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, c));
CREATE TABLE revalidation.r2_ex18 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (b, d));
INSERT INTO revalidation.r1_ex18 (a, b, c, v1)
SELECT ((i / 200) % 5 + 1)::int, ((i * 10) % 47 + 1)::int, ((i / 1) % 200 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, c) DO NOTHING;
INSERT INTO revalidation.r2_ex18 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex18 r1
    CROSS JOIN generate_series(1, 200) s_d(d)
ORDER BY random()
ON CONFLICT (b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex18 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex18
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex18 r1
INNER JOIN revalidation.r2_ex18 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex18;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            18, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v9]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 18: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex18;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex18', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, c, d)) INTO unique_count FROM revalidation.result_ex18;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex18', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        18, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v9]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        18, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        18, 'Incomparable Grains', 'B', 'Case B — Jk={a,b}, G1={a,c}, G2={b,d} [v9]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 18, SQLERRM;
END $$;

-- Example 86: Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v1]
-- Category: Incomparable Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex86 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex86 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex86 CASCADE;
CREATE TABLE revalidation.r1_ex86 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, b, c));
CREATE TABLE revalidation.r2_ex86 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (a, b, d));
INSERT INTO revalidation.r1_ex86 (a, b, c, v1)
SELECT ((i / 100) % 10 + 1)::int, ((i / 10) % 10 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b, c) DO NOTHING;
INSERT INTO revalidation.r2_ex86 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex86 r1
    CROSS JOIN generate_series(1, 10) s_d(d)
ORDER BY random()
ON CONFLICT (a, b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex86 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex86
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex86 r1
INNER JOIN revalidation.r2_ex86 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex86;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            86, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v1]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 86: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex86;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex86', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex86;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex86', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        86, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v1]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        86, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        86, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v1]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 86, SQLERRM;
END $$;

-- Example 87: Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v2]
-- Category: Incomparable Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex87 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex87 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex87 CASCADE;
CREATE TABLE revalidation.r1_ex87 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, b, c));
CREATE TABLE revalidation.r2_ex87 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (a, b, d));
INSERT INTO revalidation.r1_ex87 (a, b, c, v1)
SELECT ((i / 50) % 20 + 1)::int, ((i / 5) % 10 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b, c) DO NOTHING;
INSERT INTO revalidation.r2_ex87 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex87 r1
    CROSS JOIN generate_series(1, 5) s_d(d)
ORDER BY random()
ON CONFLICT (a, b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex87 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex87
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex87 r1
INNER JOIN revalidation.r2_ex87 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex87;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            87, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v2]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 87: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex87;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex87', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex87;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex87', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        87, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v2]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        87, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        87, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v2]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 87, SQLERRM;
END $$;

-- Example 88: Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v3]
-- Category: Incomparable Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex88 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex88 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex88 CASCADE;
CREATE TABLE revalidation.r1_ex88 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, b, c));
CREATE TABLE revalidation.r2_ex88 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (a, b, d));
INSERT INTO revalidation.r1_ex88 (a, b, c, v1)
SELECT ((i / 200) % 5 + 1)::int, ((i / 20) % 10 + 1)::int, ((i / 1) % 20 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b, c) DO NOTHING;
INSERT INTO revalidation.r2_ex88 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex88 r1
    CROSS JOIN generate_series(1, 20) s_d(d)
ORDER BY random()
ON CONFLICT (a, b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex88 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex88
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex88 r1
INNER JOIN revalidation.r2_ex88 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex88;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            88, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v3]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 88: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex88;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex88', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex88;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex88', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        88, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v3]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        88, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        88, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v3]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 88, SQLERRM;
END $$;

-- Example 89: Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v4]
-- Category: Incomparable Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex89 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex89 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex89 CASCADE;
CREATE TABLE revalidation.r1_ex89 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, b, c));
CREATE TABLE revalidation.r2_ex89 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (a, b, d));
INSERT INTO revalidation.r1_ex89 (a, b, c, v1)
SELECT ((i / 100) % 10 + 1)::int, ((i / 5) % 20 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b, c) DO NOTHING;
INSERT INTO revalidation.r2_ex89 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex89 r1
    CROSS JOIN generate_series(1, 5) s_d(d)
ORDER BY random()
ON CONFLICT (a, b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex89 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex89
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex89 r1
INNER JOIN revalidation.r2_ex89 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex89;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            89, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v4]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 89: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex89;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex89', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex89;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex89', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        89, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v4]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        89, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        89, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v4]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 89, SQLERRM;
END $$;

-- Example 90: Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v5]
-- Category: Incomparable Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex90 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex90 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex90 CASCADE;
CREATE TABLE revalidation.r1_ex90 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, b, c));
CREATE TABLE revalidation.r2_ex90 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (a, b, d));
INSERT INTO revalidation.r1_ex90 (a, b, c, v1)
SELECT ((i / 200) % 5 + 1)::int, ((i / 40) % 5 + 1)::int, ((i / 1) % 40 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b, c) DO NOTHING;
INSERT INTO revalidation.r2_ex90 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex90 r1
    CROSS JOIN generate_series(1, 40) s_d(d)
ORDER BY random()
ON CONFLICT (a, b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex90 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex90
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex90 r1
INNER JOIN revalidation.r2_ex90 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex90;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            90, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v5]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 90: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex90;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex90', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex90;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex90', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        90, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v5]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        90, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        90, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v5]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 90, SQLERRM;
END $$;

-- Example 91: Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v6]
-- Category: Incomparable Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex91 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex91 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex91 CASCADE;
CREATE TABLE revalidation.r1_ex91 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, b, c));
CREATE TABLE revalidation.r2_ex91 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (a, b, d));
INSERT INTO revalidation.r1_ex91 (a, b, c, v1)
SELECT ((i / 25) % 40 + 1)::int, ((i / 5) % 5 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b, c) DO NOTHING;
INSERT INTO revalidation.r2_ex91 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex91 r1
    CROSS JOIN generate_series(1, 5) s_d(d)
ORDER BY random()
ON CONFLICT (a, b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex91 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex91
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex91 r1
INNER JOIN revalidation.r2_ex91 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex91;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            91, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v6]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 91: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex91;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex91', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex91;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex91', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        91, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v6]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        91, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        91, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v6]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 91, SQLERRM;
END $$;

-- Example 92: Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v7]
-- Category: Incomparable Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex92 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex92 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex92 CASCADE;
CREATE TABLE revalidation.r1_ex92 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, PRIMARY KEY (a, b, c));
CREATE TABLE revalidation.r2_ex92 (a INTEGER, b INTEGER, d INTEGER, v2 INTEGER, PRIMARY KEY (a, b, d));
INSERT INTO revalidation.r1_ex92 (a, b, c, v1)
SELECT ((i / 100) % 10 + 1)::int, ((i / 10) % 10 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b, c) DO NOTHING;
INSERT INTO revalidation.r2_ex92 (a, b, d, v2)
SELECT r1.a, r1.b, s_d.d, (random() * 100 + 1)::int
FROM revalidation.r1_ex92 r1
    CROSS JOIN generate_series(1, 10) s_d(d)
ORDER BY random()
ON CONFLICT (a, b, d) DO NOTHING;
CREATE TABLE revalidation.result_ex92 (a INTEGER, b INTEGER, c INTEGER, v1 INTEGER, d INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex92
SELECT DISTINCT r1.a, r1.b, r1.c, r1.v1, r2.d, r2.v2
FROM revalidation.r1_ex92 r1
INNER JOIN revalidation.r2_ex92 r2 ON r1.a = r2.a AND r1.b = r2.b;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex92;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            92, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v7]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, c, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 92: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex92;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex92', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex92;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex92', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        92, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v7]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        92, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, c, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        92, 'Incomparable Grains', 'A', 'Case A — Jk={a,b}, G1={a,b,c}, G2={a,b,d} [v7]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 92, SQLERRM;
END $$;


\echo '── Natural Join (17 examples) ──'
-- Example 19: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v1]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex19 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex19 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex19 CASCADE;
CREATE TABLE revalidation.r1_ex19 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex19 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex19 (a, b, c)
SELECT ((i / 20) % 50 + 1)::int, ((i / 1) % 20 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex19 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex19 r1
    CROSS JOIN generate_series(1, 20) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex19 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex19
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex19 r1
INNER JOIN revalidation.r2_ex19 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex19;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            19, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v1]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 19: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex19;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex19', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex19;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex19', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        19, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v1]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        19, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        19, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v1]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 19, SQLERRM;
END $$;

-- Example 20: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v2]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex20 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex20 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex20 CASCADE;
CREATE TABLE revalidation.r1_ex20 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex20 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex20 (a, b, c)
SELECT ((i / 25) % 40 + 1)::int, ((i / 1) % 25 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex20 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex20 r1
    CROSS JOIN generate_series(1, 25) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex20 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex20
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex20 r1
INNER JOIN revalidation.r2_ex20 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex20;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            20, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v2]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 20: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex20;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex20', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex20;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex20', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        20, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v2]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        20, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        20, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v2]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 20, SQLERRM;
END $$;

-- Example 21: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v3]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex21 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex21 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex21 CASCADE;
CREATE TABLE revalidation.r1_ex21 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex21 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex21 (a, b, c)
SELECT ((i / 10) % 100 + 1)::int, ((i / 1) % 10 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex21 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex21 r1
    CROSS JOIN generate_series(1, 10) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex21 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex21
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex21 r1
INNER JOIN revalidation.r2_ex21 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex21;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            21, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v3]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 21: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex21;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex21', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex21;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex21', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        21, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v3]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        21, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        21, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v3]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 21, SQLERRM;
END $$;

-- Example 22: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v4]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex22 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex22 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex22 CASCADE;
CREATE TABLE revalidation.r1_ex22 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex22 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex22 (a, b, c)
SELECT ((i / 40) % 25 + 1)::int, ((i / 1) % 40 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex22 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex22 r1
    CROSS JOIN generate_series(1, 40) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex22 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex22
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex22 r1
INNER JOIN revalidation.r2_ex22 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex22;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            22, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v4]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 22: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex22;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex22', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex22;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex22', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        22, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v4]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        22, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        22, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v4]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 22, SQLERRM;
END $$;

-- Example 23: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v5]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex23 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex23 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex23 CASCADE;
CREATE TABLE revalidation.r1_ex23 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex23 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex23 (a, b, c)
SELECT ((i / 50) % 20 + 1)::int, ((i / 1) % 50 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex23 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex23 r1
    CROSS JOIN generate_series(1, 50) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex23 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex23
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex23 r1
INNER JOIN revalidation.r2_ex23 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex23;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            23, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v5]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 23: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex23;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex23', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex23;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex23', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        23, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v5]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        23, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        23, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v5]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 23, SQLERRM;
END $$;

-- Example 24: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v6]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex24 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex24 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex24 CASCADE;
CREATE TABLE revalidation.r1_ex24 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex24 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex24 (a, b, c)
SELECT ((i / 100) % 10 + 1)::int, ((i / 1) % 100 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex24 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex24 r1
    CROSS JOIN generate_series(1, 100) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex24 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex24
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex24 r1
INNER JOIN revalidation.r2_ex24 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex24;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            24, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v6]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 24: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex24;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex24', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex24;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex24', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        24, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v6]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        24, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        24, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v6]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 24, SQLERRM;
END $$;

-- Example 25: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v7]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex25 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex25 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex25 CASCADE;
CREATE TABLE revalidation.r1_ex25 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex25 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex25 (a, b, c)
SELECT ((i / 30) % 30 + 1)::int, ((i / 1) % 30 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex25 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex25 r1
    CROSS JOIN generate_series(1, 30) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex25 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex25
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex25 r1
INNER JOIN revalidation.r2_ex25 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex25;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            25, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v7]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 25: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex25;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex25', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex25;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex25', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        25, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v7]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        25, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        25, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v7]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 25, SQLERRM;
END $$;

-- Example 26: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v8]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex26 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex26 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex26 CASCADE;
CREATE TABLE revalidation.r1_ex26 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex26 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex26 (a, b, c)
SELECT ((i / 5) % 200 + 1)::int, ((i / 1) % 5 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex26 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex26 r1
    CROSS JOIN generate_series(1, 5) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex26 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex26
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex26 r1
INNER JOIN revalidation.r2_ex26 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex26;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            26, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v8]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 26: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex26;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex26', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex26;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex26', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        26, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v8]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        26, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        26, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v8]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 26, SQLERRM;
END $$;

-- Example 27: Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v9]
-- Category: Natural Join, Case: B
DROP TABLE IF EXISTS revalidation.r1_ex27 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex27 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex27 CASCADE;
CREATE TABLE revalidation.r1_ex27 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex27 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d));
INSERT INTO revalidation.r1_ex27 (a, b, c)
SELECT ((i / 200) % 5 + 1)::int, ((i / 1) % 200 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex27 (b, c, d)
SELECT r1.b, r1.c, s_d.d
FROM revalidation.r1_ex27 r1
    CROSS JOIN generate_series(1, 200) s_d(d)
ORDER BY random()
ON CONFLICT (c, d) DO NOTHING;
CREATE TABLE revalidation.result_ex27 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex27
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex27 r1
INNER JOIN revalidation.r2_ex27 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex27;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            27, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v9]',
            0, 'a, b, c, d', FALSE, FALSE, 'NO DATA',
            'a, b, d', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 27: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, c, d)) INTO unique_count FROM revalidation.result_ex27;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'c', 'd'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex27', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b, d)) INTO unique_count FROM revalidation.result_ex27;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b', 'd'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex27', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        27, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v9]',
        total_rows, 'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        27, total_rows,
        'a, b, c, d', p_unique, p_minimal, p_removable,
        'a, b, d', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        27, 'Natural Join', 'B', 'Case B — Jk={b,c}, G1={a,b}, G2={c,d} [v9]',
        -1, 'a, b, c, d', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b, d', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 27, SQLERRM;
END $$;

-- Example 93: Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v1]
-- Category: Natural Join, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex93 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex93 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex93 CASCADE;
CREATE TABLE revalidation.r1_ex93 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex93 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c));
INSERT INTO revalidation.r1_ex93 (a, b, c)
SELECT ((i / 20) % 50 + 1)::int, ((i / 1) % 20 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex93 (b, c, d)
SELECT r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex93 r1
ORDER BY random()
ON CONFLICT (b, c) DO NOTHING;
CREATE TABLE revalidation.result_ex93 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex93
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex93 r1
INNER JOIN revalidation.r2_ex93 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex93;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            93, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v1]',
            0, 'a, b', FALSE, FALSE, 'NO DATA',
            'a, b', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 93: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex93;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex93', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex93;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex93', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        93, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v1]',
        total_rows, 'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        93, total_rows,
        'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        93, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v1]',
        -1, 'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 93, SQLERRM;
END $$;

-- Example 94: Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v2]
-- Category: Natural Join, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex94 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex94 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex94 CASCADE;
CREATE TABLE revalidation.r1_ex94 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex94 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c));
INSERT INTO revalidation.r1_ex94 (a, b, c)
SELECT ((i / 25) % 40 + 1)::int, ((i / 1) % 25 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex94 (b, c, d)
SELECT r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex94 r1
ORDER BY random()
ON CONFLICT (b, c) DO NOTHING;
CREATE TABLE revalidation.result_ex94 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex94
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex94 r1
INNER JOIN revalidation.r2_ex94 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex94;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            94, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v2]',
            0, 'a, b', FALSE, FALSE, 'NO DATA',
            'a, b', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 94: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex94;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex94', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex94;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex94', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        94, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v2]',
        total_rows, 'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        94, total_rows,
        'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        94, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v2]',
        -1, 'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 94, SQLERRM;
END $$;

-- Example 95: Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v3]
-- Category: Natural Join, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex95 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex95 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex95 CASCADE;
CREATE TABLE revalidation.r1_ex95 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex95 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c));
INSERT INTO revalidation.r1_ex95 (a, b, c)
SELECT ((i / 10) % 100 + 1)::int, ((i / 1) % 10 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex95 (b, c, d)
SELECT r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex95 r1
ORDER BY random()
ON CONFLICT (b, c) DO NOTHING;
CREATE TABLE revalidation.result_ex95 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex95
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex95 r1
INNER JOIN revalidation.r2_ex95 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex95;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            95, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v3]',
            0, 'a, b', FALSE, FALSE, 'NO DATA',
            'a, b', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 95: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex95;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex95', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex95;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex95', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        95, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v3]',
        total_rows, 'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        95, total_rows,
        'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        95, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v3]',
        -1, 'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 95, SQLERRM;
END $$;

-- Example 96: Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v4]
-- Category: Natural Join, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex96 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex96 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex96 CASCADE;
CREATE TABLE revalidation.r1_ex96 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex96 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c));
INSERT INTO revalidation.r1_ex96 (a, b, c)
SELECT ((i / 40) % 25 + 1)::int, ((i / 1) % 40 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex96 (b, c, d)
SELECT r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex96 r1
ORDER BY random()
ON CONFLICT (b, c) DO NOTHING;
CREATE TABLE revalidation.result_ex96 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex96
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex96 r1
INNER JOIN revalidation.r2_ex96 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex96;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            96, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v4]',
            0, 'a, b', FALSE, FALSE, 'NO DATA',
            'a, b', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 96: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex96;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex96', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex96;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex96', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        96, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v4]',
        total_rows, 'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        96, total_rows,
        'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        96, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v4]',
        -1, 'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 96, SQLERRM;
END $$;

-- Example 97: Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v5]
-- Category: Natural Join, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex97 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex97 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex97 CASCADE;
CREATE TABLE revalidation.r1_ex97 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex97 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c));
INSERT INTO revalidation.r1_ex97 (a, b, c)
SELECT ((i / 50) % 20 + 1)::int, ((i / 1) % 50 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex97 (b, c, d)
SELECT r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex97 r1
ORDER BY random()
ON CONFLICT (b, c) DO NOTHING;
CREATE TABLE revalidation.result_ex97 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex97
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex97 r1
INNER JOIN revalidation.r2_ex97 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex97;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            97, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v5]',
            0, 'a, b', FALSE, FALSE, 'NO DATA',
            'a, b', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 97: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex97;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex97', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex97;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex97', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        97, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v5]',
        total_rows, 'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        97, total_rows,
        'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        97, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v5]',
        -1, 'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 97, SQLERRM;
END $$;

-- Example 98: Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v6]
-- Category: Natural Join, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex98 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex98 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex98 CASCADE;
CREATE TABLE revalidation.r1_ex98 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex98 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c));
INSERT INTO revalidation.r1_ex98 (a, b, c)
SELECT ((i / 5) % 200 + 1)::int, ((i / 1) % 5 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex98 (b, c, d)
SELECT r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex98 r1
ORDER BY random()
ON CONFLICT (b, c) DO NOTHING;
CREATE TABLE revalidation.result_ex98 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex98
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex98 r1
INNER JOIN revalidation.r2_ex98 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex98;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            98, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v6]',
            0, 'a, b', FALSE, FALSE, 'NO DATA',
            'a, b', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 98: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex98;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex98', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex98;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex98', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        98, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v6]',
        total_rows, 'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        98, total_rows,
        'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        98, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v6]',
        -1, 'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 98, SQLERRM;
END $$;

-- Example 99: Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v7]
-- Category: Natural Join, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex99 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex99 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex99 CASCADE;
CREATE TABLE revalidation.r1_ex99 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex99 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c));
INSERT INTO revalidation.r1_ex99 (a, b, c)
SELECT ((i / 100) % 10 + 1)::int, ((i / 1) % 100 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex99 (b, c, d)
SELECT r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex99 r1
ORDER BY random()
ON CONFLICT (b, c) DO NOTHING;
CREATE TABLE revalidation.result_ex99 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex99
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex99 r1
INNER JOIN revalidation.r2_ex99 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex99;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            99, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v7]',
            0, 'a, b', FALSE, FALSE, 'NO DATA',
            'a, b', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 99: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex99;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex99', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex99;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex99', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        99, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v7]',
        total_rows, 'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        99, total_rows,
        'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        99, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v7]',
        -1, 'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 99, SQLERRM;
END $$;

-- Example 100: Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v8]
-- Category: Natural Join, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex100 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex100 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex100 CASCADE;
CREATE TABLE revalidation.r1_ex100 (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b));
CREATE TABLE revalidation.r2_ex100 (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c));
INSERT INTO revalidation.r1_ex100 (a, b, c)
SELECT ((i / 30) % 30 + 1)::int, ((i / 1) % 30 + 1)::int, ((i * 17) % 47 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (a, b) DO NOTHING;
INSERT INTO revalidation.r2_ex100 (b, c, d)
SELECT r1.b, r1.c, (random() * 100 + 1)::int
FROM revalidation.r1_ex100 r1
ORDER BY random()
ON CONFLICT (b, c) DO NOTHING;
CREATE TABLE revalidation.result_ex100 (b INTEGER, c INTEGER, a INTEGER, d INTEGER);
INSERT INTO revalidation.result_ex100
SELECT DISTINCT r1.b, r1.c, r1.a, r2.d
FROM revalidation.r1_ex100 r1
INNER JOIN revalidation.r2_ex100 r2 ON r1.b = r2.b AND r1.c = r2.c;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex100;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            100, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v8]',
            0, 'a, b', FALSE, FALSE, 'NO DATA',
            'a, b', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 100: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex100;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex100', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (a, b)) INTO unique_count FROM revalidation.result_ex100;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['a', 'b'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex100', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        100, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v8]',
        total_rows, 'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        100, total_rows,
        'a, b', p_unique, p_minimal, p_removable,
        'a, b', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        100, 'Natural Join', 'A', 'Case A — Jk={b,c}, G1={a,b}, G2={b,c} [v8]',
        -1, 'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'a, b', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 100, SQLERRM;
END $$;


\echo '── Equal Grains (20 examples) ──'
-- Example 41: Equal grains |G|=1, |Jk|=1 [v1]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex41 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex41 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex41 CASCADE;
CREATE TABLE revalidation.r1_ex41 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex41 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex41 (g1, v1)
SELECT ((i / 1) % 1000 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex41 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex41 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex41 (g1 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex41
SELECT DISTINCT r1.g1, r1.v1, r2.v2
FROM revalidation.r1_ex41 r1
INNER JOIN revalidation.r2_ex41 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex41;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            41, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v1]',
            0, 'g1', FALSE, FALSE, 'NO DATA',
            'g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 41: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1)) INTO unique_count FROM revalidation.result_ex41;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex41', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1)) INTO unique_count FROM revalidation.result_ex41;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex41', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        41, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v1]',
        total_rows, 'g1', p_unique, p_minimal, p_removable,
        'g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        41, total_rows,
        'g1', p_unique, p_minimal, p_removable,
        'g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        41, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v1]',
        -1, 'g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 41, SQLERRM;
END $$;

-- Example 42: Equal grains |G|=1, |Jk|=1 [v2]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex42 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex42 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex42 CASCADE;
CREATE TABLE revalidation.r1_ex42 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex42 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex42 (g1, v1)
SELECT ((i / 1) % 500 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex42 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex42 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex42 (g1 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex42
SELECT DISTINCT r1.g1, r1.v1, r2.v2
FROM revalidation.r1_ex42 r1
INNER JOIN revalidation.r2_ex42 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex42;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            42, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v2]',
            0, 'g1', FALSE, FALSE, 'NO DATA',
            'g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 42: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1)) INTO unique_count FROM revalidation.result_ex42;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex42', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1)) INTO unique_count FROM revalidation.result_ex42;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex42', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        42, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v2]',
        total_rows, 'g1', p_unique, p_minimal, p_removable,
        'g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        42, total_rows,
        'g1', p_unique, p_minimal, p_removable,
        'g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        42, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v2]',
        -1, 'g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 42, SQLERRM;
END $$;

-- Example 43: Equal grains |G|=1, |Jk|=1 [v3]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex43 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex43 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex43 CASCADE;
CREATE TABLE revalidation.r1_ex43 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex43 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex43 (g1, v1)
SELECT ((i / 1) % 200 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex43 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex43 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex43 (g1 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex43
SELECT DISTINCT r1.g1, r1.v1, r2.v2
FROM revalidation.r1_ex43 r1
INNER JOIN revalidation.r2_ex43 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex43;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            43, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v3]',
            0, 'g1', FALSE, FALSE, 'NO DATA',
            'g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 43: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1)) INTO unique_count FROM revalidation.result_ex43;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex43', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1)) INTO unique_count FROM revalidation.result_ex43;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex43', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        43, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v3]',
        total_rows, 'g1', p_unique, p_minimal, p_removable,
        'g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        43, total_rows,
        'g1', p_unique, p_minimal, p_removable,
        'g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        43, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v3]',
        -1, 'g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 43, SQLERRM;
END $$;

-- Example 44: Equal grains |G|=1, |Jk|=1 [v4]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex44 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex44 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex44 CASCADE;
CREATE TABLE revalidation.r1_ex44 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex44 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex44 (g1, v1)
SELECT ((i / 1) % 100 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex44 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex44 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex44 (g1 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex44
SELECT DISTINCT r1.g1, r1.v1, r2.v2
FROM revalidation.r1_ex44 r1
INNER JOIN revalidation.r2_ex44 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex44;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            44, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v4]',
            0, 'g1', FALSE, FALSE, 'NO DATA',
            'g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 44: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1)) INTO unique_count FROM revalidation.result_ex44;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex44', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1)) INTO unique_count FROM revalidation.result_ex44;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex44', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        44, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v4]',
        total_rows, 'g1', p_unique, p_minimal, p_removable,
        'g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        44, total_rows,
        'g1', p_unique, p_minimal, p_removable,
        'g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        44, 'Equal Grains', 'A', 'Equal grains |G|=1, |Jk|=1 [v4]',
        -1, 'g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 44, SQLERRM;
END $$;

-- Example 45: Equal grains |G|=2, |Jk|=1 [v5]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex45 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex45 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex45 CASCADE;
CREATE TABLE revalidation.r1_ex45 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex45 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex45 (g1, g2, v1)
SELECT ((i / 20) % 50 + 1)::int, ((i / 1) % 20 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex45 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex45 r1
    CROSS JOIN generate_series(1, 20) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex45 (g1 INTEGER, g2_r1 INTEGER, g2_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex45
SELECT DISTINCT r1.g1, r1.g2 AS g2_r1, r2.g2 AS g2_r2, r1.v1, r2.v2
FROM revalidation.r1_ex45 r1
INNER JOIN revalidation.r2_ex45 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex45;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            45, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v5]',
            0, 'g2_r1, g2_r2, g1', FALSE, FALSE, 'NO DATA',
            'g2_r1, g2_r2, g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 45: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g2_r2, g1)) INTO unique_count FROM revalidation.result_ex45;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g2_r2', 'g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex45', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g2_r2, g1)) INTO unique_count FROM revalidation.result_ex45;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g2_r2', 'g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex45', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        45, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v5]',
        total_rows, 'g2_r1, g2_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g2_r2, g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        45, total_rows,
        'g2_r1, g2_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g2_r2, g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        45, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v5]',
        -1, 'g2_r1, g2_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g2_r1, g2_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 45, SQLERRM;
END $$;

-- Example 46: Equal grains |G|=2, |Jk|=1 [v6]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex46 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex46 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex46 CASCADE;
CREATE TABLE revalidation.r1_ex46 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex46 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex46 (g1, g2, v1)
SELECT ((i / 25) % 40 + 1)::int, ((i / 1) % 25 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex46 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex46 r1
    CROSS JOIN generate_series(1, 25) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex46 (g1 INTEGER, g2_r1 INTEGER, g2_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex46
SELECT DISTINCT r1.g1, r1.g2 AS g2_r1, r2.g2 AS g2_r2, r1.v1, r2.v2
FROM revalidation.r1_ex46 r1
INNER JOIN revalidation.r2_ex46 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex46;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            46, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v6]',
            0, 'g2_r1, g2_r2, g1', FALSE, FALSE, 'NO DATA',
            'g2_r1, g2_r2, g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 46: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g2_r2, g1)) INTO unique_count FROM revalidation.result_ex46;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g2_r2', 'g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex46', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g2_r2, g1)) INTO unique_count FROM revalidation.result_ex46;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g2_r2', 'g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex46', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        46, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v6]',
        total_rows, 'g2_r1, g2_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g2_r2, g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        46, total_rows,
        'g2_r1, g2_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g2_r2, g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        46, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v6]',
        -1, 'g2_r1, g2_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g2_r1, g2_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 46, SQLERRM;
END $$;

-- Example 47: Equal grains |G|=2, |Jk|=1 [v7]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex47 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex47 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex47 CASCADE;
CREATE TABLE revalidation.r1_ex47 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex47 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex47 (g1, g2, v1)
SELECT ((i / 10) % 100 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex47 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex47 r1
    CROSS JOIN generate_series(1, 10) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex47 (g1 INTEGER, g2_r1 INTEGER, g2_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex47
SELECT DISTINCT r1.g1, r1.g2 AS g2_r1, r2.g2 AS g2_r2, r1.v1, r2.v2
FROM revalidation.r1_ex47 r1
INNER JOIN revalidation.r2_ex47 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex47;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            47, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v7]',
            0, 'g2_r1, g2_r2, g1', FALSE, FALSE, 'NO DATA',
            'g2_r1, g2_r2, g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 47: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g2_r2, g1)) INTO unique_count FROM revalidation.result_ex47;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g2_r2', 'g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex47', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g2_r2, g1)) INTO unique_count FROM revalidation.result_ex47;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g2_r2', 'g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex47', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        47, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v7]',
        total_rows, 'g2_r1, g2_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g2_r2, g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        47, total_rows,
        'g2_r1, g2_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g2_r2, g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        47, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=1 [v7]',
        -1, 'g2_r1, g2_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g2_r1, g2_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 47, SQLERRM;
END $$;

-- Example 48: Equal grains |G|=2, |Jk|=2 [v8]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex48 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex48 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex48 CASCADE;
CREATE TABLE revalidation.r1_ex48 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex48 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex48 (g1, g2, v1)
SELECT ((i / 20) % 50 + 1)::int, ((i / 1) % 20 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex48 (g1, g2, v2)
SELECT r1.g1, r1.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex48 r1
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex48 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex48
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex48 r1
INNER JOIN revalidation.r2_ex48 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex48;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            48, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v8]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 48: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex48;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex48', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex48;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex48', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        48, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v8]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        48, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        48, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v8]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 48, SQLERRM;
END $$;

-- Example 49: Equal grains |G|=2, |Jk|=2 [v9]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex49 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex49 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex49 CASCADE;
CREATE TABLE revalidation.r1_ex49 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex49 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex49 (g1, g2, v1)
SELECT ((i / 25) % 40 + 1)::int, ((i / 1) % 25 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex49 (g1, g2, v2)
SELECT r1.g1, r1.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex49 r1
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex49 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex49
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex49 r1
INNER JOIN revalidation.r2_ex49 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex49;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            49, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v9]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 49: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex49;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex49', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex49;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex49', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        49, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v9]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        49, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        49, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v9]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 49, SQLERRM;
END $$;

-- Example 50: Equal grains |G|=2, |Jk|=2 [v10]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex50 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex50 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex50 CASCADE;
CREATE TABLE revalidation.r1_ex50 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex50 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex50 (g1, g2, v1)
SELECT ((i / 10) % 100 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex50 (g1, g2, v2)
SELECT r1.g1, r1.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex50 r1
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex50 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex50
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex50 r1
INNER JOIN revalidation.r2_ex50 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex50;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            50, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v10]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 50: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex50;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex50', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex50;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex50', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        50, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v10]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        50, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        50, 'Equal Grains', 'A', 'Equal grains |G|=2, |Jk|=2 [v10]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 50, SQLERRM;
END $$;

-- Example 51: Equal grains |G|=3, |Jk|=1 [v11]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex51 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex51 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex51 CASCADE;
CREATE TABLE revalidation.r1_ex51 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3));
CREATE TABLE revalidation.r2_ex51 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3));
INSERT INTO revalidation.r1_ex51 (g1, g2, g3, v1)
SELECT ((i / 100) % 10 + 1)::int, ((i / 10) % 10 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3) DO NOTHING;
INSERT INTO revalidation.r2_ex51 (g1, g2, g3, v2)
SELECT r1.g1, s_g2.g2, s_g3.g3, (random() * 100 + 1)::int
FROM revalidation.r1_ex51 r1
    CROSS JOIN generate_series(1, 10) s_g2(g2)
    CROSS JOIN generate_series(1, 10) s_g3(g3)
ORDER BY random()
ON CONFLICT (g1, g2, g3) DO NOTHING;
CREATE TABLE revalidation.result_ex51 (g1 INTEGER, g2_r1 INTEGER, g2_r2 INTEGER, g3_r1 INTEGER, g3_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex51
SELECT DISTINCT r1.g1, r1.g2 AS g2_r1, r2.g2 AS g2_r2, r1.g3 AS g3_r1, r2.g3 AS g3_r2, r1.v1, r2.v2
FROM revalidation.r1_ex51 r1
INNER JOIN revalidation.r2_ex51 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex51;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            51, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=1 [v11]',
            0, 'g2_r1, g3_r1, g2_r2, g3_r2, g1', FALSE, FALSE, 'NO DATA',
            'g2_r1, g3_r1, g2_r2, g3_r2, g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 51: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g3_r1, g2_r2, g3_r2, g1)) INTO unique_count FROM revalidation.result_ex51;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g3_r1', 'g2_r2', 'g3_r2', 'g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex51', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g3_r1, g2_r2, g3_r2, g1)) INTO unique_count FROM revalidation.result_ex51;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g3_r1', 'g2_r2', 'g3_r2', 'g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex51', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        51, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=1 [v11]',
        total_rows, 'g2_r1, g3_r1, g2_r2, g3_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g3_r1, g2_r2, g3_r2, g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        51, total_rows,
        'g2_r1, g3_r1, g2_r2, g3_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g3_r1, g2_r2, g3_r2, g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        51, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=1 [v11]',
        -1, 'g2_r1, g3_r1, g2_r2, g3_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g2_r1, g3_r1, g2_r2, g3_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 51, SQLERRM;
END $$;

-- Example 52: Equal grains |G|=3, |Jk|=1 [v12]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex52 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex52 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex52 CASCADE;
CREATE TABLE revalidation.r1_ex52 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3));
CREATE TABLE revalidation.r2_ex52 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3));
INSERT INTO revalidation.r1_ex52 (g1, g2, g3, v1)
SELECT ((i / 50) % 20 + 1)::int, ((i / 5) % 10 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3) DO NOTHING;
INSERT INTO revalidation.r2_ex52 (g1, g2, g3, v2)
SELECT r1.g1, s_g2.g2, s_g3.g3, (random() * 100 + 1)::int
FROM revalidation.r1_ex52 r1
    CROSS JOIN generate_series(1, 10) s_g2(g2)
    CROSS JOIN generate_series(1, 5) s_g3(g3)
ORDER BY random()
ON CONFLICT (g1, g2, g3) DO NOTHING;
CREATE TABLE revalidation.result_ex52 (g1 INTEGER, g2_r1 INTEGER, g2_r2 INTEGER, g3_r1 INTEGER, g3_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex52
SELECT DISTINCT r1.g1, r1.g2 AS g2_r1, r2.g2 AS g2_r2, r1.g3 AS g3_r1, r2.g3 AS g3_r2, r1.v1, r2.v2
FROM revalidation.r1_ex52 r1
INNER JOIN revalidation.r2_ex52 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex52;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            52, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=1 [v12]',
            0, 'g2_r1, g3_r1, g2_r2, g3_r2, g1', FALSE, FALSE, 'NO DATA',
            'g2_r1, g3_r1, g2_r2, g3_r2, g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 52: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g3_r1, g2_r2, g3_r2, g1)) INTO unique_count FROM revalidation.result_ex52;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g3_r1', 'g2_r2', 'g3_r2', 'g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex52', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g3_r1, g2_r2, g3_r2, g1)) INTO unique_count FROM revalidation.result_ex52;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g3_r1', 'g2_r2', 'g3_r2', 'g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex52', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        52, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=1 [v12]',
        total_rows, 'g2_r1, g3_r1, g2_r2, g3_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g3_r1, g2_r2, g3_r2, g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        52, total_rows,
        'g2_r1, g3_r1, g2_r2, g3_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g3_r1, g2_r2, g3_r2, g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        52, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=1 [v12]',
        -1, 'g2_r1, g3_r1, g2_r2, g3_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g2_r1, g3_r1, g2_r2, g3_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 52, SQLERRM;
END $$;

-- Example 53: Equal grains |G|=3, |Jk|=2 [v13]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex53 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex53 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex53 CASCADE;
CREATE TABLE revalidation.r1_ex53 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3));
CREATE TABLE revalidation.r2_ex53 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3));
INSERT INTO revalidation.r1_ex53 (g1, g2, g3, v1)
SELECT ((i / 100) % 10 + 1)::int, ((i / 10) % 10 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3) DO NOTHING;
INSERT INTO revalidation.r2_ex53 (g1, g2, g3, v2)
SELECT r1.g1, r1.g2, s_g3.g3, (random() * 100 + 1)::int
FROM revalidation.r1_ex53 r1
    CROSS JOIN generate_series(1, 10) s_g3(g3)
ORDER BY random()
ON CONFLICT (g1, g2, g3) DO NOTHING;
CREATE TABLE revalidation.result_ex53 (g1 INTEGER, g2 INTEGER, g3_r1 INTEGER, g3_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex53
SELECT DISTINCT r1.g1, r1.g2, r1.g3 AS g3_r1, r2.g3 AS g3_r2, r1.v1, r2.v2
FROM revalidation.r1_ex53 r1
INNER JOIN revalidation.r2_ex53 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex53;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            53, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=2 [v13]',
            0, 'g3_r1, g3_r2, g1, g2', FALSE, FALSE, 'NO DATA',
            'g3_r1, g3_r2, g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 53: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g3_r1, g3_r2, g1, g2)) INTO unique_count FROM revalidation.result_ex53;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g3_r1', 'g3_r2', 'g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex53', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g3_r1, g3_r2, g1, g2)) INTO unique_count FROM revalidation.result_ex53;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g3_r1', 'g3_r2', 'g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex53', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        53, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=2 [v13]',
        total_rows, 'g3_r1, g3_r2, g1, g2', p_unique, p_minimal, p_removable,
        'g3_r1, g3_r2, g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        53, total_rows,
        'g3_r1, g3_r2, g1, g2', p_unique, p_minimal, p_removable,
        'g3_r1, g3_r2, g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        53, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=2 [v13]',
        -1, 'g3_r1, g3_r2, g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g3_r1, g3_r2, g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 53, SQLERRM;
END $$;

-- Example 54: Equal grains |G|=3, |Jk|=2 [v14]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex54 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex54 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex54 CASCADE;
CREATE TABLE revalidation.r1_ex54 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3));
CREATE TABLE revalidation.r2_ex54 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3));
INSERT INTO revalidation.r1_ex54 (g1, g2, g3, v1)
SELECT ((i / 50) % 20 + 1)::int, ((i / 5) % 10 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3) DO NOTHING;
INSERT INTO revalidation.r2_ex54 (g1, g2, g3, v2)
SELECT r1.g1, r1.g2, s_g3.g3, (random() * 100 + 1)::int
FROM revalidation.r1_ex54 r1
    CROSS JOIN generate_series(1, 5) s_g3(g3)
ORDER BY random()
ON CONFLICT (g1, g2, g3) DO NOTHING;
CREATE TABLE revalidation.result_ex54 (g1 INTEGER, g2 INTEGER, g3_r1 INTEGER, g3_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex54
SELECT DISTINCT r1.g1, r1.g2, r1.g3 AS g3_r1, r2.g3 AS g3_r2, r1.v1, r2.v2
FROM revalidation.r1_ex54 r1
INNER JOIN revalidation.r2_ex54 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex54;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            54, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=2 [v14]',
            0, 'g3_r1, g3_r2, g1, g2', FALSE, FALSE, 'NO DATA',
            'g3_r1, g3_r2, g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 54: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g3_r1, g3_r2, g1, g2)) INTO unique_count FROM revalidation.result_ex54;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g3_r1', 'g3_r2', 'g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex54', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g3_r1, g3_r2, g1, g2)) INTO unique_count FROM revalidation.result_ex54;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g3_r1', 'g3_r2', 'g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex54', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        54, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=2 [v14]',
        total_rows, 'g3_r1, g3_r2, g1, g2', p_unique, p_minimal, p_removable,
        'g3_r1, g3_r2, g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        54, total_rows,
        'g3_r1, g3_r2, g1, g2', p_unique, p_minimal, p_removable,
        'g3_r1, g3_r2, g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        54, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=2 [v14]',
        -1, 'g3_r1, g3_r2, g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g3_r1, g3_r2, g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 54, SQLERRM;
END $$;

-- Example 55: Equal grains |G|=3, |Jk|=3 [v15]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex55 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex55 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex55 CASCADE;
CREATE TABLE revalidation.r1_ex55 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3));
CREATE TABLE revalidation.r2_ex55 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3));
INSERT INTO revalidation.r1_ex55 (g1, g2, g3, v1)
SELECT ((i / 100) % 10 + 1)::int, ((i / 10) % 10 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3) DO NOTHING;
INSERT INTO revalidation.r2_ex55 (g1, g2, g3, v2)
SELECT r1.g1, r1.g2, r1.g3, (random() * 100 + 1)::int
FROM revalidation.r1_ex55 r1
ORDER BY random()
ON CONFLICT (g1, g2, g3) DO NOTHING;
CREATE TABLE revalidation.result_ex55 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex55
SELECT DISTINCT r1.g1, r1.g2, r1.g3, r1.v1, r2.v2
FROM revalidation.r1_ex55 r1
INNER JOIN revalidation.r2_ex55 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2 AND r1.g3 = r2.g3;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex55;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            55, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=3 [v15]',
            0, 'g1, g2, g3', FALSE, FALSE, 'NO DATA',
            'g1, g2, g3', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 55: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2, g3)) INTO unique_count FROM revalidation.result_ex55;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2', 'g3'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex55', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2, g3)) INTO unique_count FROM revalidation.result_ex55;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2', 'g3'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex55', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        55, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=3 [v15]',
        total_rows, 'g1, g2, g3', p_unique, p_minimal, p_removable,
        'g1, g2, g3', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        55, total_rows,
        'g1, g2, g3', p_unique, p_minimal, p_removable,
        'g1, g2, g3', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        55, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=3 [v15]',
        -1, 'g1, g2, g3', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2, g3', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 55, SQLERRM;
END $$;

-- Example 56: Equal grains |G|=3, |Jk|=3 [v16]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex56 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex56 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex56 CASCADE;
CREATE TABLE revalidation.r1_ex56 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3));
CREATE TABLE revalidation.r2_ex56 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3));
INSERT INTO revalidation.r1_ex56 (g1, g2, g3, v1)
SELECT ((i / 50) % 20 + 1)::int, ((i / 5) % 10 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3) DO NOTHING;
INSERT INTO revalidation.r2_ex56 (g1, g2, g3, v2)
SELECT r1.g1, r1.g2, r1.g3, (random() * 100 + 1)::int
FROM revalidation.r1_ex56 r1
ORDER BY random()
ON CONFLICT (g1, g2, g3) DO NOTHING;
CREATE TABLE revalidation.result_ex56 (g1 INTEGER, g2 INTEGER, g3 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex56
SELECT DISTINCT r1.g1, r1.g2, r1.g3, r1.v1, r2.v2
FROM revalidation.r1_ex56 r1
INNER JOIN revalidation.r2_ex56 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2 AND r1.g3 = r2.g3;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex56;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            56, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=3 [v16]',
            0, 'g1, g2, g3', FALSE, FALSE, 'NO DATA',
            'g1, g2, g3', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 56: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2, g3)) INTO unique_count FROM revalidation.result_ex56;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2', 'g3'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex56', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2, g3)) INTO unique_count FROM revalidation.result_ex56;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2', 'g3'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex56', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        56, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=3 [v16]',
        total_rows, 'g1, g2, g3', p_unique, p_minimal, p_removable,
        'g1, g2, g3', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        56, total_rows,
        'g1, g2, g3', p_unique, p_minimal, p_removable,
        'g1, g2, g3', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        56, 'Equal Grains', 'A', 'Equal grains |G|=3, |Jk|=3 [v16]',
        -1, 'g1, g2, g3', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2, g3', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 56, SQLERRM;
END $$;

-- Example 57: Equal grains |G|=4, |Jk|=1 [v17]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex57 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex57 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex57 CASCADE;
CREATE TABLE revalidation.r1_ex57 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3, g4));
CREATE TABLE revalidation.r2_ex57 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3, g4));
INSERT INTO revalidation.r1_ex57 (g1, g2, g3, g4, v1)
SELECT ((i / 200) % 5 + 1)::int, ((i / 40) % 5 + 1)::int, ((i / 8) % 5 + 1)::int, ((i / 1) % 8 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3, g4) DO NOTHING;
INSERT INTO revalidation.r2_ex57 (g1, g2, g3, g4, v2)
SELECT r1.g1, s_g2.g2, s_g3.g3, s_g4.g4, (random() * 100 + 1)::int
FROM revalidation.r1_ex57 r1
    CROSS JOIN generate_series(1, 5) s_g2(g2)
    CROSS JOIN generate_series(1, 5) s_g3(g3)
    CROSS JOIN generate_series(1, 8) s_g4(g4)
ORDER BY random()
ON CONFLICT (g1, g2, g3, g4) DO NOTHING;
CREATE TABLE revalidation.result_ex57 (g1 INTEGER, g2_r1 INTEGER, g2_r2 INTEGER, g3_r1 INTEGER, g3_r2 INTEGER, g4_r1 INTEGER, g4_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex57
SELECT DISTINCT r1.g1, r1.g2 AS g2_r1, r2.g2 AS g2_r2, r1.g3 AS g3_r1, r2.g3 AS g3_r2, r1.g4 AS g4_r1, r2.g4 AS g4_r2, r1.v1, r2.v2
FROM revalidation.r1_ex57 r1
INNER JOIN revalidation.r2_ex57 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex57;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            57, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=1 [v17]',
            0, 'g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1', FALSE, FALSE, 'NO DATA',
            'g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 57: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1)) INTO unique_count FROM revalidation.result_ex57;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g3_r1', 'g4_r1', 'g2_r2', 'g3_r2', 'g4_r2', 'g1'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex57', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1)) INTO unique_count FROM revalidation.result_ex57;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g2_r1', 'g3_r1', 'g4_r1', 'g2_r2', 'g3_r2', 'g4_r2', 'g1'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex57', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        57, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=1 [v17]',
        total_rows, 'g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        57, total_rows,
        'g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1', p_unique, p_minimal, p_removable,
        'g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        57, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=1 [v17]',
        -1, 'g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g2_r1, g3_r1, g4_r1, g2_r2, g3_r2, g4_r2, g1', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 57, SQLERRM;
END $$;

-- Example 58: Equal grains |G|=4, |Jk|=2 [v18]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex58 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex58 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex58 CASCADE;
CREATE TABLE revalidation.r1_ex58 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3, g4));
CREATE TABLE revalidation.r2_ex58 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3, g4));
INSERT INTO revalidation.r1_ex58 (g1, g2, g3, g4, v1)
SELECT ((i / 200) % 5 + 1)::int, ((i / 40) % 5 + 1)::int, ((i / 8) % 5 + 1)::int, ((i / 1) % 8 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3, g4) DO NOTHING;
INSERT INTO revalidation.r2_ex58 (g1, g2, g3, g4, v2)
SELECT r1.g1, r1.g2, s_g3.g3, s_g4.g4, (random() * 100 + 1)::int
FROM revalidation.r1_ex58 r1
    CROSS JOIN generate_series(1, 5) s_g3(g3)
    CROSS JOIN generate_series(1, 8) s_g4(g4)
ORDER BY random()
ON CONFLICT (g1, g2, g3, g4) DO NOTHING;
CREATE TABLE revalidation.result_ex58 (g1 INTEGER, g2 INTEGER, g3_r1 INTEGER, g3_r2 INTEGER, g4_r1 INTEGER, g4_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex58
SELECT DISTINCT r1.g1, r1.g2, r1.g3 AS g3_r1, r2.g3 AS g3_r2, r1.g4 AS g4_r1, r2.g4 AS g4_r2, r1.v1, r2.v2
FROM revalidation.r1_ex58 r1
INNER JOIN revalidation.r2_ex58 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex58;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            58, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=2 [v18]',
            0, 'g3_r1, g4_r1, g3_r2, g4_r2, g1, g2', FALSE, FALSE, 'NO DATA',
            'g3_r1, g4_r1, g3_r2, g4_r2, g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 58: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g3_r1, g4_r1, g3_r2, g4_r2, g1, g2)) INTO unique_count FROM revalidation.result_ex58;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g3_r1', 'g4_r1', 'g3_r2', 'g4_r2', 'g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex58', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g3_r1, g4_r1, g3_r2, g4_r2, g1, g2)) INTO unique_count FROM revalidation.result_ex58;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g3_r1', 'g4_r1', 'g3_r2', 'g4_r2', 'g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex58', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        58, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=2 [v18]',
        total_rows, 'g3_r1, g4_r1, g3_r2, g4_r2, g1, g2', p_unique, p_minimal, p_removable,
        'g3_r1, g4_r1, g3_r2, g4_r2, g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        58, total_rows,
        'g3_r1, g4_r1, g3_r2, g4_r2, g1, g2', p_unique, p_minimal, p_removable,
        'g3_r1, g4_r1, g3_r2, g4_r2, g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        58, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=2 [v18]',
        -1, 'g3_r1, g4_r1, g3_r2, g4_r2, g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g3_r1, g4_r1, g3_r2, g4_r2, g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 58, SQLERRM;
END $$;

-- Example 59: Equal grains |G|=4, |Jk|=3 [v19]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex59 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex59 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex59 CASCADE;
CREATE TABLE revalidation.r1_ex59 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3, g4));
CREATE TABLE revalidation.r2_ex59 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3, g4));
INSERT INTO revalidation.r1_ex59 (g1, g2, g3, g4, v1)
SELECT ((i / 200) % 5 + 1)::int, ((i / 40) % 5 + 1)::int, ((i / 8) % 5 + 1)::int, ((i / 1) % 8 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3, g4) DO NOTHING;
INSERT INTO revalidation.r2_ex59 (g1, g2, g3, g4, v2)
SELECT r1.g1, r1.g2, r1.g3, s_g4.g4, (random() * 100 + 1)::int
FROM revalidation.r1_ex59 r1
    CROSS JOIN generate_series(1, 8) s_g4(g4)
ORDER BY random()
ON CONFLICT (g1, g2, g3, g4) DO NOTHING;
CREATE TABLE revalidation.result_ex59 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4_r1 INTEGER, g4_r2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex59
SELECT DISTINCT r1.g1, r1.g2, r1.g3, r1.g4 AS g4_r1, r2.g4 AS g4_r2, r1.v1, r2.v2
FROM revalidation.r1_ex59 r1
INNER JOIN revalidation.r2_ex59 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2 AND r1.g3 = r2.g3;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex59;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            59, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=3 [v19]',
            0, 'g4_r1, g4_r2, g1, g2, g3', FALSE, FALSE, 'NO DATA',
            'g4_r1, g4_r2, g1, g2, g3', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 59: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g4_r1, g4_r2, g1, g2, g3)) INTO unique_count FROM revalidation.result_ex59;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g4_r1', 'g4_r2', 'g1', 'g2', 'g3'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex59', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g4_r1, g4_r2, g1, g2, g3)) INTO unique_count FROM revalidation.result_ex59;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g4_r1', 'g4_r2', 'g1', 'g2', 'g3'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex59', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        59, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=3 [v19]',
        total_rows, 'g4_r1, g4_r2, g1, g2, g3', p_unique, p_minimal, p_removable,
        'g4_r1, g4_r2, g1, g2, g3', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        59, total_rows,
        'g4_r1, g4_r2, g1, g2, g3', p_unique, p_minimal, p_removable,
        'g4_r1, g4_r2, g1, g2, g3', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        59, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=3 [v19]',
        -1, 'g4_r1, g4_r2, g1, g2, g3', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g4_r1, g4_r2, g1, g2, g3', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 59, SQLERRM;
END $$;

-- Example 60: Equal grains |G|=4, |Jk|=4 [v20]
-- Category: Equal Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex60 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex60 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex60 CASCADE;
CREATE TABLE revalidation.r1_ex60 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2, g3, g4));
CREATE TABLE revalidation.r2_ex60 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2, g3, g4));
INSERT INTO revalidation.r1_ex60 (g1, g2, g3, g4, v1)
SELECT ((i / 200) % 5 + 1)::int, ((i / 40) % 5 + 1)::int, ((i / 8) % 5 + 1)::int, ((i / 1) % 8 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2, g3, g4) DO NOTHING;
INSERT INTO revalidation.r2_ex60 (g1, g2, g3, g4, v2)
SELECT r1.g1, r1.g2, r1.g3, r1.g4, (random() * 100 + 1)::int
FROM revalidation.r1_ex60 r1
ORDER BY random()
ON CONFLICT (g1, g2, g3, g4) DO NOTHING;
CREATE TABLE revalidation.result_ex60 (g1 INTEGER, g2 INTEGER, g3 INTEGER, g4 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex60
SELECT DISTINCT r1.g1, r1.g2, r1.g3, r1.g4, r1.v1, r2.v2
FROM revalidation.r1_ex60 r1
INNER JOIN revalidation.r2_ex60 r2 ON r1.g1 = r2.g1 AND r1.g2 = r2.g2 AND r1.g3 = r2.g3 AND r1.g4 = r2.g4;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex60;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            60, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=4 [v20]',
            0, 'g1, g2, g3, g4', FALSE, FALSE, 'NO DATA',
            'g1, g2, g3, g4', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 60: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2, g3, g4)) INTO unique_count FROM revalidation.result_ex60;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2', 'g3', 'g4'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex60', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2, g3, g4)) INTO unique_count FROM revalidation.result_ex60;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2', 'g3', 'g4'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex60', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        60, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=4 [v20]',
        total_rows, 'g1, g2, g3, g4', p_unique, p_minimal, p_removable,
        'g1, g2, g3, g4', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        60, total_rows,
        'g1, g2, g3, g4', p_unique, p_minimal, p_removable,
        'g1, g2, g3, g4', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        60, 'Equal Grains', 'A', 'Equal grains |G|=4, |Jk|=4 [v20]',
        -1, 'g1, g2, g3, g4', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2, g3, g4', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 60, SQLERRM;
END $$;


\echo '── Ordered Grains (25 examples) ──'
-- Example 61: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v1]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex61 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex61 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex61 CASCADE;
CREATE TABLE revalidation.r1_ex61 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex61 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex61 (g1, g2, v1)
SELECT ((i / 20) % 50 + 1)::int, ((i / 1) % 20 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex61 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex61 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex61 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex61
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex61 r1
INNER JOIN revalidation.r2_ex61 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex61;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            61, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v1]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 61: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex61;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex61', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex61;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex61', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        61, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v1]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        61, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        61, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v1]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 61, SQLERRM;
END $$;

-- Example 62: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v2]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex62 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex62 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex62 CASCADE;
CREATE TABLE revalidation.r1_ex62 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex62 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex62 (g1, g2, v1)
SELECT ((i / 25) % 40 + 1)::int, ((i / 1) % 25 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex62 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex62 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex62 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex62
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex62 r1
INNER JOIN revalidation.r2_ex62 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex62;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            62, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v2]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 62: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex62;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex62', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex62;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex62', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        62, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v2]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        62, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        62, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v2]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 62, SQLERRM;
END $$;

-- Example 63: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v3]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex63 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex63 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex63 CASCADE;
CREATE TABLE revalidation.r1_ex63 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex63 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex63 (g1, g2, v1)
SELECT ((i / 10) % 100 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex63 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex63 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex63 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex63
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex63 r1
INNER JOIN revalidation.r2_ex63 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex63;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            63, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v3]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 63: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex63;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex63', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex63;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex63', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        63, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v3]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        63, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        63, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v3]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 63, SQLERRM;
END $$;

-- Example 64: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v4]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex64 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex64 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex64 CASCADE;
CREATE TABLE revalidation.r1_ex64 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex64 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex64 (g1, g2, v1)
SELECT ((i / 40) % 25 + 1)::int, ((i / 1) % 40 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex64 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex64 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex64 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex64
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex64 r1
INNER JOIN revalidation.r2_ex64 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex64;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            64, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v4]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 64: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex64;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex64', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex64;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex64', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        64, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v4]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        64, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        64, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v4]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 64, SQLERRM;
END $$;

-- Example 65: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v5]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex65 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex65 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex65 CASCADE;
CREATE TABLE revalidation.r1_ex65 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex65 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex65 (g1, g2, v1)
SELECT ((i / 50) % 20 + 1)::int, ((i / 1) % 50 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex65 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex65 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex65 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex65
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex65 r1
INNER JOIN revalidation.r2_ex65 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex65;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            65, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v5]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 65: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex65;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex65', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex65;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex65', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        65, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v5]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        65, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        65, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v5]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 65, SQLERRM;
END $$;

-- Example 66: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v6]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex66 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex66 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex66 CASCADE;
CREATE TABLE revalidation.r1_ex66 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex66 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex66 (g1, g2, v1)
SELECT ((i / 5) % 200 + 1)::int, ((i / 1) % 5 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex66 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex66 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex66 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex66
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex66 r1
INNER JOIN revalidation.r2_ex66 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex66;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            66, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v6]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 66: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex66;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex66', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex66;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex66', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        66, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v6]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        66, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        66, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v6]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 66, SQLERRM;
END $$;

-- Example 67: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v7]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex67 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex67 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex67 CASCADE;
CREATE TABLE revalidation.r1_ex67 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex67 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex67 (g1, g2, v1)
SELECT ((i / 100) % 10 + 1)::int, ((i / 1) % 100 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex67 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex67 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex67 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex67
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex67 r1
INNER JOIN revalidation.r2_ex67 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex67;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            67, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v7]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 67: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex67;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex67', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex67;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex67', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        67, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v7]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        67, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        67, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v7]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 67, SQLERRM;
END $$;

-- Example 68: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v8]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex68 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex68 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex68 CASCADE;
CREATE TABLE revalidation.r1_ex68 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex68 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex68 (g1, g2, v1)
SELECT ((i / 30) % 30 + 1)::int, ((i / 1) % 30 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex68 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex68 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex68 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex68
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex68 r1
INNER JOIN revalidation.r2_ex68 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex68;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            68, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v8]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 68: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex68;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex68', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex68;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex68', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        68, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v8]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        68, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        68, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v8]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 68, SQLERRM;
END $$;

-- Example 69: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v9]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex69 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex69 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex69 CASCADE;
CREATE TABLE revalidation.r1_ex69 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex69 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex69 (g1, g2, v1)
SELECT ((i / 20) % 50 + 1)::int, ((i / 1) % 20 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex69 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex69 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex69 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex69
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex69 r1
INNER JOIN revalidation.r2_ex69 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex69;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            69, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v9]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 69: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex69;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex69', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex69;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex69', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        69, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v9]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        69, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        69, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v9]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 69, SQLERRM;
END $$;

-- Example 70: Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v10]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex70 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex70 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex70 CASCADE;
CREATE TABLE revalidation.r1_ex70 (g1 INTEGER, g2 INTEGER, v1 INTEGER, PRIMARY KEY (g1, g2));
CREATE TABLE revalidation.r2_ex70 (g1 INTEGER, v2 INTEGER, PRIMARY KEY (g1));
INSERT INTO revalidation.r1_ex70 (g1, g2, v1)
SELECT ((i / 10) % 100 + 1)::int, ((i / 1) % 10 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1, g2) DO NOTHING;
INSERT INTO revalidation.r2_ex70 (g1, v2)
SELECT r1.g1, (random() * 100 + 1)::int
FROM revalidation.r1_ex70 r1
ORDER BY random()
ON CONFLICT (g1) DO NOTHING;
CREATE TABLE revalidation.result_ex70 (g1 INTEGER, g2 INTEGER, v1 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex70
SELECT DISTINCT r1.g1, r1.g2, r1.v1, r2.v2
FROM revalidation.r1_ex70 r1
INNER JOIN revalidation.r2_ex70 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex70;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            70, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v10]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 70: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex70;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex70', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex70;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex70', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        70, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v10]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        70, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        70, 'Ordered Grains', 'A', 'Ordered — G1={g1,g2} > G2={g1}, Jk={g1} [v10]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 70, SQLERRM;
END $$;

-- Example 71: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v11]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex71 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex71 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex71 CASCADE;
CREATE TABLE revalidation.r1_ex71 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex71 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex71 (g1, v1)
SELECT ((i / 1) % 1000 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex71 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex71 r1
    CROSS JOIN generate_series(1, 20) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex71 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex71
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex71 r1
INNER JOIN revalidation.r2_ex71 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex71;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            71, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v11]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 71: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex71;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex71', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex71;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex71', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        71, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v11]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        71, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        71, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v11]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 71, SQLERRM;
END $$;

-- Example 72: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v12]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex72 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex72 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex72 CASCADE;
CREATE TABLE revalidation.r1_ex72 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex72 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex72 (g1, v1)
SELECT ((i / 1) % 500 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex72 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex72 r1
    CROSS JOIN generate_series(1, 25) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex72 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex72
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex72 r1
INNER JOIN revalidation.r2_ex72 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex72;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            72, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v12]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 72: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex72;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex72', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex72;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex72', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        72, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v12]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        72, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        72, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v12]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 72, SQLERRM;
END $$;

-- Example 73: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v13]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex73 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex73 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex73 CASCADE;
CREATE TABLE revalidation.r1_ex73 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex73 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex73 (g1, v1)
SELECT ((i / 1) % 200 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex73 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex73 r1
    CROSS JOIN generate_series(1, 10) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex73 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex73
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex73 r1
INNER JOIN revalidation.r2_ex73 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex73;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            73, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v13]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 73: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex73;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex73', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex73;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex73', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        73, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v13]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        73, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        73, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v13]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 73, SQLERRM;
END $$;

-- Example 74: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v14]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex74 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex74 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex74 CASCADE;
CREATE TABLE revalidation.r1_ex74 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex74 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex74 (g1, v1)
SELECT ((i / 1) % 100 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex74 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex74 r1
    CROSS JOIN generate_series(1, 40) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex74 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex74
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex74 r1
INNER JOIN revalidation.r2_ex74 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex74;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            74, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v14]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 74: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex74;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex74', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex74;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex74', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        74, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v14]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        74, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        74, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v14]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 74, SQLERRM;
END $$;

-- Example 75: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v15]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex75 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex75 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex75 CASCADE;
CREATE TABLE revalidation.r1_ex75 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex75 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex75 (g1, v1)
SELECT ((i / 1) % 50 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex75 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex75 r1
    CROSS JOIN generate_series(1, 50) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex75 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex75
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex75 r1
INNER JOIN revalidation.r2_ex75 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex75;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            75, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v15]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 75: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex75;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex75', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex75;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex75', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        75, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v15]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        75, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        75, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v15]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 75, SQLERRM;
END $$;

-- Example 76: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v16]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex76 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex76 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex76 CASCADE;
CREATE TABLE revalidation.r1_ex76 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex76 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex76 (g1, v1)
SELECT ((i / 1) % 1000 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex76 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex76 r1
    CROSS JOIN generate_series(1, 5) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex76 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex76
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex76 r1
INNER JOIN revalidation.r2_ex76 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex76;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            76, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v16]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 76: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex76;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex76', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex76;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex76', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        76, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v16]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        76, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        76, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v16]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 76, SQLERRM;
END $$;

-- Example 77: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v17]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex77 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex77 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex77 CASCADE;
CREATE TABLE revalidation.r1_ex77 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex77 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex77 (g1, v1)
SELECT ((i / 1) % 500 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex77 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex77 r1
    CROSS JOIN generate_series(1, 100) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex77 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex77
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex77 r1
INNER JOIN revalidation.r2_ex77 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex77;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            77, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v17]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 77: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex77;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex77', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex77;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex77', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        77, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v17]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        77, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        77, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v17]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 77, SQLERRM;
END $$;

-- Example 78: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v18]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex78 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex78 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex78 CASCADE;
CREATE TABLE revalidation.r1_ex78 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex78 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex78 (g1, v1)
SELECT ((i / 1) % 200 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex78 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex78 r1
    CROSS JOIN generate_series(1, 30) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex78 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex78
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex78 r1
INNER JOIN revalidation.r2_ex78 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex78;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            78, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v18]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 78: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex78;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex78', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex78;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex78', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        78, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v18]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        78, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        78, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v18]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 78, SQLERRM;
END $$;

-- Example 79: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v19]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex79 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex79 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex79 CASCADE;
CREATE TABLE revalidation.r1_ex79 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex79 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex79 (g1, v1)
SELECT ((i / 1) % 500 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex79 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex79 r1
    CROSS JOIN generate_series(1, 20) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex79 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex79
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex79 r1
INNER JOIN revalidation.r2_ex79 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex79;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            79, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v19]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 79: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex79;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex79', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex79;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex79', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        79, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v19]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        79, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        79, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v19]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 79, SQLERRM;
END $$;

-- Example 80: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v20]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex80 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex80 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex80 CASCADE;
CREATE TABLE revalidation.r1_ex80 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex80 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex80 (g1, v1)
SELECT ((i / 1) % 1000 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex80 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex80 r1
    CROSS JOIN generate_series(1, 10) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex80 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex80
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex80 r1
INNER JOIN revalidation.r2_ex80 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex80;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            80, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v20]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 80: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex80;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex80', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex80;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex80', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        80, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v20]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        80, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        80, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v20]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 80, SQLERRM;
END $$;

-- Example 81: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v21]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex81 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex81 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex81 CASCADE;
CREATE TABLE revalidation.r1_ex81 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex81 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex81 (g1, v1)
SELECT ((i / 1) % 100 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex81 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex81 r1
    CROSS JOIN generate_series(1, 20) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex81 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex81
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex81 r1
INNER JOIN revalidation.r2_ex81 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex81;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            81, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v21]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 81: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex81;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex81', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex81;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex81', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        81, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v21]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        81, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        81, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v21]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 81, SQLERRM;
END $$;

-- Example 82: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v22]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex82 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex82 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex82 CASCADE;
CREATE TABLE revalidation.r1_ex82 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex82 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex82 (g1, v1)
SELECT ((i / 1) % 200 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex82 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex82 r1
    CROSS JOIN generate_series(1, 25) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex82 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex82
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex82 r1
INNER JOIN revalidation.r2_ex82 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex82;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            82, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v22]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 82: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex82;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex82', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex82;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex82', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        82, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v22]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        82, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        82, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v22]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 82, SQLERRM;
END $$;

-- Example 83: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v23]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex83 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex83 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex83 CASCADE;
CREATE TABLE revalidation.r1_ex83 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex83 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex83 (g1, v1)
SELECT ((i / 1) % 500 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex83 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex83 r1
    CROSS JOIN generate_series(1, 10) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex83 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex83
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex83 r1
INNER JOIN revalidation.r2_ex83 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex83;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            83, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v23]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 83: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex83;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex83', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex83;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex83', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        83, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v23]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        83, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        83, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v23]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 83, SQLERRM;
END $$;

-- Example 84: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v24]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex84 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex84 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex84 CASCADE;
CREATE TABLE revalidation.r1_ex84 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex84 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex84 (g1, v1)
SELECT ((i / 1) % 1000 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex84 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex84 r1
    CROSS JOIN generate_series(1, 5) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex84 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex84
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex84 r1
INNER JOIN revalidation.r2_ex84 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex84;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            84, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v24]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 84: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex84;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex84', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex84;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex84', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        84, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v24]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        84, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        84, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v24]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 84, SQLERRM;
END $$;

-- Example 85: Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v25]
-- Category: Ordered Grains, Case: A
DROP TABLE IF EXISTS revalidation.r1_ex85 CASCADE;
DROP TABLE IF EXISTS revalidation.r2_ex85 CASCADE;
DROP TABLE IF EXISTS revalidation.result_ex85 CASCADE;
CREATE TABLE revalidation.r1_ex85 (g1 INTEGER, v1 INTEGER, PRIMARY KEY (g1));
CREATE TABLE revalidation.r2_ex85 (g1 INTEGER, g2 INTEGER, v2 INTEGER, PRIMARY KEY (g1, g2));
INSERT INTO revalidation.r1_ex85 (g1, v1)
SELECT ((i / 1) % 50 + 1)::int, (random() * 100 + 1)::int
FROM generate_series(1, 1000) s(i)
ON CONFLICT (g1) DO NOTHING;
INSERT INTO revalidation.r2_ex85 (g1, g2, v2)
SELECT r1.g1, s_g2.g2, (random() * 100 + 1)::int
FROM revalidation.r1_ex85 r1
    CROSS JOIN generate_series(1, 100) s_g2(g2)
ORDER BY random()
ON CONFLICT (g1, g2) DO NOTHING;
CREATE TABLE revalidation.result_ex85 (g1 INTEGER, v1 INTEGER, g2 INTEGER, v2 INTEGER);
INSERT INTO revalidation.result_ex85
SELECT DISTINCT r1.g1, r1.v1, r2.g2, r2.v2
FROM revalidation.r1_ex85 r1
INNER JOIN revalidation.r2_ex85 r2 ON r1.g1 = r2.g1;

DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM revalidation.result_ex85;

    IF total_rows = 0 THEN
        INSERT INTO revalidation.test_results VALUES (
            85, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v25]',
            0, 'g1, g2', FALSE, FALSE, 'NO DATA',
            'g1, g2', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex 85: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex85;
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex85', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT (g1, g2)) INTO unique_count FROM revalidation.result_ex85;
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY['g1', 'g2'];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM revalidation.result_ex85', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO revalidation.test_results VALUES (
        85, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v25]',
        total_rows, 'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        85, total_rows,
        'g1, g2', p_unique, p_minimal, p_removable,
        'g1, g2', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO revalidation.test_results VALUES (
        85, 'Ordered Grains', 'A', 'Ordered — G1={g1} < G2={g1,g2}, Jk={g1} [v25]',
        -1, 'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        'g1, g2', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', 85, SQLERRM;
END $$;



\echo ''
\echo '========================================================'
\echo 'SUMMARY REPORT'
\echo '========================================================'
\echo ''

-- Overall summary
DO $$
DECLARE
    total INTEGER;
    case_a INTEGER;
    case_b INTEGER;
    paper_uniq_pass INTEGER;
    paper_min_pass INTEGER;
    paper_min_fail INTEGER;
    corr_uniq_pass INTEGER;
    corr_min_pass INTEGER;
    no_data INTEGER;
    errors INTEGER;
BEGIN
    SELECT COUNT(*) INTO total FROM revalidation.test_results;
    SELECT COUNT(*) INTO case_a FROM revalidation.test_results WHERE case_type = 'A';
    SELECT COUNT(*) INTO case_b FROM revalidation.test_results WHERE case_type = 'B';
    SELECT COUNT(*) INTO no_data FROM revalidation.test_results WHERE result_rows = 0;
    SELECT COUNT(*) INTO errors FROM revalidation.test_results WHERE result_rows < 0;

    SELECT COUNT(*) INTO paper_uniq_pass FROM revalidation.test_results
        WHERE paper_unique = TRUE AND result_rows > 0;
    SELECT COUNT(*) INTO paper_min_pass FROM revalidation.test_results
        WHERE paper_minimal = TRUE AND result_rows > 0;
    SELECT COUNT(*) INTO paper_min_fail FROM revalidation.test_results
        WHERE paper_minimal = FALSE AND paper_unique = TRUE AND result_rows > 0;

    SELECT COUNT(*) INTO corr_uniq_pass FROM revalidation.test_results
        WHERE corrected_unique = TRUE AND result_rows > 0;
    SELECT COUNT(*) INTO corr_min_pass FROM revalidation.test_results
        WHERE corrected_minimal = TRUE AND result_rows > 0;

    RAISE NOTICE '';
    RAISE NOTICE 'Total examples:        %', total;
    RAISE NOTICE '  Case A:              %', case_a;
    RAISE NOTICE '  Case B:              %', case_b;
    RAISE NOTICE '  No data (0 rows):    %', no_data;
    RAISE NOTICE '  Errors:              %', errors;
    RAISE NOTICE '';
    RAISE NOTICE '── PAPER FORMULA (Theorem 6.1) ──';
    RAISE NOTICE '  Uniqueness pass:     %/%', paper_uniq_pass, total - no_data - errors;
    RAISE NOTICE '  Minimality pass:     %/%', paper_min_pass, total - no_data - errors;
    RAISE NOTICE '  Minimality FAIL:     %  (all should be Case B)', paper_min_fail;
    RAISE NOTICE '';
    RAISE NOTICE '── CORRECTED FORMULA ──';
    RAISE NOTICE '  Uniqueness pass:     %/%', corr_uniq_pass, total - no_data - errors;
    RAISE NOTICE '  Minimality pass:     %/%', corr_min_pass, total - no_data - errors;
    RAISE NOTICE '';

    IF paper_min_fail = case_b AND corr_min_pass = (total - no_data - errors) THEN
        RAISE NOTICE '✓ VALIDATION CONFIRMED:';
        RAISE NOTICE '  Paper formula fails minimality on ALL % Case B examples', case_b;
        RAISE NOTICE '  Corrected formula passes uniqueness + minimality on ALL % examples', corr_min_pass;
    ELSE
        RAISE NOTICE '⚠ UNEXPECTED RESULTS — review details below';
    END IF;
END $$;

-- Detailed results: Case B failures
\echo ''
\echo '── Case B: Paper formula minimality failures ──'
SELECT example_id, description, result_rows,
       paper_grain, paper_removable,
       corrected_grain
FROM revalidation.test_results
WHERE case_type = 'B' AND result_rows > 0
ORDER BY example_id;

-- Detailed results: any unexpected failures
\echo ''
\echo '── Any unexpected results (errors, Case A minimality failures, etc.) ──'
SELECT example_id, category, case_type, description, result_rows,
       paper_grain, paper_unique, paper_minimal, paper_removable,
       corrected_grain, corrected_unique, corrected_minimal
FROM revalidation.test_results
WHERE result_rows <= 0
   OR (case_type = 'A' AND (paper_minimal = FALSE OR corrected_minimal = FALSE))
   OR corrected_unique = FALSE
   OR corrected_minimal = FALSE
ORDER BY example_id;

\echo ''
\echo '========================================================'
\echo 'Revalidation Complete'
\echo '========================================================'

