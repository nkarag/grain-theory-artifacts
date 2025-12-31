-- Generate and execute 85 additional examples covering all equi-join cases
-- Examples 16-100 (keeping first 15 separate for paper examples)

SET search_path TO experiments, public;

\echo '========================================'
\echo 'Generating 85 Additional Examples'
\echo '========================================'

-- Main Theorem Additional Examples (16-30: 15 examples)
\echo 'Main Theorem Additional Examples (16-30)...'

DO $$
DECLARE
    i INTEGER;
    total_rows BIGINT;
    unique_rows BIGINT;
    success_count INTEGER := 0;
BEGIN
    FOR i IN 16..30 LOOP
        BEGIN
            -- Case A examples (16-22)
            IF i <= 22 THEN
                EXECUTE format('DROP TABLE IF EXISTS r1_mt%s, r2_mt%s, result_mt%s CASCADE', i, i, i);
                EXECUTE format('CREATE TABLE r1_mt%s (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b))', i);
                EXECUTE format('CREATE TABLE r2_mt%s (a INTEGER, b INTEGER, d INTEGER, PRIMARY KEY (a, b, d))', i);
                EXECUTE format('INSERT INTO r1_mt%s SELECT ((row_number() OVER () - 1) / 20 + 1)::int, ((row_number() OVER () - 1) %% 20 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('INSERT INTO r2_mt%s SELECT ((row_number() OVER () - 1) / 20 + 1)::int, ((row_number() OVER () - 1) %% 20 + 1)::int, ((row_number() OVER () - 1) %% 10 + 1)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('CREATE TABLE result_mt%s (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b, d))', i);
                EXECUTE format('INSERT INTO result_mt%s SELECT DISTINCT r1.a, r1.b, r1.c, r2.d FROM r1_mt%s r1 INNER JOIN r2_mt%s r2 ON r1.a = r2.a AND r1.b = r2.b', i, i, i);
                -- Verification will be done separately
            -- Case B examples (23-30)
            ELSE
                EXECUTE format('DROP TABLE IF EXISTS r1_mt%s, r2_mt%s, result_mt%s CASCADE', i, i, i);
                EXECUTE format('CREATE TABLE r1_mt%s (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, c))', i);
                EXECUTE format('CREATE TABLE r2_mt%s (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (b, c))', i);
                EXECUTE format('INSERT INTO r1_mt%s SELECT ((row_number() OVER () - 1) / 10 + 1)::int, (random() * 50 + 1)::int, ((row_number() OVER () - 1) %% 10 + 1)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('INSERT INTO r2_mt%s SELECT (random() * 100 + 1)::int, ((row_number() OVER () - 1) / 10 + 1)::int, ((row_number() OVER () - 1) %% 10 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('CREATE TABLE result_mt%s (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b, c))', i);
                EXECUTE format('INSERT INTO result_mt%s SELECT DISTINCT r1.a, r1.b, r1.c, r2.d FROM r1_mt%s r1 INNER JOIN r2_mt%s r2 ON r1.a = r2.a AND r1.b = r2.b AND r1.c = r2.c', i, i, i);
                -- Verification will be done separately
            END IF;
            
            EXECUTE format('SELECT COUNT(*) FROM result_mt%s', i) INTO total_rows;
            IF i <= 22 THEN
                EXECUTE format('SELECT COUNT(DISTINCT (a, b, d)) FROM result_mt%s', i) INTO unique_rows;
            ELSE
                EXECUTE format('SELECT COUNT(DISTINCT (a, b, c)) FROM result_mt%s', i) INTO unique_rows;
            END IF;
            
            IF total_rows = unique_rows THEN
                success_count := success_count + 1;
            END IF;
            
            RAISE NOTICE 'Main Theorem Example %: Total=% Unique=% Match=%', i, total_rows, unique_rows, (total_rows = unique_rows);
        EXCEPTION WHEN OTHERS THEN
            RAISE NOTICE 'Main Theorem Example %: ERROR - %', i, SQLERRM;
        END;
    END LOOP;
    RAISE NOTICE 'Main Theorem Additional: %/% successful', success_count, 15;
END $$;

-- Equal Grains Additional Examples (31-50: 20 examples)
\echo 'Equal Grains Additional Examples (31-50)...'

DO $$
DECLARE
    i INTEGER;
    total_rows BIGINT;
    unique_rows BIGINT;
    success_count INTEGER := 0;
BEGIN
    FOR i IN 31..50 LOOP
        BEGIN
            EXECUTE format('DROP TABLE IF EXISTS r1_eg%s, r2_eg%s, result_eg%s CASCADE', i, i, i);
            
            -- Vary grain sizes: 1 field (31-35), 2 fields (36-42), 3 fields (43-47), 4 fields (48-50)
            IF i <= 35 THEN
                EXECUTE format('CREATE TABLE r1_eg%s (id INTEGER PRIMARY KEY, val1 INTEGER)', i);
                EXECUTE format('CREATE TABLE r2_eg%s (id INTEGER PRIMARY KEY, val2 INTEGER)', i);
                EXECUTE format('INSERT INTO r1_eg%s SELECT generate_series(1, 1000), (random() * 100)::int', i);
                EXECUTE format('INSERT INTO r2_eg%s SELECT generate_series(1, %s), (random() * 100)::int', i, 500 + (i-31)*50);
                EXECUTE format('CREATE TABLE result_eg%s (id INTEGER PRIMARY KEY, val1 INTEGER, val2 INTEGER)', i);
                EXECUTE format('INSERT INTO result_eg%s SELECT r1.id, r1.val1, r2.val2 FROM r1_eg%s r1 INNER JOIN r2_eg%s r2 ON r1.id = r2.id', i, i, i);
                -- Verification will be done separately
            ELSIF i <= 42 THEN
                EXECUTE format('CREATE TABLE r1_eg%s (id1 INTEGER, id2 INTEGER, val1 INTEGER, PRIMARY KEY (id1, id2))', i);
                EXECUTE format('CREATE TABLE r2_eg%s (id1 INTEGER, id2 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2))', i);
                -- Generate unique 2-field grain combinations
                EXECUTE format('INSERT INTO r1_eg%s SELECT id1, id2, (random() * 100)::int FROM (SELECT generate_series(1, 50) as id1) a CROSS JOIN (SELECT generate_series(1, 20) as id2) b LIMIT 1000', i);
                EXECUTE format('INSERT INTO r2_eg%s SELECT id1, id2, (random() * 100)::int FROM (SELECT generate_series(1, 50) as id1) a CROSS JOIN (SELECT generate_series(1, 20) as id2) b LIMIT 1000', i);
                -- When joining on id1 only, grain should be (id1, id2_r1, id2_r2) since id2 can differ
                EXECUTE format('CREATE TABLE result_eg%s (id1 INTEGER, id2_r1 INTEGER, id2_r2 INTEGER, val1 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2_r1, id2_r2))', i);
                EXECUTE format('INSERT INTO result_eg%s SELECT DISTINCT r1.id1, r1.id2 as id2_r1, r2.id2 as id2_r2, r1.val1, r2.val2 FROM r1_eg%s r1 INNER JOIN r2_eg%s r2 ON r1.id1 = r2.id1', i, i, i);
                -- Verification will be done separately
            ELSIF i <= 47 THEN
                EXECUTE format('CREATE TABLE r1_eg%s (id1 INTEGER, id2 INTEGER, id3 INTEGER, val1 INTEGER, PRIMARY KEY (id1, id2, id3))', i);
                EXECUTE format('CREATE TABLE r2_eg%s (id1 INTEGER, id2 INTEGER, id3 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2, id3))', i);
                -- Generate unique 3-field grain combinations
                EXECUTE format('INSERT INTO r1_eg%s SELECT id1, id2, id3, (random() * 100)::int FROM (SELECT generate_series(1, 10) as id1) a CROSS JOIN (SELECT generate_series(1, 10) as id2) b CROSS JOIN (SELECT generate_series(1, 10) as id3) c LIMIT 1000', i);
                EXECUTE format('INSERT INTO r2_eg%s SELECT id1, id2, id3, (random() * 100)::int FROM (SELECT generate_series(1, 10) as id1) a CROSS JOIN (SELECT generate_series(1, 10) as id2) b CROSS JOIN (SELECT generate_series(1, 10) as id3) c LIMIT 1000', i);
                -- When joining on (id1, id2) only, grain should be (id1, id2, id3_r1, id3_r2)
                EXECUTE format('CREATE TABLE result_eg%s (id1 INTEGER, id2 INTEGER, id3_r1 INTEGER, id3_r2 INTEGER, val1 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2, id3_r1, id3_r2))', i);
                EXECUTE format('INSERT INTO result_eg%s SELECT DISTINCT r1.id1, r1.id2, r1.id3 as id3_r1, r2.id3 as id3_r2, r1.val1, r2.val2 FROM r1_eg%s r1 INNER JOIN r2_eg%s r2 ON r1.id1 = r2.id1 AND r1.id2 = r2.id2', i, i, i);
                -- Verification will be done separately
            ELSE
                EXECUTE format('CREATE TABLE r1_eg%s (id1 INTEGER, id2 INTEGER, id3 INTEGER, id4 INTEGER, val1 INTEGER, PRIMARY KEY (id1, id2, id3, id4))', i);
                EXECUTE format('CREATE TABLE r2_eg%s (id1 INTEGER, id2 INTEGER, id3 INTEGER, id4 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2, id3, id4))', i);
                -- Generate unique 4-field grain combinations
                EXECUTE format('INSERT INTO r1_eg%s SELECT id1, id2, id3, id4, (random() * 100)::int FROM (SELECT generate_series(1, 5) as id1) a CROSS JOIN (SELECT generate_series(1, 10) as id2) b CROSS JOIN (SELECT generate_series(1, 10) as id3) c CROSS JOIN (SELECT generate_series(1, 2) as id4) d LIMIT 1000', i);
                EXECUTE format('INSERT INTO r2_eg%s SELECT id1, id2, id3, id4, (random() * 100)::int FROM (SELECT generate_series(1, 5) as id1) a CROSS JOIN (SELECT generate_series(1, 10) as id2) b CROSS JOIN (SELECT generate_series(1, 10) as id3) c CROSS JOIN (SELECT generate_series(1, 2) as id4) d LIMIT 1000', i);
                -- When joining on (id1, id2) only, grain should include id3 and id4 from both sides
                EXECUTE format('CREATE TABLE result_eg%s (id1 INTEGER, id2 INTEGER, id3_r1 INTEGER, id3_r2 INTEGER, id4_r1 INTEGER, id4_r2 INTEGER, val1 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2, id3_r1, id3_r2, id4_r1, id4_r2))', i);
                EXECUTE format('INSERT INTO result_eg%s SELECT DISTINCT r1.id1, r1.id2, r1.id3 as id3_r1, r2.id3 as id3_r2, r1.id4 as id4_r1, r2.id4 as id4_r2, r1.val1, r2.val2 FROM r1_eg%s r1 INNER JOIN r2_eg%s r2 ON r1.id1 = r2.id1 AND r1.id2 = r2.id2', i, i, i);
                -- Verification will be done separately
            END IF;
            
            EXECUTE format('SELECT COUNT(*) FROM result_eg%s', i) INTO total_rows;
            IF i <= 35 THEN
                EXECUTE format('SELECT COUNT(DISTINCT id) FROM result_eg%s', i) INTO unique_rows;
            ELSIF i <= 42 THEN
                EXECUTE format('SELECT COUNT(DISTINCT (id1, id2_r1, id2_r2)) FROM result_eg%s', i) INTO unique_rows;
            ELSIF i <= 47 THEN
                EXECUTE format('SELECT COUNT(DISTINCT (id1, id2, id3_r1, id3_r2)) FROM result_eg%s', i) INTO unique_rows;
            ELSE
                -- For 4-field grains joining on (id1, id2), grain includes id3 and id4 from both sides
                EXECUTE format('SELECT COUNT(DISTINCT (id1, id2, id3_r1, id3_r2, id4_r1, id4_r2)) FROM result_eg%s', i) INTO unique_rows;
            END IF;
            
            IF total_rows = unique_rows THEN
                success_count := success_count + 1;
            END IF;
            
            RAISE NOTICE 'Equal Grains Example %: Total=% Unique=% Match=%', i, total_rows, unique_rows, (total_rows = unique_rows);
        EXCEPTION WHEN OTHERS THEN
            RAISE NOTICE 'Equal Grains Example %: ERROR - %', i, SQLERRM;
        END;
    END LOOP;
    RAISE NOTICE 'Equal Grains Additional: %/% successful', success_count, 20;
END $$;

-- Ordered Grains Additional Examples (51-70: 20 examples)
\echo 'Ordered Grains Additional Examples (51-70)...'

DO $$
DECLARE
    i INTEGER;
    total_rows BIGINT;
    unique_rows BIGINT;
    success_count INTEGER := 0;
BEGIN
    FOR i IN 51..70 LOOP
        BEGIN
            EXECUTE format('DROP TABLE IF EXISTS r1_og%s, r2_og%s, result_og%s CASCADE', i, i, i);
            
            -- Vary the ordering relationships and join key positions
            IF i <= 60 THEN
                -- R1 finer grain, R2 coarser grain
                EXECUTE format('CREATE TABLE r1_og%s (id1 INTEGER, id2 INTEGER, val1 INTEGER, PRIMARY KEY (id1, id2))', i);
                EXECUTE format('CREATE TABLE r2_og%s (id1 INTEGER, val2 INTEGER, PRIMARY KEY (id1))', i);
                EXECUTE format('INSERT INTO r1_og%s SELECT ((row_number() OVER () - 1) / 10 + 1)::int, ((row_number() OVER () - 1) %% 10 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('INSERT INTO r2_og%s SELECT generate_series(1, 1000), (random() * 100)::int', i);
                EXECUTE format('CREATE TABLE result_og%s (id1 INTEGER, id2 INTEGER, val1 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2))', i);
                EXECUTE format('INSERT INTO result_og%s SELECT DISTINCT r1.id1, r1.id2, r1.val1, r2.val2 FROM r1_og%s r1 INNER JOIN r2_og%s r2 ON r1.id1 = r2.id1', i, i, i);
                EXECUTE format('SELECT COUNT(*) FROM result_og%s', i) INTO total_rows;
                EXECUTE format('SELECT COUNT(DISTINCT (id1, id2)) FROM result_og%s', i) INTO unique_rows;
            ELSE
                -- R1 coarser grain, R2 finer grain (reverse ordering)
                EXECUTE format('CREATE TABLE r1_og%s (id1 INTEGER, val1 INTEGER, PRIMARY KEY (id1))', i);
                EXECUTE format('CREATE TABLE r2_og%s (id1 INTEGER, id2 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2))', i);
                EXECUTE format('INSERT INTO r1_og%s SELECT generate_series(1, 1000), (random() * 100)::int', i);
                EXECUTE format('INSERT INTO r2_og%s SELECT ((row_number() OVER () - 1) / 10 + 1)::int, ((row_number() OVER () - 1) %% 10 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('CREATE TABLE result_og%s (id1 INTEGER, id2 INTEGER, val1 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2))', i);
                EXECUTE format('INSERT INTO result_og%s SELECT DISTINCT r1.id1, r2.id2, r1.val1, r2.val2 FROM r1_og%s r1 INNER JOIN r2_og%s r2 ON r1.id1 = r2.id1', i, i, i);
                EXECUTE format('SELECT COUNT(*) FROM result_og%s', i) INTO total_rows;
                EXECUTE format('SELECT COUNT(DISTINCT (id1, id2)) FROM result_og%s', i) INTO unique_rows;
            END IF;
            
            IF total_rows = unique_rows THEN
                success_count := success_count + 1;
            END IF;
            
            RAISE NOTICE 'Ordered Grains Example %: Total=% Unique=% Match=%', i, total_rows, unique_rows, (total_rows = unique_rows);
        EXCEPTION WHEN OTHERS THEN
            RAISE NOTICE 'Ordered Grains Example %: ERROR - %', i, SQLERRM;
        END;
    END LOOP;
    RAISE NOTICE 'Ordered Grains Additional: %/% successful', success_count, 20;
END $$;

-- Incomparable Grains Additional Examples (71-85: 15 examples)
\echo 'Incomparable Grains Additional Examples (71-85)...'

DO $$
DECLARE
    i INTEGER;
    total_rows BIGINT;
    unique_rows BIGINT;
    success_count INTEGER := 0;
BEGIN
    FOR i IN 71..85 LOOP
        BEGIN
            EXECUTE format('DROP TABLE IF EXISTS r1_ig%s, r2_ig%s, result_ig%s CASCADE', i, i, i);
            
            -- Case A: Comparable Jk-portions (71-77)
            IF i <= 77 THEN
                EXECUTE format('CREATE TABLE r1_ig%s (a INTEGER, b INTEGER, c INTEGER, val1 INTEGER, PRIMARY KEY (a, b, c))', i);
                EXECUTE format('CREATE TABLE r2_ig%s (a INTEGER, b INTEGER, d INTEGER, val2 INTEGER, PRIMARY KEY (a, b, d))', i);
                EXECUTE format('INSERT INTO r1_ig%s SELECT ((row_number() OVER () - 1) / 50 + 1)::int, ((row_number() OVER () - 1) / 5 %% 10 + 1)::int, ((row_number() OVER () - 1) %% 5 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('INSERT INTO r2_ig%s SELECT ((row_number() OVER () - 1) / 50 + 1)::int, ((row_number() OVER () - 1) / 5 %% 10 + 1)::int, ((row_number() OVER () - 1) %% 5 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('CREATE TABLE result_ig%s (a INTEGER, b INTEGER, c INTEGER, d INTEGER, val1 INTEGER, val2 INTEGER, PRIMARY KEY (a, b, c, d))', i);
                EXECUTE format('INSERT INTO result_ig%s SELECT DISTINCT r1.a, r1.b, r1.c, r2.d, r1.val1, r2.val2 FROM r1_ig%s r1 INNER JOIN r2_ig%s r2 ON r1.a = r2.a AND r1.b = r2.b', i, i, i);
                EXECUTE format('SELECT COUNT(*) FROM result_ig%s', i) INTO total_rows;
                EXECUTE format('SELECT COUNT(DISTINCT (a, b, c, d)) FROM result_ig%s', i) INTO unique_rows;
            -- Case B: Incomparable Jk-portions (78-85)
            ELSE
                EXECUTE format('CREATE TABLE r1_ig%s (a INTEGER, b INTEGER, c INTEGER, val1 INTEGER, PRIMARY KEY (a, c))', i);
                EXECUTE format('CREATE TABLE r2_ig%s (a INTEGER, b INTEGER, d INTEGER, val2 INTEGER, PRIMARY KEY (b, d))', i);
                EXECUTE format('INSERT INTO r1_ig%s SELECT ((row_number() OVER () - 1) / 10 + 1)::int, (random() * 50 + 1)::int, ((row_number() OVER () - 1) %% 10 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('INSERT INTO r2_ig%s SELECT (random() * 100 + 1)::int, ((row_number() OVER () - 1) / 10 + 1)::int, ((row_number() OVER () - 1) %% 10 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('CREATE TABLE result_ig%s (a INTEGER, b INTEGER, c INTEGER, d INTEGER, val1 INTEGER, val2 INTEGER, PRIMARY KEY (a, b, c, d))', i);
                EXECUTE format('INSERT INTO result_ig%s SELECT DISTINCT r1.a, r1.b, r1.c, r2.d, r1.val1, r2.val2 FROM r1_ig%s r1 INNER JOIN r2_ig%s r2 ON r1.a = r2.a AND r1.b = r2.b', i, i, i);
                EXECUTE format('SELECT COUNT(*) FROM result_ig%s', i) INTO total_rows;
                EXECUTE format('SELECT COUNT(DISTINCT (a, b, c, d)) FROM result_ig%s', i) INTO unique_rows;
            END IF;
            
            IF total_rows = unique_rows THEN
                success_count := success_count + 1;
            END IF;
            
            RAISE NOTICE 'Incomparable Grains Example %: Total=% Unique=% Match=%', i, total_rows, unique_rows, (total_rows = unique_rows);
        EXCEPTION WHEN OTHERS THEN
            RAISE NOTICE 'Incomparable Grains Example %: ERROR - %', i, SQLERRM;
        END;
    END LOOP;
    RAISE NOTICE 'Incomparable Grains Additional: %/% successful', success_count, 15;
END $$;

-- Natural Join Additional Examples (86-100: 15 examples)
\echo 'Natural Join Additional Examples (86-100)...'

DO $$
DECLARE
    i INTEGER;
    total_rows BIGINT;
    unique_rows BIGINT;
    success_count INTEGER := 0;
BEGIN
    FOR i IN 86..100 LOOP
        BEGIN
            EXECUTE format('DROP TABLE IF EXISTS r1_nj%s, r2_nj%s, result_nj%s CASCADE', i, i, i);
            
            -- Case A: Comparable Jk-portions (86-92)
            IF i <= 92 THEN
                EXECUTE format('CREATE TABLE r1_nj%s (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b))', i);
                EXECUTE format('CREATE TABLE r2_nj%s (a INTEGER, b INTEGER, d INTEGER, PRIMARY KEY (a, b))', i);
                EXECUTE format('INSERT INTO r1_nj%s SELECT ((row_number() OVER () - 1) / 20 + 1)::int, ((row_number() OVER () - 1) %% 20 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('INSERT INTO r2_nj%s SELECT ((row_number() OVER () - 1) / 20 + 1)::int, ((row_number() OVER () - 1) %% 20 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
                EXECUTE format('CREATE TABLE result_nj%s (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b))', i);
                EXECUTE format('INSERT INTO result_nj%s SELECT DISTINCT r1.a, r1.b, r1.c, r2.d FROM r1_nj%s r1 INNER JOIN r2_nj%s r2 ON r1.a = r2.a AND r1.b = r2.b', i, i, i);
                EXECUTE format('SELECT COUNT(*) FROM result_nj%s', i) INTO total_rows;
                EXECUTE format('SELECT COUNT(DISTINCT (a, b)) FROM result_nj%s', i) INTO unique_rows;
            -- Case B: Incomparable Jk-portions (93-100)
            ELSE
                EXECUTE format('CREATE TABLE r1_nj%s (a INTEGER, b INTEGER, c INTEGER, PRIMARY KEY (a, b))', i);
                EXECUTE format('CREATE TABLE r2_nj%s (b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (c, d))', i);
                -- Generate unique (a, b) pairs for r1
                EXECUTE format('INSERT INTO r1_nj%s SELECT a, b, (random() * 100)::int FROM (SELECT generate_series(1, 50) as a) a CROSS JOIN (SELECT generate_series(1, 20) as b) b LIMIT 1000', i);
                -- Generate unique (c, d) pairs for r2  
                EXECUTE format('INSERT INTO r2_nj%s SELECT (random() * 20 + 1)::int, c, d FROM (SELECT generate_series(1, 50) as c) c CROSS JOIN (SELECT generate_series(1, 20) as d) d LIMIT 1000', i);
                EXECUTE format('CREATE TABLE result_nj%s (a INTEGER, b INTEGER, c INTEGER, d INTEGER, PRIMARY KEY (a, b, c, d))', i);
                EXECUTE format('INSERT INTO result_nj%s SELECT DISTINCT r1.a, r1.b, r1.c, r2.d FROM r1_nj%s r1 INNER JOIN r2_nj%s r2 ON r1.b = r2.b AND r1.c = r2.c', i, i, i);
                EXECUTE format('SELECT COUNT(*) FROM result_nj%s', i) INTO total_rows;
                EXECUTE format('SELECT COUNT(DISTINCT (a, b, c, d)) FROM result_nj%s', i) INTO unique_rows;
            END IF;
            
            IF total_rows = unique_rows THEN
                success_count := success_count + 1;
            END IF;
            
            RAISE NOTICE 'Natural Join Example %: Total=% Unique=% Match=%', i, total_rows, unique_rows, (total_rows = unique_rows);
        EXCEPTION WHEN OTHERS THEN
            RAISE NOTICE 'Natural Join Example %: ERROR - %', i, SQLERRM;
        END;
    END LOOP;
    RAISE NOTICE 'Natural Join Additional: %/% successful', success_count, 15;
END $$;

\echo '========================================'
\echo '85 Additional Examples Generation Completed'
\echo '========================================';

