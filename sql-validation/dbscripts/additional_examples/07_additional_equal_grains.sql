-- Additional Equal Grains Examples (Examples 16-35)
-- Covering various grain sizes, join key positions, and data distributions

SET search_path TO experiments, public;

-- Examples 16-20: Single field grains with different join key relationships
DO $$
DECLARE
    i INTEGER;
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    FOR i IN 16..20 LOOP
        -- Create tables
        EXECUTE format('DROP TABLE IF EXISTS r1_eq%d CASCADE', i);
        EXECUTE format('CREATE TABLE r1_eq%d (id INTEGER PRIMARY KEY, val1 INTEGER, val2 INTEGER)', i);
        
        EXECUTE format('DROP TABLE IF EXISTS r2_eq%d CASCADE', i);
        EXECUTE format('CREATE TABLE r2_eq%d (id INTEGER PRIMARY KEY, val3 INTEGER, val4 INTEGER)', i);
        
        -- Insert data
        EXECUTE format('INSERT INTO r1_eq%d (id, val1, val2) SELECT generate_series(1, 1000), (random() * 100)::int, (random() * 100)::int', i);
        EXECUTE format('INSERT INTO r2_eq%d (id, val3, val4) SELECT generate_series(1, %d), (random() * 100)::int, (random() * 100)::int', i, 500 + (i-16)*100);
        
        -- Create result table
        EXECUTE format('DROP TABLE IF EXISTS result_eq%d CASCADE', i);
        EXECUTE format('CREATE TABLE result_eq%d (id INTEGER PRIMARY KEY, val1 INTEGER, val2 INTEGER, val3 INTEGER, val4 INTEGER)', i);
        
        -- Join
        EXECUTE format('INSERT INTO result_eq%d SELECT r1.id, r1.val1, r1.val2, r2.val3, r2.val4 FROM r1_eq%d r1 INNER JOIN r2_eq%d r2 ON r1.id = r2.id', i, i, i);
        
        -- Verify
        EXECUTE format('SELECT COUNT(*), COUNT(DISTINCT id) INTO %I, %I FROM result_eq%d', 'total_rows', 'unique_rows', i);
        EXECUTE format('SELECT COUNT(*) FROM result_eq%d', i) INTO total_rows;
        EXECUTE format('SELECT COUNT(DISTINCT id) FROM result_eq%d', i) INTO unique_rows;
        RAISE NOTICE 'Equal Grains Example %: Total=% Unique=% Match=%', i, total_rows, unique_rows, (total_rows = unique_rows);
    END LOOP;
END $$;

-- Examples 21-25: Two-field grains with join on first field
DO $$
DECLARE
    i INTEGER;
    total_rows BIGINT;
    unique_rows BIGINT;
BEGIN
    FOR i IN 21..25 LOOP
        EXECUTE format('DROP TABLE IF EXISTS r1_eq%d CASCADE', i);
        EXECUTE format('CREATE TABLE r1_eq%d (id1 INTEGER, id2 INTEGER, val1 INTEGER, PRIMARY KEY (id1, id2))', i);
        
        EXECUTE format('DROP TABLE IF EXISTS r2_eq%d CASCADE', i);
        EXECUTE format('CREATE TABLE r2_eq%d (id1 INTEGER, id2 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2))', i);
        
        EXECUTE format('INSERT INTO r1_eq%d (id1, id2, val1) SELECT ((row_number() OVER () - 1) / 20 + 1)::int, ((row_number() OVER () - 1) %% 20 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
        EXECUTE format('INSERT INTO r2_eq%d (id1, id2, val2) SELECT ((row_number() OVER () - 1) / 20 + 1)::int, ((row_number() OVER () - 1) %% 20 + 1)::int, (random() * 100)::int FROM generate_series(1, 1000)', i);
        
        EXECUTE format('DROP TABLE IF EXISTS result_eq%d CASCADE', i);
        EXECUTE format('CREATE TABLE result_eq%d (id1 INTEGER, id2 INTEGER, val1 INTEGER, val2 INTEGER, PRIMARY KEY (id1, id2))', i);
        
        EXECUTE format('INSERT INTO result_eq%d SELECT r1.id1, r1.id2, r1.val1, r2.val2 FROM r1_eq%d r1 INNER JOIN r2_eq%d r2 ON r1.id1 = r2.id1', i, i, i);
        
        EXECUTE format('SELECT COUNT(*) FROM result_eq%d', i) INTO total_rows;
        EXECUTE format('SELECT COUNT(DISTINCT (id1, id2)) FROM result_eq%d', i) INTO unique_rows;
        RAISE NOTICE 'Equal Grains Example %: Total=% Unique=% Match=%', i, total_rows, unique_rows, (total_rows = unique_rows);
    END LOOP;
END $$;

-- Continue with more systematic examples...
RAISE NOTICE 'Additional Equal Grains Examples 16-25 completed';







