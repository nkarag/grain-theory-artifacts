"""
SQL execution helpers for equi-join grain inference PBT.

Handles table creation, data insertion, join execution,
and uniqueness/minimality checks against PostgreSQL.
"""

from typing import Dict, List, Tuple

from config import Config


SCHEMA = "pbt_equijoin"


def create_schema(conn):
    """Create the PBT schema (idempotent)."""
    with conn.cursor() as cur:
        cur.execute(f"CREATE SCHEMA IF NOT EXISTS {SCHEMA}")
    conn.commit()


def drop_schema(conn):
    """Drop the PBT schema and all its objects."""
    with conn.cursor() as cur:
        cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
    conn.commit()


def _table_name(prefix: str, config_id: int) -> str:
    return f"{SCHEMA}.{prefix}_{config_id}"


def _col_def(col: str) -> str:
    return f"{col} INTEGER NOT NULL"


def create_tables(
    conn,
    config: Config,
    r1_data: List[Dict[str, int]],
    r2_data: List[Dict[str, int]],
    config_id: int = 0,
) -> Tuple[str, str]:
    """Create and populate R1 and R2 tables.

    Returns (r1_table, r2_table) fully-qualified names.
    """
    r1_table = _table_name("r1", config_id)
    r2_table = _table_name("r2", config_id)

    with conn.cursor() as cur:
        # R1
        cols_def = ", ".join(_col_def(c) for c in config.r1_fields)
        cur.execute(f"DROP TABLE IF EXISTS {r1_table}")
        cur.execute(f"CREATE TABLE {r1_table} ({cols_def})")
        if r1_data:
            placeholders = ", ".join(["%s"] * len(config.r1_fields))
            insert_sql = f"INSERT INTO {r1_table} VALUES ({placeholders})"
            for row in r1_data:
                cur.execute(insert_sql, [row[c] for c in config.r1_fields])

        # R2
        cols_def = ", ".join(_col_def(c) for c in config.r2_fields)
        cur.execute(f"DROP TABLE IF EXISTS {r2_table}")
        cur.execute(f"CREATE TABLE {r2_table} ({cols_def})")
        if r2_data:
            placeholders = ", ".join(["%s"] * len(config.r2_fields))
            insert_sql = f"INSERT INTO {r2_table} VALUES ({placeholders})"
            for row in r2_data:
                cur.execute(insert_sql, [row[c] for c in config.r2_fields])

    conn.commit()
    return r1_table, r2_table


def execute_join(
    conn,
    config: Config,
    r1_table: str,
    r2_table: str,
    config_id: int = 0,
) -> str:
    """Execute the equi-join and materialize into a result table.

    Returns the fully-qualified result table name.
    """
    res_table = _table_name("res", config_id)

    # Build join condition
    join_conds = " AND ".join(
        f"r1.{col} = r2.{col}" for col in config.jk
    )

    # Build SELECT list: R1 non-Jk cols (prefixed), Jk cols, R2 non-Jk cols (prefixed)
    jk_set = set(config.jk)
    r1_only = [c for c in config.r1_fields if c not in jk_set]
    r2_only = [c for c in config.r2_fields if c not in jk_set]

    select_parts = []
    for c in r1_only:
        select_parts.append(f"r1.{c} AS {c}_r1")
    for c in config.jk:
        select_parts.append(f"r1.{c}")
    for c in r2_only:
        select_parts.append(f"r2.{c} AS {c}_r2")

    select_clause = ", ".join(select_parts) if select_parts else "*"

    with conn.cursor() as cur:
        cur.execute(f"DROP TABLE IF EXISTS {res_table}")
        cur.execute(
            f"CREATE TABLE {res_table} AS "
            f"SELECT {select_clause} "
            f"FROM {r1_table} r1 JOIN {r2_table} r2 ON {join_conds}"
        )
    conn.commit()
    return res_table


def _resolve_grain_cols(grain_cols: tuple, config: Config) -> List[str]:
    """Resolve grain column names to result table column names.

    Grain cols from R1-only get _r1 suffix, from R2-only get _r2 suffix,
    Jk cols keep their name.
    """
    jk_set = set(config.jk)
    r1_only_set = set(config.r1_fields) - jk_set
    r2_only_set = set(config.r2_fields) - jk_set

    resolved = []
    for c in grain_cols:
        if c in jk_set:
            resolved.append(c)
        elif c in r1_only_set:
            resolved.append(f"{c}_r1")
        elif c in r2_only_set:
            resolved.append(f"{c}_r2")
        else:
            # Column in both R1 and R2 non-Jk — shouldn't happen in valid config
            resolved.append(c)
    return resolved


def count_total(conn, table: str) -> int:
    """Return total row count."""
    with conn.cursor() as cur:
        cur.execute(f"SELECT COUNT(*) FROM {table}")
        return cur.fetchone()[0]


def count_distinct(conn, table: str, cols: List[str]) -> int:
    """Return COUNT(DISTINCT (cols)) on the table."""
    if not cols:
        return 1  # empty projection — all rows "equal"
    col_list = ", ".join(cols)
    with conn.cursor() as cur:
        cur.execute(f"SELECT COUNT(DISTINCT ({col_list})) FROM {table}")
        return cur.fetchone()[0]


def check_uniqueness(conn, table: str, grain_cols: List[str]) -> bool:
    """Check if grain_cols form a unique identifier (COUNT = COUNT DISTINCT)."""
    total = count_total(conn, table)
    if total == 0:
        return True  # vacuously true
    distinct = count_distinct(conn, table, grain_cols)
    return total == distinct


def check_minimality(conn, table: str, grain_cols: List[str]) -> bool:
    """Check if grain_cols are minimal: removing ANY single column breaks uniqueness.

    Returns True if the grain is minimal (irreducible).
    """
    total = count_total(conn, table)
    if total <= 1:
        return True  # trivially minimal
    if len(grain_cols) <= 1:
        return True  # single column — can't remove anything

    for i, col in enumerate(grain_cols):
        reduced = [c for j, c in enumerate(grain_cols) if j != i]
        distinct = count_distinct(conn, table, reduced)
        if distinct == total:
            # Column is removable — grain is NOT minimal
            return False
    return True


def find_removable_columns(conn, table: str, grain_cols: List[str]) -> List[str]:
    """Find which columns can be removed while preserving uniqueness."""
    total = count_total(conn, table)
    removable = []
    for i, col in enumerate(grain_cols):
        reduced = [c for j, c in enumerate(grain_cols) if j != i]
        if not reduced:
            continue
        distinct = count_distinct(conn, table, reduced)
        if distinct == total:
            removable.append(col)
    return removable


def cleanup_tables(conn, config_id: int = 0):
    """Drop all tables for a given config_id."""
    with conn.cursor() as cur:
        for prefix in ("r1", "r2", "res"):
            table = _table_name(prefix, config_id)
            cur.execute(f"DROP TABLE IF EXISTS {table}")
    conn.commit()
