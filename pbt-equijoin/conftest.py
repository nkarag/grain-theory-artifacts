"""
Pytest fixtures for equi-join grain inference PBT.

Provides a PostgreSQL connection with a dedicated schema that is
created at session start and dropped at session end.
"""

import pytest
import psycopg2

from sql_runner import SCHEMA


@pytest.fixture(scope="session")
def pg_conn():
    """Session-scoped PostgreSQL connection.

    Creates the pbt_equijoin schema on startup, drops it on teardown.
    Connects to the local 'postgres' database.
    """
    conn = psycopg2.connect(dbname="postgres")
    conn.autocommit = False

    # Setup: create schema
    with conn.cursor() as cur:
        cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        cur.execute(f"CREATE SCHEMA {SCHEMA}")
    conn.commit()

    yield conn

    # Teardown: drop schema
    try:
        with conn.cursor() as cur:
            cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        conn.commit()
    finally:
        conn.close()


@pytest.fixture
def db(pg_conn):
    """Per-test fixture that provides a connection and cleans up after each test.

    Rolls back any uncommitted changes after each test to keep the schema clean.
    """
    yield pg_conn
    pg_conn.rollback()
