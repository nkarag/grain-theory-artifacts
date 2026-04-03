"""
Hypothesis-based property tests for equi-join grain inference.

Tests the 6 core properties:
  P1 (Uniqueness):    Both F1 and F2 produce unique identifiers
  P2 (Minimality):    Convention grain is minimal (irreducible)
  P3 (Non-minimality): Wrong direction is non-minimal for comparable configs
  P4 (Both-minimal):  Both directions minimal for incomparable configs
  P5 (Size relation):  |F1| - |F2| = |G1^Jk| - |G2^Jk|
  P6 (Convention smallest): |convention_grain| <= min(|F1|, |F2|)

P1-P4 require a PostgreSQL connection (via db fixture from conftest.py).
P5-P6 are pure Python and run without a database.

Usage:
  pytest test_properties.py -v                    # smoke test (100 examples)
  pytest test_properties.py -k "P5 or P6" -v      # pure-Python only
  pytest test_properties.py -k "P1" -v             # uniqueness only
"""

import os
import threading

from hypothesis import given, settings, HealthCheck, assume
from hypothesis import strategies as st

from config import Config, JkRelation
from generators import equijoin_config, equijoin_config_comparable, equijoin_config_incomparable
from properties import (
    check_convention_smallest,
    check_incomparable_both_minimal,
    check_minimality_convention,
    check_size_relationship,
    check_uniqueness_both,
    check_wrong_direction_non_minimal,
    run_all_properties,
)
from sql_runner import (
    _resolve_grain_cols,
    cleanup_tables,
    count_total,
    create_tables,
    execute_join,
)
from data_gen import generate_data

# ---------------------------------------------------------------------------
# Config-id generator — thread-safe to avoid table name collisions
# ---------------------------------------------------------------------------

_config_id_lock = threading.Lock()
_config_id_counter = 0


def _next_config_id() -> int:
    global _config_id_counter
    with _config_id_lock:
        _config_id_counter += 1
        return _config_id_counter


# ---------------------------------------------------------------------------
# Helper: setup join and return (res_table, config_id)
# ---------------------------------------------------------------------------

def _setup(db, config: Config, n_rows: int = 30, seed: int = 42):
    """Generate data, create tables, execute join. Returns (res_table, config_id)."""
    cid = _next_config_id()
    r1_data, r2_data = generate_data(config, n_rows=n_rows, seed=seed)
    r1_table, r2_table = create_tables(db, config, r1_data, r2_data, config_id=cid)
    res_table = execute_join(db, config, r1_table, r2_table, config_id=cid)
    return res_table, cid


# ---------------------------------------------------------------------------
# Hypothesis settings
# ---------------------------------------------------------------------------

# Suppress the too_slow health check — SQL operations can be slow.
# Suppress function_scoped_fixture — we know db is safe with Hypothesis.
COMMON_SETTINGS = dict(
    max_examples=100,
    suppress_health_check=[HealthCheck.too_slow, HealthCheck.function_scoped_fixture],
    deadline=None,
)


# ===========================================================================
# P5 — Size relationship (pure Python)
# ===========================================================================

class TestP5SizeRelationship:
    """P5: |F1| - |F2| = |G1^Jk| - |G2^Jk|."""

    @given(config=equijoin_config(max_jk=6, max_r_only=4))
    @settings(**COMMON_SETTINGS)
    def test_size_relationship(self, config: Config):
        passed, msg = check_size_relationship(config)
        assert passed, msg


# ===========================================================================
# P6 — Convention grain is smallest (pure Python)
# ===========================================================================

class TestP6ConventionSmallest:
    """P6: |convention_grain| <= min(|F1|, |F2|)."""

    @given(config=equijoin_config(max_jk=6, max_r_only=4))
    @settings(**COMMON_SETTINGS)
    def test_convention_smallest(self, config: Config):
        passed, msg = check_convention_smallest(config)
        assert passed, msg


# ===========================================================================
# P1 — Uniqueness (SQL)
# ===========================================================================

class TestP1Uniqueness:
    """P1: Both F1 and F2 produce unique identifiers on the join result."""

    @given(config=equijoin_config(max_jk=4, max_r_only=3))
    @settings(**COMMON_SETTINGS)
    def test_uniqueness_both_directions(self, config: Config, db):
        cid = _next_config_id()
        try:
            r1_data, r2_data = generate_data(config, n_rows=30, seed=42)
            r1_table, r2_table = create_tables(db, config, r1_data, r2_data,
                                               config_id=cid)
            res_table = execute_join(db, config, r1_table, r2_table,
                                     config_id=cid)

            passed, msg = check_uniqueness_both(db, config, res_table)
            assert passed, msg
        finally:
            cleanup_tables(db, config_id=cid)


# ===========================================================================
# P2 — Minimality (SQL)
# ===========================================================================

class TestP2Minimality:
    """P2: The convention-compliant grain is minimal."""

    @given(
        config=equijoin_config(max_jk=4, max_r_only=3),
        seed=st.integers(min_value=0, max_value=999),
    )
    @settings(**COMMON_SETTINGS)
    def test_convention_grain_minimal(self, config: Config, seed: int, db):
        # Use extreme_low distribution for maximum Jk fan-out. This creates
        # many rows per Jk value, increasing collision coverage and making
        # minimality reliably testable.
        n_rows = 50
        cid = _next_config_id()
        try:
            r1_data, r2_data = generate_data(
                config, n_rows=n_rows, seed=seed,
                distribution="extreme_low",
            )
            r1_table, r2_table = create_tables(db, config, r1_data, r2_data,
                                               config_id=cid)
            res_table = execute_join(db, config, r1_table, r2_table,
                                     config_id=cid)

            total = count_total(db, res_table)
            if total <= 1:
                return  # can't test minimality on 0-1 rows

            passed, msg = check_minimality_convention(
                db, config, res_table,
                r1_table=r1_table, r2_table=r2_table,
            )
            assert passed, msg
        finally:
            cleanup_tables(db, config_id=cid)


# ===========================================================================
# P3 — Wrong direction non-minimality (SQL)
# ===========================================================================

class TestP3WrongDirectionNonMinimal:
    """P3: Wrong direction is NOT minimal for comparable, non-equal configs."""

    @given(
        config=equijoin_config(max_jk=4, max_r_only=3),
        seed=st.integers(min_value=0, max_value=999),
    )
    @settings(**COMMON_SETTINGS)
    def test_wrong_direction_not_minimal(self, config: Config, seed: int, db):
        # Only test for proper subset/superset
        assume(config.jk_rel in (JkRelation.PROPER_SUBSET,
                                  JkRelation.PROPER_SUPERSET))

        # Determine wrong-direction grain size — skip if single-column
        if config.jk_rel == JkRelation.PROPER_SUBSET:
            wrong_grain = config.f2
        else:
            wrong_grain = config.f1
        assume(len(wrong_grain) > 1)

        n_rows = 50
        cid = _next_config_id()
        try:
            r1_data, r2_data = generate_data(config, n_rows=n_rows, seed=seed)
            r1_table, r2_table = create_tables(db, config, r1_data, r2_data,
                                               config_id=cid)
            res_table = execute_join(db, config, r1_table, r2_table,
                                     config_id=cid)

            total = count_total(db, res_table)
            if total <= 1:
                return

            passed, msg = check_wrong_direction_non_minimal(
                db, config, res_table)
            assert passed, msg
        finally:
            cleanup_tables(db, config_id=cid)


# ===========================================================================
# P4 — Incomparable: both directions minimal (SQL)
# ===========================================================================

class TestP4IncomparableBothMinimal:
    """P4: When Jk-portions are incomparable, both F1 and F2 are minimal."""

    @given(
        config=equijoin_config(max_jk=4, max_r_only=3),
        seed=st.integers(min_value=0, max_value=999),
    )
    @settings(**COMMON_SETTINGS)
    def test_incomparable_both_minimal(self, config: Config, seed: int, db):
        assume(config.jk_rel == JkRelation.INCOMPARABLE)

        n_rows = 50
        cid = _next_config_id()
        try:
            r1_data, r2_data = generate_data(config, n_rows=n_rows, seed=seed)
            r1_table, r2_table = create_tables(db, config, r1_data, r2_data,
                                               config_id=cid)
            res_table = execute_join(db, config, r1_table, r2_table,
                                     config_id=cid)

            total = count_total(db, res_table)
            if total <= 1:
                return

            passed, msg = check_incomparable_both_minimal(
                db, config, res_table,
                r1_table=r1_table, r2_table=r2_table)
            assert passed, msg
        finally:
            cleanup_tables(db, config_id=cid)


# ===========================================================================
# Integrated: all 6 properties on a single config (smoke test)
# ===========================================================================

class TestAllProperties:
    """Smoke test: run all 6 properties together on random configs."""

    @given(config=equijoin_config(max_jk=4, max_r_only=3))
    @settings(max_examples=50,
              suppress_health_check=[HealthCheck.too_slow,
                                     HealthCheck.function_scoped_fixture],
              deadline=None)
    def test_all_properties(self, config: Config, db):
        cid = _next_config_id()
        results = run_all_properties(db, config, n_rows=30, seed=42,
                                     config_id=cid)
        for prop_name, (passed, msg) in results.items():
            assert passed, f"{prop_name}: {msg}"
