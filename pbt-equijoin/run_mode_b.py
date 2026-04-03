"""
Mode B: Random property-based testing with 10,000 examples at larger sizes.

Runs a Hypothesis PBT campaign testing all 6 equi-join grain properties
on randomly generated configurations with max_jk=8, max_r_only=7.

Can be run as:
    python run_mode_b.py          # standalone script
    pytest run_mode_b.py -v       # via pytest

Results are saved to mode_b_results.json with full statistics.
"""

import json
import os
import sys
import threading
import time
from collections import Counter
from datetime import datetime

import psycopg2
from hypothesis import HealthCheck, given, settings

from config import Config, JkRelation
from generators import config_class_key, equijoin_config
from properties import (
    check_convention_smallest,
    check_size_relationship,
    run_all_properties,
)
from sql_runner import SCHEMA


# ---------------------------------------------------------------------------
# Global statistics tracking (thread-safe)
# ---------------------------------------------------------------------------

_stats_lock = threading.Lock()
_stats = {
    "total_examples": 0,
    "class_distribution": Counter(),
    "size_distribution": Counter(),  # total columns in config
    "property_results": {
        "P1_uniqueness": {"passed": 0, "failed": 0, "inconclusive": 0},
        "P2_minimality": {"passed": 0, "failed": 0, "inconclusive": 0},
        "P3_wrong_direction": {"passed": 0, "failed": 0, "inconclusive": 0},
        "P4_incomparable_both": {"passed": 0, "failed": 0, "inconclusive": 0},
        "P5_size_relationship": {"passed": 0, "failed": 0, "inconclusive": 0},
        "P6_convention_smallest": {"passed": 0, "failed": 0, "inconclusive": 0},
    },
    "failures": [],
}

_config_id_lock = threading.Lock()
_config_id_counter = 0


def _next_config_id() -> int:
    global _config_id_counter
    with _config_id_lock:
        _config_id_counter += 1
        return _config_id_counter


def _classify_result(msg: str) -> str:
    """Classify a property result message as passed/inconclusive."""
    if msg and "Inconclusive" in msg:
        return "inconclusive"
    if msg and "N/A" in msg:
        return "passed"  # N/A counts as passed (property not applicable)
    return "passed"


def _record_results(config: Config, results: dict):
    """Record results from a single config into global stats."""
    with _stats_lock:
        _stats["total_examples"] += 1

        # Class distribution
        key = config_class_key(config)
        class_label = (
            f"{key[0].value}"
            f"_g1rest{'E' if key[1] else 'NE'}"
            f"_g2rest{'E' if key[2] else 'NE'}"
        )
        _stats["class_distribution"][class_label] += 1

        # Size distribution
        total_cols = len(config.r1_fields) + len(config.r2_fields) - len(config.jk)
        _stats["size_distribution"][str(total_cols)] += 1

        # Property results
        for prop_name, (passed, msg) in results.items():
            if not passed:
                _stats["property_results"][prop_name]["failed"] += 1
                _stats["failures"].append({
                    "property": prop_name,
                    "message": msg,
                    "config": {
                        "r1_fields": list(config.r1_fields),
                        "r2_fields": list(config.r2_fields),
                        "jk": list(config.jk),
                        "g1": list(config.g1),
                        "g2": list(config.g2),
                        "jk_rel": config.jk_rel.value,
                    },
                })
            else:
                classification = _classify_result(msg)
                _stats["property_results"][prop_name][classification] += 1


# ---------------------------------------------------------------------------
# DB connection management
# ---------------------------------------------------------------------------

def _get_connection():
    """Create a PostgreSQL connection with the PBT schema."""
    conn = psycopg2.connect(dbname="postgres")
    conn.autocommit = False
    with conn.cursor() as cur:
        cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        cur.execute(f"CREATE SCHEMA {SCHEMA}")
    conn.commit()
    return conn


def _safe_rollback(conn):
    """Rollback without raising if connection is in a bad state."""
    try:
        conn.rollback()
    except Exception:
        pass


def _cleanup_connection(conn):
    """Drop schema and close connection."""
    try:
        _safe_rollback(conn)
        with conn.cursor() as cur:
            cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        conn.commit()
    except Exception:
        pass
    finally:
        try:
            conn.close()
        except Exception:
            pass


# ---------------------------------------------------------------------------
# Hypothesis test
# ---------------------------------------------------------------------------

# Module-level connection for Hypothesis (created on first use)
_conn = None


def _ensure_conn():
    global _conn
    if _conn is None:
        _conn = _get_connection()
    return _conn


MAX_EXAMPLES = 10000


def _run_one_config(config: Config, conn):
    """Run all 6 properties on a single config with proper error recovery.

    Returns the results dict, or raises on failure.
    """
    cid = _next_config_id()

    # Ensure clean transaction state before each config
    _safe_rollback(conn)

    try:
        results = run_all_properties(
            conn, config, n_rows=30, seed=42, config_id=cid,
        )
        return results
    except Exception:
        # If SQL failed mid-transaction, rollback so we can continue
        _safe_rollback(conn)
        # Re-setup schema (tables may be in inconsistent state)
        try:
            with conn.cursor() as cur:
                cur.execute(f"CREATE SCHEMA IF NOT EXISTS {SCHEMA}")
            conn.commit()
        except Exception:
            _safe_rollback(conn)
        raise


@given(config=equijoin_config(max_jk=8, max_r_only=7))
@settings(
    max_examples=MAX_EXAMPLES,
    deadline=None,
    suppress_health_check=[HealthCheck.too_slow, HealthCheck.function_scoped_fixture],
    database=None,  # Don't save Hypothesis database for this run
)
def test_mode_b_all_properties(config: Config):
    """Mode B: test all 6 properties on a random config at larger sizes."""
    conn = _ensure_conn()
    results = _run_one_config(config, conn)
    _record_results(config, results)

    # Assert all properties passed
    for prop_name, (passed, msg) in results.items():
        assert passed, f"{prop_name}: {msg}"


# ---------------------------------------------------------------------------
# Pytest support: provide db fixture for pytest runner
# ---------------------------------------------------------------------------

try:
    import pytest

    @pytest.fixture(scope="session")
    def pg_conn_mode_b():
        conn = _get_connection()
        yield conn
        _cleanup_connection(conn)
except ImportError:
    pass


# ---------------------------------------------------------------------------
# Standalone runner
# ---------------------------------------------------------------------------

def _print_summary(elapsed, test_passed):
    """Print formatted results summary."""
    print()
    print("=" * 70)
    print("RESULTS SUMMARY")
    print("=" * 70)
    print(f"  Total examples:  {_stats['total_examples']}")
    print(f"  Elapsed:         {elapsed:.1f}s")
    print(f"  Test passed:     {test_passed}")
    print()

    print("Property results:")
    for prop, counts in _stats["property_results"].items():
        p, f, i = counts["passed"], counts["failed"], counts["inconclusive"]
        status = "PASS" if f == 0 else "FAIL"
        print(
            f"  {prop:30s}  {status}  "
            f"passed={p}  failed={f}  inconclusive={i}"
        )
    print()

    n_total = max(1, _stats["total_examples"])
    print(f"Config class distribution ({len(_stats['class_distribution'])} classes):")
    for cls, count in sorted(_stats["class_distribution"].items()):
        pct = 100 * count / n_total
        print(f"  {cls:50s}  {count:6d}  ({pct:5.1f}%)")
    print()

    print("Size distribution:")
    for size, count in sorted(
        _stats["size_distribution"].items(), key=lambda x: int(x[0])
    ):
        pct = 100 * count / n_total
        print(f"  {size:3s} columns  {count:6d}  ({pct:5.1f}%)")
    print()


def run_standalone():
    """Run Mode B as a standalone script with progress reporting."""
    global _conn

    print("=" * 70)
    print("Mode B: Random PBT -- 10,000 examples at larger sizes")
    print(f"  max_jk=8, max_r_only=7")
    print(f"  Started: {datetime.now().isoformat()}")
    print("=" * 70)
    print()

    _conn = _get_connection()
    start_time = time.time()

    try:
        # Run the Hypothesis test
        test_mode_b_all_properties()
        test_passed = True
        error_msg = None
    except Exception as e:
        test_passed = False
        error_msg = str(e)
        if "VIOLATED" in str(e):
            print(f"\nPROPERTY VIOLATION DETECTED: {e}")
        else:
            print(f"\nERROR: {e}")
    finally:
        elapsed = time.time() - start_time
        _cleanup_connection(_conn)
        _conn = None

    # Build results dict
    results = {
        "mode": "B",
        "description": "Random PBT with 10,000 examples at larger sizes",
        "max_examples": MAX_EXAMPLES,
        "generator_params": {"max_jk": 8, "max_r_only": 7},
        "n_rows_per_config": 30,
        "started": datetime.now().isoformat(),
        "elapsed_seconds": round(elapsed, 2),
        "test_passed": test_passed,
        "error": error_msg,
        "total_examples_run": _stats["total_examples"],
        "class_distribution": dict(_stats["class_distribution"]),
        "size_distribution": dict(
            sorted(
                _stats["size_distribution"].items(),
                key=lambda x: int(x[0]),
            )
        ),
        "property_results": _stats["property_results"],
        "failures": _stats["failures"],
    }

    # Save results
    results_path = os.path.join(os.path.dirname(__file__) or ".", "mode_b_results.json")
    with open(results_path, "w") as f:
        json.dump(results, f, indent=2)

    # Print summary
    _print_summary(elapsed, test_passed)
    print(f"Results saved to: {results_path}")

    if not test_passed:
        print(f"\nFAILURES ({len(_stats['failures'])}):")
        for fail in _stats["failures"]:
            print(f"  {fail['property']}: {fail['message']}")
        return 1

    return 0


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    sys.exit(run_standalone())
