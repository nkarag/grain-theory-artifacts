#!/usr/bin/env python3
"""
Mode A: Exhaustive small-model checking for equi-join grain inference.

Enumerates ALL valid equi-join configurations with |Ri| <= max_type_size
(default 5), runs all 6 properties on each, and reports results by
configuration class (16 classes: 4 Jk relations x 2 G1_rest emptiness
x 2 G2_rest emptiness).

Any property violation (passed=False) is a CRITICAL finding and halts
execution immediately.

Usage:
    python run_mode_a.py [--max-type-size N] [--n-rows N]
"""

import argparse
import json
import os
import sys
import time
from collections import defaultdict
from dataclasses import asdict

import psycopg2

from config import JkRelation
from generators import all_configs_up_to, config_class_key, all_16_classes
from properties import run_all_properties
from sql_runner import SCHEMA


# ---------------------------------------------------------------------------
# Database connection
# ---------------------------------------------------------------------------

def get_connection():
    """Connect to PostgreSQL using DATABASE_URL or default (local 'postgres' db).

    Mirrors conftest.py: connects to the local 'postgres' database by default.
    The PBT schema provides isolation within that database.
    """
    dsn = os.environ.get("DATABASE_URL")
    if dsn:
        conn = psycopg2.connect(dsn)
    else:
        conn = psycopg2.connect(dbname="postgres")
    conn.autocommit = False
    return conn


def setup_schema(conn):
    """Create the PBT schema (idempotent)."""
    with conn.cursor() as cur:
        cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        cur.execute(f"CREATE SCHEMA {SCHEMA}")
    conn.commit()


def teardown_schema(conn):
    """Drop the PBT schema."""
    with conn.cursor() as cur:
        cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
    conn.commit()


# ---------------------------------------------------------------------------
# Result tracking
# ---------------------------------------------------------------------------

PROPERTY_NAMES = [
    "P1_uniqueness",
    "P2_minimality",
    "P3_wrong_direction",
    "P4_incomparable_both",
    "P5_size_relationship",
    "P6_convention_smallest",
]


def class_key_str(key):
    """Convert a class key tuple to a human-readable string."""
    jk_rel, g1e, g2e = key
    return f"{jk_rel.value}|g1e={g1e}|g2e={g2e}"


def config_summary(config):
    """Return a compact string description of a config."""
    return (
        f"R1={list(config.r1_fields)} R2={list(config.r2_fields)} "
        f"Jk={list(config.jk)} G1={list(config.g1)} G2={list(config.g2)} "
        f"jk_rel={config.jk_rel.value} "
        f"F1={list(config.f1)} F2={list(config.f2)} "
        f"conv={list(config.convention_grain)}"
    )


# ---------------------------------------------------------------------------
# Main execution
# ---------------------------------------------------------------------------

def run_mode_a(max_type_size=5, n_rows=10):
    """Run exhaustive verification over all configs up to max_type_size."""

    print(f"Mode A: Exhaustive small-model checking")
    print(f"  max_type_size = {max_type_size}")
    print(f"  n_rows        = {n_rows}")
    print()

    # Count configs first
    print("Counting configurations...", end=" ", flush=True)
    total_configs = sum(1 for _ in all_configs_up_to(max_type_size))
    print(f"{total_configs} configurations to check")
    print()

    # Connect to PostgreSQL
    conn = get_connection()
    setup_schema(conn)

    # Tracking
    class_stats = defaultdict(lambda: {
        "total": 0,
        "passed": defaultdict(int),
        "failed": defaultdict(int),
        "inconclusive": defaultdict(int),
    })
    overall_passed = 0
    overall_failed = 0
    overall_inconclusive = 0
    violation_found = False
    violation_details = None

    start_time = time.time()
    progress_interval = max(1, total_configs // 20)  # Print progress ~20 times

    try:
        for i, config in enumerate(all_configs_up_to(max_type_size)):
            # Progress reporting
            if i % progress_interval == 0 or i == total_configs - 1:
                elapsed = time.time() - start_time
                rate = (i + 1) / elapsed if elapsed > 0 else 0
                eta = (total_configs - i - 1) / rate if rate > 0 else 0
                print(
                    f"\r  [{i+1:>{len(str(total_configs))}}/{total_configs}] "
                    f"{100*(i+1)/total_configs:5.1f}%  "
                    f"{rate:.1f} cfg/s  "
                    f"ETA {eta:.0f}s  "
                    f"passed={overall_passed} inconc={overall_inconclusive} "
                    f"FAILED={overall_failed}",
                    end="", flush=True,
                )

            # Run all properties
            results = run_all_properties(
                conn, config, n_rows=n_rows, seed=42, config_id=i % 1000
            )

            # Classify results
            key = config_class_key(config)
            stats = class_stats[key]
            stats["total"] += 1

            for prop_name in PROPERTY_NAMES:
                passed, message = results[prop_name]
                if not passed:
                    # CRITICAL VIOLATION
                    stats["failed"][prop_name] += 1
                    overall_failed += 1
                    violation_found = True
                    violation_details = {
                        "property": prop_name,
                        "message": message,
                        "config": config_summary(config),
                        "class_key": class_key_str(key),
                        "config_index": i,
                    }
                    print(f"\n\n{'='*72}")
                    print(f"CRITICAL VIOLATION FOUND!")
                    print(f"{'='*72}")
                    print(f"Property:  {prop_name}")
                    print(f"Message:   {message}")
                    print(f"Config:    {config_summary(config)}")
                    print(f"Class:     {class_key_str(key)}")
                    print(f"Config #:  {i}")
                    print(f"{'='*72}")
                    # Stop immediately
                    return None
                elif message and "Inconclusive" in message:
                    stats["inconclusive"][prop_name] += 1
                    overall_inconclusive += 1
                else:
                    stats["passed"][prop_name] += 1
                    overall_passed += 1

        elapsed = time.time() - start_time
        print(f"\n\nDone in {elapsed:.1f}s ({total_configs/elapsed:.1f} cfg/s)")

    finally:
        teardown_schema(conn)
        conn.close()

    # Build results JSON
    results_json = build_results_json(
        class_stats, total_configs, max_type_size, n_rows, elapsed,
        overall_passed, overall_failed, overall_inconclusive,
    )

    # Save results
    output_path = os.path.join(os.path.dirname(__file__), "mode_a_results.json")
    with open(output_path, "w") as f:
        json.dump(results_json, f, indent=2)
    print(f"\nResults saved to {output_path}")

    # Print summary table
    print_summary_table(class_stats, overall_passed, overall_failed,
                        overall_inconclusive, total_configs)

    return results_json


def build_results_json(class_stats, total_configs, max_type_size, n_rows,
                       elapsed, overall_passed, overall_failed,
                       overall_inconclusive):
    """Build the results dictionary for JSON output."""
    results = {
        "mode": "A",
        "description": "Exhaustive small-model checking",
        "parameters": {
            "max_type_size": max_type_size,
            "n_rows": n_rows,
        },
        "total_configs": total_configs,
        "elapsed_seconds": round(elapsed, 2),
        "summary": {
            "total_property_checks": overall_passed + overall_failed + overall_inconclusive,
            "passed": overall_passed,
            "failed": overall_failed,
            "inconclusive": overall_inconclusive,
        },
        "verdict": "ALL PASSED" if overall_failed == 0 else "VIOLATION FOUND",
        "by_class": {},
    }

    for key, stats in sorted(class_stats.items(), key=lambda x: str(x[0])):
        class_name = class_key_str(key)
        results["by_class"][class_name] = {
            "configs_tested": stats["total"],
            "passed": dict(stats["passed"]),
            "failed": dict(stats["failed"]),
            "inconclusive": dict(stats["inconclusive"]),
        }

    return results


def print_summary_table(class_stats, overall_passed, overall_failed,
                        overall_inconclusive, total_configs):
    """Print a human-readable summary table."""
    print()
    print("=" * 90)
    print("MODE A SUMMARY — Exhaustive Small-Model Checking")
    print("=" * 90)
    print()

    # Header
    header = f"{'Class':<45} {'Configs':>7} {'Pass':>6} {'Inc':>6} {'Fail':>6}"
    print(header)
    print("-" * len(header))

    for key in sorted(class_stats.keys(), key=lambda x: str(x)):
        stats = class_stats[key]
        p = sum(stats["passed"].values())
        inc = sum(stats["inconclusive"].values())
        f = sum(stats["failed"].values())
        name = class_key_str(key)
        print(f"{name:<45} {stats['total']:>7} {p:>6} {inc:>6} {f:>6}")

    print("-" * len(header))
    print(f"{'TOTAL':<45} {total_configs:>7} {overall_passed:>6} "
          f"{overall_inconclusive:>6} {overall_failed:>6}")
    print()

    if overall_failed == 0:
        print("VERDICT: ALL PROPERTIES PASSED across all configurations.")
        print("         No counterexamples found.")
    else:
        print("VERDICT: VIOLATION(S) FOUND — see details above.")
    print()

    # Per-property breakdown
    print("Per-property breakdown:")
    print("-" * 60)
    prop_totals = defaultdict(lambda: {"passed": 0, "inconclusive": 0, "failed": 0})
    for stats in class_stats.values():
        for prop in PROPERTY_NAMES:
            prop_totals[prop]["passed"] += stats["passed"].get(prop, 0)
            prop_totals[prop]["inconclusive"] += stats["inconclusive"].get(prop, 0)
            prop_totals[prop]["failed"] += stats["failed"].get(prop, 0)

    for prop in PROPERTY_NAMES:
        t = prop_totals[prop]
        total = t["passed"] + t["inconclusive"] + t["failed"]
        print(f"  {prop:<30} pass={t['passed']:>5}  "
              f"inc={t['inconclusive']:>5}  fail={t['failed']:>5}  "
              f"(total={total})")
    print()


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Mode A: Exhaustive small-model checking for equi-join grain inference"
    )
    parser.add_argument(
        "--max-type-size", type=int, default=5,
        help="Maximum number of columns per relation (default: 5)"
    )
    parser.add_argument(
        "--n-rows", type=int, default=10,
        help="Number of rows to generate per table (default: 10)"
    )
    args = parser.parse_args()

    result = run_mode_a(
        max_type_size=args.max_type_size,
        n_rows=args.n_rows,
    )

    if result is None:
        print("\nExiting with failure (violation found).")
        sys.exit(1)
    elif result["summary"]["failed"] > 0:
        sys.exit(1)
    else:
        sys.exit(0)
