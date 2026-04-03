#!/usr/bin/env python3
"""
Mode C: Targeted edge-case testing for equi-join grain inference.

Runs all 6 properties (P1-P6) on 16 hand-crafted boundary configurations,
each tested with both uniform and skewed data distributions.

Usage:
    python run_mode_c.py
"""

import json
import sys
import time

import psycopg2

from edge_cases import ALL_EDGE_CASES
from properties import run_all_properties
from sql_runner import SCHEMA


DISTRIBUTIONS = ["uniform", "skewed"]
N_ROWS = 50
SEED = 42


def main():
    # Connect to PostgreSQL
    conn = psycopg2.connect(dbname="postgres")
    conn.autocommit = False

    # Setup schema
    with conn.cursor() as cur:
        cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        cur.execute(f"CREATE SCHEMA {SCHEMA}")
    conn.commit()

    all_results = {}
    total_tests = 0
    total_passed = 0
    total_failed = 0
    failures = []

    config_id_counter = 0

    print("=" * 78)
    print("Mode C: Edge-Case Verification (16 cases x 2 distributions)")
    print("=" * 78)
    print()

    t0 = time.time()

    for case_name, case_fn in ALL_EDGE_CASES:
        config = case_fn()
        case_results = {}

        for dist in DISTRIBUTIONS:
            config_id_counter += 1
            label = f"{case_name}/{dist}"

            # Patch the data generation by passing distribution via
            # a custom n_rows/seed/config_id call.  run_all_properties
            # generates data internally with generate_data, which uses
            # the default "uniform" distribution.  We need to call the
            # pipeline manually to control distribution.
            from data_gen import generate_data
            from sql_runner import (
                cleanup_tables,
                count_total,
                create_tables,
                execute_join,
            )
            from properties import (
                check_convention_smallest,
                check_incomparable_both_minimal,
                check_minimality_convention,
                check_size_relationship,
                check_uniqueness_both,
                check_wrong_direction_non_minimal,
            )

            cid = config_id_counter
            results = {}

            # P5, P6: pure Python
            results["P5_size_relationship"] = check_size_relationship(config)
            results["P6_convention_smallest"] = check_convention_smallest(config)

            # P1-P4: SQL
            try:
                r1_data, r2_data = generate_data(
                    config, n_rows=N_ROWS, seed=SEED, distribution=dist
                )
                r1_table, r2_table = create_tables(
                    conn, config, r1_data, r2_data, config_id=cid
                )
                res_table = execute_join(
                    conn, config, r1_table, r2_table, config_id=cid
                )

                results["P1_uniqueness"] = check_uniqueness_both(
                    conn, config, res_table
                )
                results["P2_minimality"] = check_minimality_convention(
                    conn, config, res_table,
                    r1_table=r1_table, r2_table=r2_table,
                )
                results["P3_wrong_direction"] = check_wrong_direction_non_minimal(
                    conn, config, res_table
                )
                results["P4_incomparable_both"] = check_incomparable_both_minimal(
                    conn, config, res_table,
                    r1_table=r1_table, r2_table=r2_table,
                )
            finally:
                cleanup_tables(conn, config_id=cid)

            # Tally
            case_pass = True
            for prop_name, (passed, msg) in results.items():
                total_tests += 1
                if passed:
                    total_passed += 1
                else:
                    total_failed += 1
                    case_pass = False
                    failures.append((label, prop_name, msg))

            status = "PASS" if case_pass else "FAIL"
            print(f"  [{status}] {label}")
            for prop_name, (passed, msg) in sorted(results.items()):
                flag = "ok" if passed else "FAIL"
                print(f"         {flag}  {prop_name}: {msg}")

            case_results[dist] = {
                prop: {"passed": p, "message": m}
                for prop, (p, m) in results.items()
            }

        # Store metadata alongside results
        all_results[case_name] = {
            "jk_rel": config.jk_rel.value,
            "g1_jk": list(config.g1_jk),
            "g2_jk": list(config.g2_jk),
            "g1_rest": list(config.g1_rest),
            "g2_rest": list(config.g2_rest),
            "f1": list(config.f1),
            "f2": list(config.f2),
            "convention_grain": list(config.convention_grain),
            "distributions": case_results,
        }
        print()

    elapsed = time.time() - t0

    # Teardown schema
    try:
        with conn.cursor() as cur:
            cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        conn.commit()
    finally:
        conn.close()

    # Save results
    output = {
        "mode": "C",
        "description": "Targeted edge-case verification",
        "n_cases": len(ALL_EDGE_CASES),
        "distributions": DISTRIBUTIONS,
        "n_rows": N_ROWS,
        "seed": SEED,
        "total_tests": total_tests,
        "total_passed": total_passed,
        "total_failed": total_failed,
        "elapsed_seconds": round(elapsed, 2),
        "cases": all_results,
    }
    with open("mode_c_results.json", "w") as f:
        json.dump(output, f, indent=2)

    # Summary
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print(f"  Cases:          {len(ALL_EDGE_CASES)}")
    print(f"  Distributions:  {', '.join(DISTRIBUTIONS)}")
    print(f"  Total tests:    {total_tests}")
    print(f"  Passed:         {total_passed}")
    print(f"  Failed:         {total_failed}")
    print(f"  Elapsed:        {elapsed:.2f}s")
    print()

    if failures:
        print("FAILURES:")
        for label, prop, msg in failures:
            print(f"  {label} / {prop}: {msg}")
        print()
        print("RESULT: FAIL")
        sys.exit(1)
    else:
        print("RESULT: ALL PASSED")
        print()
        print(f"Saved to mode_c_results.json")
        sys.exit(0)


if __name__ == "__main__":
    main()
