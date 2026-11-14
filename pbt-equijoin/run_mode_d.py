#!/usr/bin/env python3
"""
Mode D: declared functional dependencies inside and across the join inputs.

The base modes (A, B, C) generate configurations in which the only
declarations are the two input grains, so the second hypothesis of the
equi-join theorem (arXiv v4 `thm:equijoin-grain`) holds by construction and
the reduction of `prop:grain-reduction-fd` has nothing to do. Mode D declares
one further dependency U -> v per configuration, within one input or spanning
both, enforces it in the generated data, and checks D1-D6 of
``properties_fd``: the theorem's candidate is then a superkey but not the
grain, and the reduction returns a key.

Two sub-runs:
  * exhaustive: every admissible dependency (determinant of at most 3 fields)
    on every configuration with |Ri| <= --max-type-size (default 4);
  * random: Hypothesis draws configurations at larger sizes (max_jk=6,
    max_r_only=5) and one admissible dependency each, --random-examples
    (default 5000) times.

Any failure of D1-D5 is a property violation and is reported; D6 may be
inconclusive. Results are written to mode_d_results.json.

Usage:
    python run_mode_d.py [--max-type-size 4] [--random-examples 5000] [--n-rows 30]
"""

import argparse
import json
import os
import sys
import time
from collections import Counter
from datetime import datetime

import psycopg2
from hypothesis import HealthCheck, given, settings, strategies as st

from config import Config
from fd_config import FDConfig, admissible_fds, all_fd_configs, make_fd_config
from generators import all_configs_up_to, equijoin_config
from properties_fd import run_all_fd_properties
from sql_runner import SCHEMA

PROPS = ["D1_fd_holds", "D2_candidate_superkey", "D3_candidate_reducible",
         "D4_reduction_key", "D5_reduction_drops_target", "D6_reduction_minimal"]


def get_connection():
    dsn = os.environ.get("DATABASE_URL")
    conn = psycopg2.connect(dsn) if dsn else psycopg2.connect(dbname="postgres")
    conn.autocommit = False
    with conn.cursor() as cur:
        cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        cur.execute(f"CREATE SCHEMA {SCHEMA}")
    conn.commit()
    return conn


class Stats:
    def __init__(self):
        self.total = 0
        self.by_kind = Counter()
        self.by_lhs_size = Counter()
        self.props = {p: {"passed": 0, "failed": 0, "inconclusive": 0} for p in PROPS}
        self.failures = []

    def record(self, fdc: FDConfig, results: dict):
        self.total += 1
        self.by_kind[fdc.fd.kind] += 1
        self.by_lhs_size[str(len(fdc.fd.lhs))] += 1
        for p, (ok, msg) in results.items():
            if not ok:
                self.props[p]["failed"] += 1
                self.failures.append({
                    "property": p, "message": msg,
                    "config": {"r1_fields": list(fdc.config.r1_fields),
                               "r2_fields": list(fdc.config.r2_fields),
                               "jk": list(fdc.config.jk), "g1": list(fdc.config.g1),
                               "g2": list(fdc.config.g2)},
                    "fd": {"lhs": list(fdc.fd.lhs), "rhs": fdc.fd.rhs, "kind": fdc.fd.kind},
                    "candidate": list(fdc.candidate), "reduced": list(fdc.reduced),
                })
            elif msg and "Inconclusive" in msg:
                self.props[p]["inconclusive"] += 1
            else:
                self.props[p]["passed"] += 1

    def as_dict(self):
        return {"total_fd_configs": self.total, "by_kind": dict(self.by_kind),
                "by_lhs_size": dict(sorted(self.by_lhs_size.items())),
                "property_results": self.props, "failures": self.failures}


def run_one(conn, fdc: FDConfig, stats: Stats, cid: int, n_rows: int):
    try:
        conn.rollback()
    except Exception:
        pass
    results = run_all_fd_properties(conn, fdc, n_rows=n_rows, seed=42, config_id=cid)
    stats.record(fdc, results)
    return results


def run_exhaustive(conn, max_type_size: int, n_rows: int) -> Stats:
    stats = Stats()
    cid = 0
    t0 = time.time()
    for fdc in all_fd_configs(all_configs_up_to(max_type_size), max_lhs=3):
        cid += 1
        run_one(conn, fdc, stats, cid, n_rows)
        if cid % 2000 == 0:
            print(f"  exhaustive: {cid} fd-configs, {time.time() - t0:.0f}s, "
                  f"failures so far: {len(stats.failures)}", flush=True)
    return stats


@st.composite
def fd_config_strategy(draw, max_jk=6, max_r_only=5):
    config = draw(equijoin_config(max_jk=max_jk, max_r_only=max_r_only))
    fds = list(admissible_fds(config, max_lhs=3))
    if not fds:
        # no non-join-key grain field in the candidate: nothing to declare
        from hypothesis import assume
        assume(False)
    fd = draw(st.sampled_from(fds))
    return make_fd_config(config, fd)


def run_random(conn, n_examples: int, n_rows: int) -> Stats:
    stats = Stats()
    counter = {"cid": 100_000}

    @given(fdc=fd_config_strategy())
    @settings(max_examples=n_examples, deadline=None, database=None,
              suppress_health_check=[HealthCheck.too_slow,
                                     HealthCheck.filter_too_much,
                                     HealthCheck.function_scoped_fixture])
    def test(fdc: FDConfig):
        counter["cid"] += 1
        results = run_one(conn, fdc, stats, counter["cid"], n_rows)
        for p, (ok, msg) in results.items():
            assert ok, f"{p}: {msg}"

    try:
        test()
        stats.hypothesis_passed = True
        stats.hypothesis_error = None
    except Exception as e:  # a property violation; recorded in stats.failures too
        stats.hypothesis_passed = False
        stats.hypothesis_error = str(e)[:2000]
    return stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-type-size", type=int, default=4)
    ap.add_argument("--random-examples", type=int, default=5000)
    ap.add_argument("--n-rows", type=int, default=30)
    args = ap.parse_args()

    print("=" * 70)
    print("Mode D: declared dependencies inside and across the inputs")
    print(f"  exhaustive up to |Ri| <= {args.max_type_size}, lhs <= 3; "
          f"random {args.random_examples} examples; n_rows={args.n_rows}")
    print(f"  Started: {datetime.now().isoformat()}")
    print("=" * 70, flush=True)

    conn = get_connection()
    t0 = time.time()
    ex = run_exhaustive(conn, args.max_type_size, args.n_rows)
    t1 = time.time()
    print(f"exhaustive done: {ex.total} fd-configs in {t1 - t0:.1f}s, "
          f"failures: {len(ex.failures)}", flush=True)
    rn = run_random(conn, args.random_examples, args.n_rows)
    t2 = time.time()
    print(f"random done: {rn.total} fd-configs in {t2 - t1:.1f}s, "
          f"failures: {len(rn.failures)}", flush=True)
    try:
        with conn.cursor() as cur:
            cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE")
        conn.commit()
    finally:
        conn.close()

    out = {
        "mode": "D",
        "description": "Declared FDs within and across inputs; candidate superkey, "
                       "candidate reducible, reduction a key (prop:grain-reduction-fd)",
        "started": datetime.now().isoformat(),
        "n_rows_per_config": args.n_rows,
        "exhaustive": {"max_type_size": args.max_type_size, "max_lhs": 3,
                       "elapsed_seconds": round(t1 - t0, 1), **ex.as_dict()},
        "random": {"max_examples": args.random_examples,
                   "generator_params": {"max_jk": 6, "max_r_only": 5},
                   "elapsed_seconds": round(t2 - t1, 1),
                   "hypothesis_passed": getattr(rn, "hypothesis_passed", None),
                   "hypothesis_error": getattr(rn, "hypothesis_error", None),
                   **rn.as_dict()},
    }
    path = os.path.join(os.path.dirname(__file__) or ".", "mode_d_results.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2)

    print()
    for name, s in (("exhaustive", ex), ("random", rn)):
        print(f"{name}: {s.total} fd-configs; kinds {dict(s.by_kind)}")
        for p, c in s.props.items():
            status = "PASS" if c["failed"] == 0 else "FAIL"
            print(f"  {p:28s} {status}  passed={c['passed']} failed={c['failed']} "
                  f"inconclusive={c['inconclusive']}")
    n_fail = len(ex.failures) + len(rn.failures)
    print(f"\nResults saved to {path}; failures: {n_fail}")
    return 1 if n_fail else 0


if __name__ == "__main__":
    sys.exit(main())
