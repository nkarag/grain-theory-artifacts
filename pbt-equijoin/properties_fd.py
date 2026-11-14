"""
Properties of Mode D: the equi-join candidate under a declared dependency.

For an ``FDConfig`` (configuration plus one declared dependency ``U -> v``):

  D1 (Dependency holds):   ``U -> v`` holds on the join result (data sanity).
  D2 (Candidate superkey): the theorem's candidate K is still unique on the
                           result (first claim of prop:grain-reduction-fd).
  D3 (Candidate reducible): ``v`` is removable from K on the result, so K is
                           NOT the grain once the dependency is declared
                           (why the theorem needs its second hypothesis).
  D4 (Reduction is a key):  the reduction K' of prop:grain-reduction-fd is
                           unique on the result.
  D5 (Reduction drops v):   structural: ``v`` is in K and not in K' (pure Python).
  D6 (Reduction minimal):   K' is irreducible on the result; non-minimality
                           is reported as inconclusive, as for P2 of the base
                           modes, because random data can make a column
                           accidentally redundant.

D1-D4 and D6 run SQL against PostgreSQL; D5 is pure Python.
"""

from typing import Tuple

from fd_config import FDConfig
from data_gen_fd import generate_data_fd
from sql_runner import (
    _resolve_grain_cols,
    check_minimality,
    check_uniqueness,
    cleanup_tables,
    count_distinct,
    count_total,
    create_tables,
    execute_join,
    find_removable_columns,
)


def check_reduction_drops_target(fdc: FDConfig) -> Tuple[bool, str]:
    """D5: the declared target is in the candidate and not in the reduction."""
    v = fdc.fd.rhs
    if v in fdc.candidate and v not in fdc.reduced and v in fdc.removed:
        return True, f"{v} removed by the reduction: {fdc.candidate} -> {fdc.reduced}"
    return False, (f"REDUCTION DID NOT DROP TARGET: v={v}, candidate={fdc.candidate}, "
                   f"reduced={fdc.reduced}, removed={fdc.removed}")


def _setup(conn, fdc: FDConfig, n_rows: int, seed: int, config_id: int):
    r1_data, r2_data = generate_data_fd(fdc, n_rows=n_rows, seed=seed)
    r1_table, r2_table = create_tables(conn, fdc.config, r1_data, r2_data,
                                       config_id=config_id)
    res_table = execute_join(conn, fdc.config, r1_table, r2_table,
                             config_id=config_id)
    return r1_table, r2_table, res_table


def check_fd_holds(conn, fdc: FDConfig, res_table: str) -> Tuple[bool, str]:
    """D1: COUNT(DISTINCT U) == COUNT(DISTINCT U, v) on the result."""
    lhs_cols = _resolve_grain_cols(tuple(fdc.fd.lhs), fdc.config)
    rhs_cols = _resolve_grain_cols((fdc.fd.rhs,), fdc.config)
    if count_total(conn, res_table) == 0:
        return True, "Vacuous: empty join"
    d_lhs = count_distinct(conn, res_table, lhs_cols)
    d_both = count_distinct(conn, res_table, lhs_cols + rhs_cols)
    if d_lhs == d_both:
        return True, f"{fdc.fd.lhs} -> {fdc.fd.rhs} holds on the result ({d_lhs} groups)"
    return False, (f"DECLARED FD VIOLATED ON RESULT: {fdc.fd.lhs} -> {fdc.fd.rhs}, "
                   f"distinct(lhs)={d_lhs}, distinct(lhs+rhs)={d_both}")


def check_candidate_superkey(conn, fdc: FDConfig, res_table: str) -> Tuple[bool, str]:
    """D2: the theorem's candidate is unique on the result."""
    cols = _resolve_grain_cols(fdc.candidate, fdc.config)
    if check_uniqueness(conn, res_table, cols):
        return True, f"Candidate {fdc.candidate} is a superkey of the result"
    return False, f"CANDIDATE NOT A SUPERKEY: {fdc.candidate}"


def check_candidate_reducible(conn, fdc: FDConfig, res_table: str) -> Tuple[bool, str]:
    """D3: the candidate minus the declared target is still unique."""
    total = count_total(conn, res_table)
    if total <= 1:
        return True, "Vacuous: 0-1 rows"
    cols = _resolve_grain_cols(fdc.candidate, fdc.config)
    v_col = _resolve_grain_cols((fdc.fd.rhs,), fdc.config)[0]
    reduced = [c for c in cols if c != v_col]
    if not reduced:
        return True, "Vacuous: candidate is the target alone"
    if count_distinct(conn, res_table, reduced) == total:
        return True, f"Candidate reducible: {v_col} removable"
    return False, (f"CANDIDATE NOT REDUCIBLE although {fdc.fd.lhs} -> {fdc.fd.rhs} "
                   f"is declared: {v_col} not removable from {cols}")


def check_reduction_key(conn, fdc: FDConfig, res_table: str) -> Tuple[bool, str]:
    """D4: the reduction of prop:grain-reduction-fd is unique on the result."""
    cols = _resolve_grain_cols(fdc.reduced, fdc.config)
    if check_uniqueness(conn, res_table, cols):
        return True, f"Reduction {fdc.reduced} is a key of the result"
    return False, f"REDUCTION NOT A KEY: {fdc.reduced}"


def check_reduction_minimal(conn, fdc: FDConfig, res_table: str) -> Tuple[bool, str]:
    """D6: the reduction is irreducible on the result; else inconclusive."""
    cols = _resolve_grain_cols(fdc.reduced, fdc.config)
    total = count_total(conn, res_table)
    if total <= 1 or len(cols) <= 1:
        return True, "Minimality vacuous"
    if check_minimality(conn, res_table, cols):
        return True, f"Reduction is minimal ({len(cols)} cols)"
    removable = find_removable_columns(conn, res_table, cols)
    return True, (f"Inconclusive: reduction not minimal in this sample "
                  f"(removable={removable}); insufficient collision coverage")


def run_all_fd_properties(conn, fdc: FDConfig, n_rows: int = 30, seed: int = 42,
                          config_id: int = 0) -> dict:
    """Run D1-D6 on one FDConfig. Always cleans up the tables."""
    results = {"D5_reduction_drops_target": check_reduction_drops_target(fdc)}
    try:
        r1_table, r2_table, res_table = _setup(conn, fdc, n_rows, seed, config_id)
        results["D1_fd_holds"] = check_fd_holds(conn, fdc, res_table)
        results["D2_candidate_superkey"] = check_candidate_superkey(conn, fdc, res_table)
        results["D3_candidate_reducible"] = check_candidate_reducible(conn, fdc, res_table)
        results["D4_reduction_key"] = check_reduction_key(conn, fdc, res_table)
        results["D6_reduction_minimal"] = check_reduction_minimal(conn, fdc, res_table)
    finally:
        cleanup_tables(conn, config_id=config_id)
    return results
