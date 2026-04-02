#!/usr/bin/env python3
"""
Grain Formula Revalidation — 100 Examples
==========================================

Generates SQL to test both the paper's Theorem 6.1 formula and the corrected
formula across 100 equi-join examples.

For each example, tests:
  1. Paper's grain formula: uniqueness (should PASS) + minimality
  2. Corrected formula:     uniqueness (should PASS) + minimality (should PASS)

Expected results:
  - Case A examples (73): both formulas identical → both pass uniqueness & minimality
  - Case B examples (27): paper passes uniqueness but FAILS minimality;
                           corrected passes both

Usage:
    python3 generate_revalidation.py > revalidation.sql
    psql -d postgres -f revalidation.sql 2>&1 | tee output.txt
"""

import sys
from dataclasses import dataclass, field
from typing import List


@dataclass
class Example:
    id: int
    category: str
    case_type: str  # 'A' or 'B'
    desc: str
    # R1
    r1_cols: List[str]
    r1_grain: List[str]
    r1_nongrain_deterministic: bool  # whether nongrain cols are determined by grain
    # R2
    r2_cols: List[str]
    r2_grain: List[str]
    r2_nongrain_deterministic: bool
    # Join
    jk: List[str]
    # Grains to test
    paper_grain: List[str]
    corrected_grain: List[str]
    # Data gen params
    r1_nrows: int = 1000
    r2_nrows: int = 1000
    r1_grain_ranges: List[int] = field(default_factory=list)  # cardinality of each grain col
    r2_grain_ranges: List[int] = field(default_factory=list)


def make_case_b_main(eid, suffix, r1_g_ranges, r2_g_ranges):
    """Case B: R1(a,b,c,e) G1=(a,c), R2(a,b,c,d) G2=(a,b), Jk=(a,b,c)
    Paper grain: (a,b,c). Corrected: (a,c). Column b is removable."""
    return Example(
        id=eid, category='Main Theorem', case_type='B',
        desc=f'Case B — Jk={{a,b,c}}, G1={{a,c}}, G2={{a,b}} [{suffix}]',
        r1_cols=['a', 'b', 'c', 'e'], r1_grain=['a', 'c'],
        r1_nongrain_deterministic=True,
        r2_cols=['a', 'b', 'c', 'd'], r2_grain=['a', 'b'],
        r2_nongrain_deterministic=True,
        jk=['a', 'b', 'c'],
        paper_grain=['a', 'b', 'c'], corrected_grain=['a', 'c'],
        r1_grain_ranges=r1_g_ranges, r2_grain_ranges=r2_g_ranges,
    )


def make_case_b_incomp(eid, suffix, r1_g_ranges, r2_g_ranges):
    """Case B: R1(a,b,c,v1) G1=(a,c), R2(a,b,d,v2) G2=(b,d), Jk=(a,b)
    G1∩Jk={a}, G2∩Jk={b}, incomparable.
    Paper: (a,b,c,d). Corrected: G[R1]∪(G[R2]\\Jk) = {a,c}∪{d} = (a,c,d)."""
    return Example(
        id=eid, category='Incomparable Grains', case_type='B',
        desc=f'Case B — Jk={{a,b}}, G1={{a,c}}, G2={{b,d}} [{suffix}]',
        r1_cols=['a', 'b', 'c', 'v1'], r1_grain=['a', 'c'],
        r1_nongrain_deterministic=True,
        r2_cols=['a', 'b', 'd', 'v2'], r2_grain=['b', 'd'],
        r2_nongrain_deterministic=True,
        jk=['a', 'b'],
        paper_grain=['a', 'b', 'c', 'd'], corrected_grain=['a', 'c', 'd'],
        r1_grain_ranges=r1_g_ranges, r2_grain_ranges=r2_g_ranges,
    )


def make_case_b_natjoin(eid, suffix, r1_g_ranges, r2_g_ranges):
    """Case B: R1(a,b,c) G1=(a,b), R2(b,c,d) G2=(c,d), Jk=(b,c)
    G1∩Jk={b}, G2∩Jk={c}, incomparable.
    Paper: (a,b,c,d). Corrected: G[R1]∪(G[R2]\\Jk) = {a,b}∪{d} = (a,b,d)."""
    return Example(
        id=eid, category='Natural Join', case_type='B',
        desc=f'Case B — Jk={{b,c}}, G1={{a,b}}, G2={{c,d}} [{suffix}]',
        r1_cols=['a', 'b', 'c'], r1_grain=['a', 'b'],
        r1_nongrain_deterministic=True,
        r2_cols=['b', 'c', 'd'], r2_grain=['c', 'd'],
        r2_nongrain_deterministic=True,
        jk=['b', 'c'],
        paper_grain=['a', 'b', 'c', 'd'], corrected_grain=['a', 'b', 'd'],
        r1_grain_ranges=r1_g_ranges, r2_grain_ranges=r2_g_ranges,
    )


def make_case_a_equal(eid, suffix, grain_size, jk_size, g_ranges):
    """Case A: Equal grains, join on subset of grain cols."""
    grain_cols = [f'g{i}' for i in range(1, grain_size + 1)]
    jk_cols = grain_cols[:jk_size]
    rest = grain_cols[jk_size:]
    all_r1 = grain_cols + ['v1']
    all_r2 = grain_cols + ['v2']
    # Paper grain = rest_r1 × rest_r2 × common (= Jk portion of grain)
    # Since equal grains and Jk ⊆ grain: G1∩Jk = G2∩Jk → Case A
    # rest outside Jk from each side, plus common Jk part
    if rest:
        paper = [f'{c}_r1' for c in rest] + [f'{c}_r2' for c in rest] + jk_cols
    else:
        paper = jk_cols
    corrected = paper  # Case A: same
    return Example(
        id=eid, category='Equal Grains', case_type='A',
        desc=f'Equal grains |G|={grain_size}, |Jk|={jk_size} [{suffix}]',
        r1_cols=all_r1, r1_grain=grain_cols,
        r1_nongrain_deterministic=True,
        r2_cols=all_r2, r2_grain=grain_cols,
        r2_nongrain_deterministic=True,
        jk=jk_cols, paper_grain=paper, corrected_grain=corrected,
        r1_grain_ranges=g_ranges, r2_grain_ranges=g_ranges,
    )


def make_case_a_ordered(eid, suffix, g_ranges_fine, g_ranges_coarse,
                        reversed=False):
    """Case A: Ordered grains.
    Normal:   R1 finer (G1 = g1 × g2), R2 coarser (G2 = g1).
    Reversed: R1 coarser (G1 = g1), R2 finer (G2 = g1 × g2).
    Jk = (g1). G1∩Jk = {g1}, G2∩Jk = {g1}. Case A.
    Paper grain = finer grain = (g1, g2). Corrected = same."""
    if not reversed:
        return Example(
            id=eid, category='Ordered Grains', case_type='A',
            desc=f'Ordered — G1={{g1,g2}} > G2={{g1}}, Jk={{g1}} [{suffix}]',
            r1_cols=['g1', 'g2', 'v1'], r1_grain=['g1', 'g2'],
            r1_nongrain_deterministic=True,
            r2_cols=['g1', 'v2'], r2_grain=['g1'],
            r2_nongrain_deterministic=True,
            jk=['g1'],
            paper_grain=['g1', 'g2'], corrected_grain=['g1', 'g2'],
            r1_grain_ranges=g_ranges_fine, r2_grain_ranges=g_ranges_coarse,
        )
    else:
        # R1 coarser, R2 finer. Paper grain = G[R1] ∪ (G[R2] \ Jk) = {g1} ∪ {g2} = {g1,g2}
        return Example(
            id=eid, category='Ordered Grains', case_type='A',
            desc=f'Ordered — G1={{g1}} < G2={{g1,g2}}, Jk={{g1}} [{suffix}]',
            r1_cols=['g1', 'v1'], r1_grain=['g1'],
            r1_nongrain_deterministic=True,
            r2_cols=['g1', 'g2', 'v2'], r2_grain=['g1', 'g2'],
            r2_nongrain_deterministic=True,
            jk=['g1'],
            paper_grain=['g1', 'g2'], corrected_grain=['g1', 'g2'],
            r1_grain_ranges=g_ranges_coarse, r2_grain_ranges=g_ranges_fine,
        )


def make_case_a_incomp(eid, suffix, g_ranges):
    """Case A: Incomparable grains but comparable Jk-portions.
    R1(a,b,c,v1) G1=(a,b,c), R2(a,b,d,v2) G2=(a,b,d), Jk=(a,b).
    G1∩Jk = {a,b} = G2∩Jk → Case A.
    Paper grain = (c, d, a, b). Corrected = same."""
    return Example(
        id=eid, category='Incomparable Grains', case_type='A',
        desc=f'Case A — Jk={{a,b}}, G1={{a,b,c}}, G2={{a,b,d}} [{suffix}]',
        r1_cols=['a', 'b', 'c', 'v1'], r1_grain=['a', 'b', 'c'],
        r1_nongrain_deterministic=True,
        r2_cols=['a', 'b', 'd', 'v2'], r2_grain=['a', 'b', 'd'],
        r2_nongrain_deterministic=True,
        jk=['a', 'b'],
        paper_grain=['a', 'b', 'c', 'd'], corrected_grain=['a', 'b', 'c', 'd'],
        r1_grain_ranges=g_ranges, r2_grain_ranges=g_ranges,
    )


def make_case_a_main(eid, suffix, g_ranges_r1, g_ranges_r2):
    """Case A: R1(a,b,v1) G1=(a), R2(a,b,v2) G2=(a,b), Jk=(a,b).
    G1∩Jk = {a} ⊆ G2∩Jk = {a,b} → Case A.
    Paper: (G1\\Jk)×(G2\\Jk)×(G1∩G2∩Jk) = {}×{}×{a} = (a).
    Corrected: G[R1]∪(G[R2]\\Jk) = {a}∪{} = (a). Same."""
    return Example(
        id=eid, category='Main Theorem', case_type='A',
        desc=f'Case A — Jk={{a,b}}, G1={{a}}, G2={{a,b}} [{suffix}]',
        r1_cols=['a', 'b', 'v1'], r1_grain=['a'],
        r1_nongrain_deterministic=True,
        r2_cols=['a', 'b', 'v2'], r2_grain=['a', 'b'],
        r2_nongrain_deterministic=True,
        jk=['a', 'b'],
        paper_grain=['a'], corrected_grain=['a'],
        r1_grain_ranges=g_ranges_r1, r2_grain_ranges=g_ranges_r2,
    )


def make_case_a_natjoin(eid, suffix, g_ranges):
    """Case A natural join: R1(a,b,c) G1=(a,b), R2(b,c,d) G2=(b,c), Jk=(b,c).
    G1∩Jk = {b} ⊆ G2∩Jk = {b,c} → Case A.
    Paper grain = {a} ∪ {} ∪ {b} = (a, b). Corrected = same.
    Wait: G1_rest = {a}, G2_rest = {d}... hold on.
    G[R1] = {a,b}. G[R2] = {b,c}. Jk = {b,c}.
    G1∩Jk = {a,b} ∩ {b,c} = {b}. G2∩Jk = {b,c} ∩ {b,c} = {b,c}.
    {b} ⊆ {b,c} → Case A.
    G1_rest = G[R1] \ Jk = {a}. G2_rest = G[R2] \ Jk = {}.
    G_common = G1∩Jk ∩ G2∩Jk = {b}.
    Paper = {a} × {} × {b} = (a, b).
    Corrected = G[R1] ∪ (G[R2] \ Jk) = {a,b} ∪ {} = (a, b). Same."""
    return Example(
        id=eid, category='Natural Join', case_type='A',
        desc=f'Case A — Jk={{b,c}}, G1={{a,b}}, G2={{b,c}} [{suffix}]',
        r1_cols=['a', 'b', 'c'], r1_grain=['a', 'b'],
        r1_nongrain_deterministic=True,
        r2_cols=['b', 'c', 'd'], r2_grain=['b', 'c'],
        r2_nongrain_deterministic=True,
        jk=['b', 'c'],
        paper_grain=['a', 'b'], corrected_grain=['a', 'b'],
        r1_grain_ranges=g_ranges, r2_grain_ranges=g_ranges,
    )


def build_examples():
    """Build all 100 examples."""
    examples = []
    eid = 1

    # ── CASE B: Main Theorem (9 examples) ──
    range_sets = [
        ([50, 20], [50, 20]),
        ([40, 25], [40, 25]),
        ([100, 10], [100, 10]),
        ([25, 40], [25, 40]),
        ([20, 50], [20, 50]),
        ([10, 100], [10, 100]),
        ([30, 30], [30, 30]),
        ([200, 5], [200, 5]),
        ([5, 200], [5, 200]),
    ]
    for i, (r1r, r2r) in enumerate(range_sets):
        examples.append(make_case_b_main(eid, f'v{i+1}', r1r, r2r))
        eid += 1

    # ── CASE B: Incomparable Grains (9 examples) ──
    for i, (r1r, r2r) in enumerate(range_sets):
        examples.append(make_case_b_incomp(eid, f'v{i+1}', r1r, r2r))
        eid += 1

    # ── CASE B: Natural Join (9 examples) ──
    for i, (r1r, r2r) in enumerate(range_sets):
        examples.append(make_case_b_natjoin(eid, f'v{i+1}', r1r, r2r))
        eid += 1

    # ── CASE A: Main Theorem (13 examples) ──
    a_ranges = [
        ([1000], [50, 20]),
        ([500], [25, 20]),
        ([200], [100, 10]),
        ([100], [50, 20]),
        ([50], [50, 20]),
        ([1000], [100, 10]),
        ([500], [50, 20]),
        ([200], [200, 5]),
        ([100], [100, 10]),
        ([50], [25, 40]),
        ([1000], [25, 40]),
        ([500], [100, 10]),
        ([200], [50, 20]),
    ]
    for i, (r1r, r2r) in enumerate(a_ranges):
        examples.append(make_case_a_main(eid, f'v{i+1}', r1r, r2r))
        eid += 1

    # ── CASE A: Equal Grains (20 examples) ──
    eq_configs = [
        (1, 1, [1000]), (1, 1, [500]), (1, 1, [200]), (1, 1, [100]),
        (2, 1, [50, 20]), (2, 1, [40, 25]), (2, 1, [100, 10]),
        (2, 2, [50, 20]), (2, 2, [40, 25]), (2, 2, [100, 10]),
        (3, 1, [10, 10, 10]), (3, 1, [20, 10, 5]),
        (3, 2, [10, 10, 10]), (3, 2, [20, 10, 5]),
        (3, 3, [10, 10, 10]), (3, 3, [20, 10, 5]),
        (4, 1, [5, 5, 5, 8]), (4, 2, [5, 5, 5, 8]),
        (4, 3, [5, 5, 5, 8]), (4, 4, [5, 5, 5, 8]),
    ]
    for i, (gs, js, gr) in enumerate(eq_configs):
        examples.append(make_case_a_equal(eid, f'v{i+1}', gs, js, gr))
        eid += 1

    # ── CASE A: Ordered Grains (25 examples) ──
    ord_ranges = [
        ([50, 20], [1000]),
        ([40, 25], [500]),
        ([100, 10], [200]),
        ([25, 40], [100]),
        ([20, 50], [50]),
        ([200, 5], [1000]),
        ([10, 100], [500]),
        ([30, 30], [200]),
        ([50, 20], [500]),
        ([100, 10], [1000]),
        # Reversed: coarser R1, finer R2 — still Case A
        ([1000], [50, 20]),
        ([500], [40, 25]),
        ([200], [100, 10]),
        ([100], [25, 40]),
        ([50], [20, 50]),
        ([1000], [200, 5]),
        ([500], [10, 100]),
        ([200], [30, 30]),
        ([500], [50, 20]),
        ([1000], [100, 10]),
        ([100], [50, 20]),
        ([200], [40, 25]),
        ([500], [100, 10]),
        ([1000], [200, 5]),
        ([50], [10, 100]),
    ]
    for i, (r1r, r2r) in enumerate(ord_ranges):
        if i < 10:
            # Normal: R1 finer (r1r=multi), R2 coarser (r2r=single)
            examples.append(make_case_a_ordered(eid, f'v{i+1}', r1r, r2r))
        else:
            # Reversed: R1 coarser (r1r=single), R2 finer (r2r=multi)
            # Swap args so g_ranges_fine=r2r (multi) and g_ranges_coarse=r1r (single)
            examples.append(make_case_a_ordered(eid, f'v{i+1}', r2r, r1r, reversed=True))
        eid += 1

    # ── CASE A: Incomparable Grains, comparable Jk-portions (7 examples) ──
    ia_ranges = [
        [10, 10, 10],
        [20, 10, 5],
        [5, 10, 20],
        [10, 20, 5],
        [5, 5, 40],
        [40, 5, 5],
        [10, 10, 10],
    ]
    for i, gr in enumerate(ia_ranges):
        examples.append(make_case_a_incomp(eid, f'v{i+1}', gr))
        eid += 1

    # ── CASE A: Natural Join, comparable Jk-portions (8 examples) ──
    nj_ranges = [
        [50, 20],
        [40, 25],
        [100, 10],
        [25, 40],
        [20, 50],
        [200, 5],
        [10, 100],
        [30, 30],
    ]
    for i, gr in enumerate(nj_ranges):
        examples.append(make_case_a_natjoin(eid, f'v{i+1}', gr))
        eid += 1

    # Verify count
    n_b = sum(1 for e in examples if e.case_type == 'B')
    n_a = sum(1 for e in examples if e.case_type == 'A')
    assert len(examples) == 100, f"Expected 100 examples, got {len(examples)}"
    assert n_b == 27, f"Expected 27 Case B, got {n_b}"
    assert n_a == 73, f"Expected 73 Case A, got {n_a}"

    return examples


# ─── SQL Generation ───────────────────────────────────────────────────────────

def grain_col_gen_expr(col_idx, total_grain, ranges, row_var='i'):
    """Generate SQL expression for a grain column using modular arithmetic.
    Produces unique combinations across all grain columns."""
    if col_idx >= len(ranges):
        return f'(({row_var} * {7 + col_idx * 3}) % 100 + 1)::int'
    r = ranges[col_idx]
    # Each grain column cycles at a different rate
    divisor = 1
    for j in range(col_idx + 1, len(ranges)):
        if j < len(ranges):
            divisor *= ranges[j]
    return f'(({row_var} / {divisor}) % {r} + 1)::int'


def gen_insert_sql(table, cols, grain_cols, grain_ranges, nrows, seed_offset=0):
    """Generate INSERT statement for a table."""
    exprs = []
    for ci, c in enumerate(cols):
        if c in grain_cols:
            gi = grain_cols.index(c)
            exprs.append(grain_col_gen_expr(gi, len(grain_cols), grain_ranges))
        elif c.startswith('v') or c in ('e', 'd'):
            # Non-grain: random (to show non-grain columns don't affect grain)
            exprs.append(f'(random() * 100 + 1)::int')
        else:
            # Non-grain determined by grain (e.g., b in R1 of Case B)
            exprs.append(f'((i * {3 + ci * 7 + seed_offset}) % 47 + 1)::int')
    select_exprs = ', '.join(exprs)
    col_list = ', '.join(cols)
    pk_list = ', '.join(grain_cols)
    # Use ON CONFLICT to handle any duplicate grain combos from modular arithmetic
    return f"""INSERT INTO {{schema}}.{table} ({col_list})
SELECT {select_exprs}
FROM generate_series(1, {nrows}) s(i)
ON CONFLICT ({pk_list}) DO NOTHING;"""


def gen_insert_r2_derived_sql(r1_table, r2_table, ex):
    """Generate R2 INSERT derived from R1 to ensure join matches.
    Jk columns come from R1; R2 grain cols outside Jk come from CROSS JOIN;
    non-grain non-Jk cols are random."""

    r2_grain_outside_jk = [c for c in ex.r2_grain if c not in ex.jk]

    select_parts = []
    for c in ex.r2_cols:
        if c in ex.jk:
            select_parts.append(f'r1.{c}')
        elif c in r2_grain_outside_jk:
            select_parts.append(f's_{c}.{c}')
        else:
            select_parts.append(f'(random() * 100 + 1)::int')

    col_list = ', '.join(ex.r2_cols)
    select_list = ', '.join(select_parts)
    pk_list = ', '.join(ex.r2_grain)

    from_parts = ['{schema}.' + r1_table + ' r1']
    for c in r2_grain_outside_jk:
        gi = ex.r2_grain.index(c)
        r = ex.r2_grain_ranges[gi] if gi < len(ex.r2_grain_ranges) else 20
        from_parts.append(f'    CROSS JOIN generate_series(1, {r}) s_{c}({c})')

    from_clause = '\n'.join(from_parts)

    return f"""INSERT INTO {{schema}}.{r2_table} ({col_list})
SELECT {select_list}
FROM {from_clause}
ORDER BY random()
ON CONFLICT ({pk_list}) DO NOTHING;"""


def gen_result_cols(ex):
    """Determine result columns from the join, handling name clashes."""
    r1_only = [c for c in ex.r1_cols if c not in ex.r2_cols]
    r2_only = [c for c in ex.r2_cols if c not in ex.r1_cols]
    common = [c for c in ex.r1_cols if c in ex.r2_cols]
    # For common cols in the join key, they're equal → keep once
    # For common cols NOT in the join key, keep both with suffix
    result_cols = []
    select_parts = []
    for c in common:
        if c in ex.jk:
            result_cols.append(c)
            select_parts.append(f'r1.{c}')
        else:
            result_cols.append(f'{c}_r1')
            result_cols.append(f'{c}_r2')
            select_parts.append(f'r1.{c} AS {c}_r1')
            select_parts.append(f'r2.{c} AS {c}_r2')
    for c in r1_only:
        result_cols.append(c)
        select_parts.append(f'r1.{c}')
    for c in r2_only:
        result_cols.append(c)
        select_parts.append(f'r2.{c}')
    join_cond = ' AND '.join(f'r1.{c} = r2.{c}' for c in ex.jk)
    return result_cols, select_parts, join_cond


def map_grain_to_result_cols(grain_cols, ex, result_cols):
    """Map grain column names to actual result column names (handling _r1/_r2)."""
    common_not_jk = [c for c in ex.r1_cols if c in ex.r2_cols and c not in ex.jk]
    mapped = []
    for c in grain_cols:
        if c.endswith('_r1') or c.endswith('_r2'):
            mapped.append(c)
        elif c in common_not_jk:
            # Ambiguous common col — check if it's in R1 grain or R2 grain
            if c in ex.r1_grain:
                mapped.append(f'{c}_r1')
            elif c in ex.r2_grain:
                mapped.append(f'{c}_r2')
            else:
                mapped.append(f'{c}_r1')
        elif c in result_cols:
            mapped.append(c)
        else:
            mapped.append(c)
    return mapped


def generate_example_sql(ex, schema='revalidation'):
    """Generate complete SQL for one example."""
    r1_table = f'r1_ex{ex.id}'
    r2_table = f'r2_ex{ex.id}'
    res_table = f'result_ex{ex.id}'

    lines = []
    lines.append(f'-- Example {ex.id}: {ex.desc}')
    lines.append(f'-- Category: {ex.category}, Case: {ex.case_type}')

    # Drop old tables
    lines.append(f'DROP TABLE IF EXISTS {schema}.{r1_table} CASCADE;')
    lines.append(f'DROP TABLE IF EXISTS {schema}.{r2_table} CASCADE;')
    lines.append(f'DROP TABLE IF EXISTS {schema}.{res_table} CASCADE;')

    # Create R1
    r1_col_defs = ', '.join(f'{c} INTEGER' for c in ex.r1_cols)
    r1_pk = ', '.join(ex.r1_grain)
    lines.append(f'CREATE TABLE {schema}.{r1_table} ({r1_col_defs}, PRIMARY KEY ({r1_pk}));')

    # Create R2
    r2_col_defs = ', '.join(f'{c} INTEGER' for c in ex.r2_cols)
    r2_pk = ', '.join(ex.r2_grain)
    lines.append(f'CREATE TABLE {schema}.{r2_table} ({r2_col_defs}, PRIMARY KEY ({r2_pk}));')

    # Insert R1
    insert_r1 = gen_insert_sql(r1_table, ex.r1_cols, ex.r1_grain,
                               ex.r1_grain_ranges, ex.r1_nrows, seed_offset=0)
    lines.append(insert_r1.replace('{schema}', schema))

    # Insert R2 derived from R1 to ensure dense joins
    insert_r2 = gen_insert_r2_derived_sql(r1_table, r2_table, ex)
    lines.append(insert_r2.replace('{schema}', schema))

    # Create result table (no PK) via join
    result_cols, select_parts, join_cond = gen_result_cols(ex)
    select_list = ', '.join(select_parts)
    res_col_defs = ', '.join(f'{c} INTEGER' for c in result_cols)
    lines.append(f'CREATE TABLE {schema}.{res_table} ({res_col_defs});')
    lines.append(f"""INSERT INTO {schema}.{res_table}
SELECT DISTINCT {select_list}
FROM {schema}.{r1_table} r1
INNER JOIN {schema}.{r2_table} r2 ON {join_cond};""")

    # Map grain column names to result column names
    paper_mapped = map_grain_to_result_cols(ex.paper_grain, ex, result_cols)
    corrected_mapped = map_grain_to_result_cols(ex.corrected_grain, ex, result_cols)

    paper_str = ', '.join(paper_mapped)
    corrected_str = ', '.join(corrected_mapped)

    # Test block
    lines.append(f"""
DO $$
DECLARE
    total_rows BIGINT;
    unique_count BIGINT;
    reduced_count BIGINT;
    -- Paper grain
    p_unique BOOLEAN;
    p_minimal BOOLEAN := TRUE;
    p_removable TEXT := '';
    -- Corrected grain
    c_unique BOOLEAN;
    c_minimal BOOLEAN := TRUE;
    c_removable TEXT := '';
    -- Temp
    col_to_remove TEXT;
    reduced_cols TEXT;
    grain_cols TEXT[];
    i INTEGER;
BEGIN
    SELECT COUNT(*) INTO total_rows FROM {schema}.{res_table};

    IF total_rows = 0 THEN
        INSERT INTO {schema}.test_results VALUES (
            {ex.id}, '{ex.category}', '{ex.case_type}', '{ex.desc}',
            0, '{paper_str}', FALSE, FALSE, 'NO DATA',
            '{corrected_str}', FALSE, FALSE, 'NO DATA'
        );
        RAISE NOTICE 'Ex {ex.id}: NO JOIN RESULTS (0 rows)';
        RETURN;
    END IF;

    -- ── Test paper grain: uniqueness ──
    SELECT COUNT(DISTINCT ({paper_str})) INTO unique_count FROM {schema}.{res_table};
    p_unique := (total_rows = unique_count);

    -- ── Test paper grain: minimality ──
    grain_cols := ARRAY[{', '.join(f"'{c}'" for c in paper_mapped)}];
    IF p_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM {schema}.{res_table}', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                p_minimal := FALSE;
                IF p_removable != '' THEN p_removable := p_removable || ', '; END IF;
                p_removable := p_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    -- ── Test corrected grain: uniqueness ──
    SELECT COUNT(DISTINCT ({corrected_str})) INTO unique_count FROM {schema}.{res_table};
    c_unique := (total_rows = unique_count);

    -- ── Test corrected grain: minimality ──
    grain_cols := ARRAY[{', '.join(f"'{c}'" for c in corrected_mapped)}];
    IF c_unique AND array_length(grain_cols, 1) > 1 THEN
        FOR i IN 1..array_length(grain_cols, 1) LOOP
            reduced_cols := '';
            FOR j IN 1..array_length(grain_cols, 1) LOOP
                IF j != i THEN
                    IF reduced_cols != '' THEN reduced_cols := reduced_cols || ', '; END IF;
                    reduced_cols := reduced_cols || grain_cols[j];
                END IF;
            END LOOP;
            EXECUTE format('SELECT COUNT(DISTINCT (%s)) FROM {schema}.{res_table}', reduced_cols)
                INTO reduced_count;
            IF reduced_count = total_rows THEN
                c_minimal := FALSE;
                IF c_removable != '' THEN c_removable := c_removable || ', '; END IF;
                c_removable := c_removable || grain_cols[i];
            END IF;
        END LOOP;
    END IF;

    IF p_removable = '' THEN p_removable := '-'; END IF;
    IF c_removable = '' THEN c_removable := '-'; END IF;

    INSERT INTO {schema}.test_results VALUES (
        {ex.id}, '{ex.category}', '{ex.case_type}', '{ex.desc}',
        total_rows, '{paper_str}', p_unique, p_minimal, p_removable,
        '{corrected_str}', c_unique, c_minimal, c_removable
    );

    RAISE NOTICE 'Ex %: rows=% | paper(%): uniq=% min=% rem=% | corrected(%): uniq=% min=%',
        {ex.id}, total_rows,
        '{paper_str}', p_unique, p_minimal, p_removable,
        '{corrected_str}', c_unique, c_minimal;

EXCEPTION WHEN OTHERS THEN
    INSERT INTO {schema}.test_results VALUES (
        {ex.id}, '{ex.category}', '{ex.case_type}', '{ex.desc}',
        -1, '{paper_str}', FALSE, FALSE, 'ERROR: ' || SQLERRM,
        '{corrected_str}', FALSE, FALSE, 'ERROR: ' || SQLERRM
    );
    RAISE NOTICE 'Ex %: ERROR - %', {ex.id}, SQLERRM;
END $$;
""")

    return '\n'.join(lines)


def generate_full_sql(examples):
    """Generate the complete SQL file."""
    parts = []

    parts.append("""-- ==========================================================================
-- Grain Formula Revalidation: Paper vs Corrected Formula (100 Examples)
-- ==========================================================================
--
-- Tests Theorem 6.1 from the PODS 2027 paper against the corrected formula.
-- For each example:
--   1. Paper grain tested for uniqueness and minimality
--   2. Corrected grain tested for uniqueness and minimality
--
-- Expected: paper formula fails minimality on Case B examples (27/100);
--           corrected formula passes both uniqueness and minimality on all 100.
-- ==========================================================================

CREATE SCHEMA IF NOT EXISTS revalidation;
SET search_path TO revalidation, public;
SELECT setseed(0.42);  -- reproducible random values

DROP TABLE IF EXISTS revalidation.test_results CASCADE;
CREATE TABLE revalidation.test_results (
    example_id      INTEGER,
    category        TEXT,
    case_type       CHAR(1),
    description     TEXT,
    result_rows     BIGINT,
    paper_grain     TEXT,
    paper_unique    BOOLEAN,
    paper_minimal   BOOLEAN,
    paper_removable TEXT,
    corrected_grain TEXT,
    corrected_unique  BOOLEAN,
    corrected_minimal BOOLEAN,
    corrected_removable TEXT DEFAULT '-'
);

\\echo '========================================================'
\\echo 'Grain Formula Revalidation — 100 Examples'
\\echo '========================================================'
\\echo ''
""")

    # Group examples by category for nice output
    categories = {}
    for ex in examples:
        categories.setdefault(ex.category, []).append(ex)

    for cat, exs in categories.items():
        parts.append(f"\\echo '── {cat} ({len(exs)} examples) ──'")
        for ex in exs:
            parts.append(generate_example_sql(ex))
        parts.append('')

    # Summary report
    parts.append("""
\\echo ''
\\echo '========================================================'
\\echo 'SUMMARY REPORT'
\\echo '========================================================'
\\echo ''

-- Overall summary
DO $$
DECLARE
    total INTEGER;
    case_a INTEGER;
    case_b INTEGER;
    paper_uniq_pass INTEGER;
    paper_min_pass INTEGER;
    paper_min_fail INTEGER;
    corr_uniq_pass INTEGER;
    corr_min_pass INTEGER;
    no_data INTEGER;
    errors INTEGER;
BEGIN
    SELECT COUNT(*) INTO total FROM revalidation.test_results;
    SELECT COUNT(*) INTO case_a FROM revalidation.test_results WHERE case_type = 'A';
    SELECT COUNT(*) INTO case_b FROM revalidation.test_results WHERE case_type = 'B';
    SELECT COUNT(*) INTO no_data FROM revalidation.test_results WHERE result_rows = 0;
    SELECT COUNT(*) INTO errors FROM revalidation.test_results WHERE result_rows < 0;

    SELECT COUNT(*) INTO paper_uniq_pass FROM revalidation.test_results
        WHERE paper_unique = TRUE AND result_rows > 0;
    SELECT COUNT(*) INTO paper_min_pass FROM revalidation.test_results
        WHERE paper_minimal = TRUE AND result_rows > 0;
    SELECT COUNT(*) INTO paper_min_fail FROM revalidation.test_results
        WHERE paper_minimal = FALSE AND paper_unique = TRUE AND result_rows > 0;

    SELECT COUNT(*) INTO corr_uniq_pass FROM revalidation.test_results
        WHERE corrected_unique = TRUE AND result_rows > 0;
    SELECT COUNT(*) INTO corr_min_pass FROM revalidation.test_results
        WHERE corrected_minimal = TRUE AND result_rows > 0;

    RAISE NOTICE '';
    RAISE NOTICE 'Total examples:        %', total;
    RAISE NOTICE '  Case A:              %', case_a;
    RAISE NOTICE '  Case B:              %', case_b;
    RAISE NOTICE '  No data (0 rows):    %', no_data;
    RAISE NOTICE '  Errors:              %', errors;
    RAISE NOTICE '';
    RAISE NOTICE '── PAPER FORMULA (Theorem 6.1) ──';
    RAISE NOTICE '  Uniqueness pass:     %/%', paper_uniq_pass, total - no_data - errors;
    RAISE NOTICE '  Minimality pass:     %/%', paper_min_pass, total - no_data - errors;
    RAISE NOTICE '  Minimality FAIL:     %  (all should be Case B)', paper_min_fail;
    RAISE NOTICE '';
    RAISE NOTICE '── CORRECTED FORMULA ──';
    RAISE NOTICE '  Uniqueness pass:     %/%', corr_uniq_pass, total - no_data - errors;
    RAISE NOTICE '  Minimality pass:     %/%', corr_min_pass, total - no_data - errors;
    RAISE NOTICE '';

    IF paper_min_fail = case_b AND corr_min_pass = (total - no_data - errors) THEN
        RAISE NOTICE '✓ VALIDATION CONFIRMED:';
        RAISE NOTICE '  Paper formula fails minimality on ALL % Case B examples', case_b;
        RAISE NOTICE '  Corrected formula passes uniqueness + minimality on ALL % examples', corr_min_pass;
    ELSE
        RAISE NOTICE '⚠ UNEXPECTED RESULTS — review details below';
    END IF;
END $$;

-- Detailed results: Case B failures
\\echo ''
\\echo '── Case B: Paper formula minimality failures ──'
SELECT example_id, description, result_rows,
       paper_grain, paper_removable,
       corrected_grain
FROM revalidation.test_results
WHERE case_type = 'B' AND result_rows > 0
ORDER BY example_id;

-- Detailed results: any unexpected failures
\\echo ''
\\echo '── Any unexpected results (errors, Case A minimality failures, etc.) ──'
SELECT example_id, category, case_type, description, result_rows,
       paper_grain, paper_unique, paper_minimal, paper_removable,
       corrected_grain, corrected_unique, corrected_minimal
FROM revalidation.test_results
WHERE result_rows <= 0
   OR (case_type = 'A' AND (paper_minimal = FALSE OR corrected_minimal = FALSE))
   OR corrected_unique = FALSE
   OR corrected_minimal = FALSE
ORDER BY example_id;

\\echo ''
\\echo '========================================================'
\\echo 'Revalidation Complete'
\\echo '========================================================'
""")

    return '\n'.join(parts)


# ─── Main ─────────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    examples = build_examples()
    sql = generate_full_sql(examples)
    print(sql)
