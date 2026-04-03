"""
FD-respecting data generation for equi-join PBT.

Generates R1 and R2 tables satisfying:
  - Grain columns form a key (unique per row, FD: G[Ri] → Ri)
  - Join keys overlap between R1 and R2 (non-empty join results)
  - Deterministic given seed
"""

import random
from typing import Dict, List, Tuple

from config import Config


def generate_data(
    config: Config,
    n_rows: int = 20,
    distribution: str = "uniform",
    seed: int = 42,
) -> Tuple[List[Dict[str, int]], List[Dict[str, int]]]:
    """Generate FD-respecting data for R1 and R2 with guaranteed join overlap.

    Args:
        config: Equi-join configuration.
        n_rows: Number of rows per table (>= 1).
        distribution: One of "uniform", "skewed", "extreme_low", "extreme_high".
        seed: Random seed for reproducibility.

    Returns:
        (r1_rows, r2_rows) as lists of column-name → int-value dicts.

    Guarantees:
        - Each table has exactly n_rows rows.
        - Grain tuples are unique per table (FD: G → R).
        - At least one R1/R2 row pair shares all Jk values (non-empty join).
    """
    if n_rows < 1:
        raise ValueError("n_rows must be >= 1")

    rng = random.Random(seed)
    jk_list = list(config.jk)

    # Shared Jk pool — both tables draw from it, guaranteeing overlap.
    jk_pool = _make_jk_pool(len(jk_list), n_rows, rng)

    r1_rows = _build_table(
        rng, config, jk_list, jk_pool, n_rows, distribution, is_r1=True
    )
    r2_rows = _build_table(
        rng, config, jk_list, jk_pool, n_rows, distribution, is_r1=False
    )

    return r1_rows, r2_rows


# ---------------------------------------------------------------------------
# Jk pool
# ---------------------------------------------------------------------------

def _make_jk_pool(n_jk: int, size: int, rng: random.Random) -> List[tuple]:
    """Generate ``size`` distinct Jk-value tuples.

    Uses strictly-increasing per-column values so that ANY column-subset
    projection is also distinct.  This guarantees grain uniqueness even
    when g_rest is empty, regardless of which Jk columns are in the grain.

    The pool is shuffled (deterministically via *rng*) so that different
    seeds produce different Jk assignments.
    """
    if n_jk == 0:
        return [() for _ in range(size)]
    pool = [tuple(i * n_jk + j + 1 for j in range(n_jk)) for i in range(size)]
    rng.shuffle(pool)
    return pool


# ---------------------------------------------------------------------------
# Table builder
# ---------------------------------------------------------------------------

def _build_table(
    rng: random.Random,
    config: Config,
    jk_list: List[str],
    jk_pool: List[tuple],
    n_rows: int,
    distribution: str,
    is_r1: bool,
) -> List[Dict[str, int]]:
    """Build table rows with distinct grain tuples and controlled Jk values.

    Strategy:
      1. Assign Jk values from the shared pool (controls join fan-out).
      2. Generate grain-rest column values via rng (with retry for uniqueness).
      3. Derive non-grain, non-Jk columns from the grain tuple (hash-based FD).
    """
    fields = list(config.r1_fields if is_r1 else config.r2_fields)
    grain = list(config.g1 if is_r1 else config.g2)
    grain_rest = list(config.g1_rest if is_r1 else config.g2_rest)
    tag = "r1" if is_r1 else "r2"

    has_rest = len(grain_rest) > 0

    # How many distinct Jk tuples to cycle through.
    # When g_rest is empty, grain = g_jk, so each row needs a unique Jk entry.
    n_jk_used = _jk_fan_count(n_rows, distribution) if has_rest else n_rows

    rows = []
    grain_seen = set()
    max_rest_val = n_rows * 20  # ample range to avoid grain collisions

    for i in range(n_rows):
        row = {}

        # 1. Assign Jk values from pool
        if has_rest:
            jk_idx = _jk_index(rng, i, n_jk_used, distribution)
        else:
            jk_idx = i  # sequential — grain = g_jk, must be unique
        jk_tuple = jk_pool[jk_idx]
        for j, col in enumerate(jk_list):
            row[col] = jk_tuple[j]

        # 2. Generate grain-rest values (ensure grain uniqueness)
        if has_rest:
            attempts = 0
            while True:
                for col in grain_rest:
                    row[col] = rng.randint(1, max_rest_val)
                g_tuple = tuple(row[c] for c in grain)
                if g_tuple not in grain_seen:
                    grain_seen.add(g_tuple)
                    break
                attempts += 1
                if attempts > 10_000:
                    raise RuntimeError(
                        f"Cannot generate distinct grain tuple after 10 000 attempts "
                        f"(grain={grain}, rest={grain_rest}, seen={len(grain_seen)})"
                    )
        else:
            g_tuple = tuple(row[c] for c in grain)
            grain_seen.add(g_tuple)

        # 3. Derive non-grain columns from grain (FD: G → R)
        for col in fields:
            if col not in row:
                row[col] = hash((tag, col, g_tuple)) % 1000

        rows.append(row)

    return rows


# ---------------------------------------------------------------------------
# Distribution helpers
# ---------------------------------------------------------------------------

def _jk_fan_count(n_rows: int, distribution: str) -> int:
    """How many distinct Jk tuples to use (controls join fan-out).

    Lower count → more Jk reuse → higher fan-out in the join.
    """
    if distribution == "extreme_low":
        return max(1, n_rows // 5)
    elif distribution == "extreme_high":
        return n_rows
    elif distribution == "skewed":
        return max(2, n_rows // 3)
    else:  # uniform
        return max(2, n_rows // 2)


def _jk_index(rng: random.Random, row_idx: int, n_jk_used: int,
              distribution: str) -> int:
    """Pick a Jk-pool index for this row.

    Row 0 always gets index 0 — since both R1 and R2 start at 0,
    this guarantees at least one matching Jk tuple (non-empty join).
    """
    if row_idx == 0:
        return 0
    if distribution == "skewed":
        return _zipf_index(rng, n_jk_used)
    return row_idx % n_jk_used


def _zipf_index(rng: random.Random, n: int) -> int:
    """Draw an index from 0..n-1 with Zipf(s=1) distribution."""
    weights = [1.0 / (k + 1) for k in range(n)]
    total = sum(weights)
    r = rng.random() * total
    cum = 0.0
    for k in range(n):
        cum += weights[k]
        if r <= cum:
            return k
    return n - 1
