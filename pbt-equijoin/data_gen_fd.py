"""
Data generation that enforces a declared functional dependency (Mode D).

Builds on ``data_gen.generate_data``: both inputs keep their grain as a key
and share join-key values so the join is non-empty, and in addition the
declared dependency ``U -> v`` of an ``FDConfig`` holds on the data.

* ``within`` dependencies (``U`` and ``v`` in one input) are enforced while
  that input is generated: ``v`` is computed from the ``U`` values of the row.
* ``cross`` dependencies (``U`` spans both inputs, ``v`` in R2) are realized
  through the join key: R1 is generated with one row per join-key tuple, so
  that the R1-side fields of ``U`` are a function of the join key, and ``v``
  in R2 is computed from those fields (looked up by the row's join key) and
  the R2-side fields of ``U``. On the join result ``U -> v`` then holds.

The grain of each input stays a key of that input: rows are regenerated
until the grain tuple is new, and when the declared dependency leaves no
free field in the grain, the input is generated with one row per join-key
tuple, which keeps the grain unique.
"""

import random
from typing import Dict, List, Tuple

from config import Config
from fd_config import FDConfig
from data_gen import _make_jk_pool, _jk_fan_count, _jk_index

_FD_MODULUS = 1_000_003


def _fd_value(tag: str, rhs: str, lhs_values: tuple) -> int:
    """The value a declared dependency assigns to ``rhs`` for given determinant values."""
    return hash((tag, "fd", rhs, lhs_values)) % _FD_MODULUS


def generate_data_fd(
    fdc: FDConfig,
    n_rows: int = 30,
    distribution: str = "uniform",
    seed: int = 42,
) -> Tuple[List[Dict[str, int]], List[Dict[str, int]]]:
    """Generate R1 and R2 rows satisfying the grains, the join overlap and the dependency."""
    if n_rows < 1:
        raise ValueError("n_rows must be >= 1")
    config = fdc.config
    fd = fdc.fd
    rng = random.Random(seed)
    jk_list = list(config.jk)
    jk_pool = _make_jk_pool(len(jk_list), n_rows, rng)

    if fd.kind == "cross":
        # R1 with one row per join-key tuple: the join key determines R1.
        u1 = {c for c in fd.lhs if c in config.r1_fields and c not in jk_list}
        r1_rows = _build_table_fd(rng, config, jk_list, jk_pool, n_rows,
                                  distribution, is_r1=True, fd=None,
                                  distinct_jk=True, distinct_fields=u1)
        r1_by_jk = {tuple(r[c] for c in jk_list): r for r in r1_rows}
        r2_rows = _build_table_fd(rng, config, jk_list, jk_pool, n_rows,
                                  distribution, is_r1=False, fd=fd,
                                  distinct_jk=False, r1_by_jk=r1_by_jk)
        return r1_rows, r2_rows

    # within: enforce on the target's input
    r1_rows = _build_table_fd(rng, config, jk_list, jk_pool, n_rows, distribution,
                              is_r1=True, fd=fd if fd.target_input == 1 else None)
    r2_rows = _build_table_fd(rng, config, jk_list, jk_pool, n_rows, distribution,
                              is_r1=False, fd=fd if fd.target_input == 2 else None)
    return r1_rows, r2_rows


def _build_table_fd(
    rng: random.Random,
    config: Config,
    jk_list: List[str],
    jk_pool: List[tuple],
    n_rows: int,
    distribution: str,
    is_r1: bool,
    fd,
    distinct_jk: bool = False,
    r1_by_jk: Dict[tuple, Dict[str, int]] = None,
    distinct_fields=frozenset(),
) -> List[Dict[str, int]]:
    """``distinct_fields``: fields given one value per row (used for the R1
    side of a cross dependency, so that the join key determines them and
    they determine the target injectively enough for the R2 grain to stay
    a key)."""
    fields = list(config.r1_fields if is_r1 else config.r2_fields)
    grain = list(config.g1 if is_r1 else config.g2)
    grain_rest = list(config.g1_rest if is_r1 else config.g2_rest)
    tag = "r1" if is_r1 else "r2"
    target = fd.rhs if fd is not None else None
    lhs = list(fd.lhs) if fd is not None else []
    # Fields of this input that the dependency reads but that are neither
    # join-key nor grain fields: they must exist before the target is set.
    own_set = set(fields)
    lhs_own_nongrain = [c for c in lhs if c in own_set and c not in grain
                        and c not in jk_list]
    free_rest = [c for c in grain_rest if c != target]

    def try_build(use_distinct_jk: bool):
        n_jk_used = n_rows if use_distinct_jk or not free_rest else \
            _jk_fan_count(n_rows, distribution)
        rows = []
        seen = set()
        # A small value domain for the free grain fields, so that rows collide
        # on single columns and minimality (D6) can be observed rather than
        # left inconclusive; the retry loop and the distinct-join-key fallback
        # keep the grain a key.
        max_val = max(4, n_rows // 4)
        for i in range(n_rows):
            row = {}
            jk_idx = i if (use_distinct_jk or not free_rest) else \
                _jk_index(rng, i, n_jk_used, distribution)
            jk_tuple = jk_pool[jk_idx]
            for j, col in enumerate(jk_list):
                row[col] = jk_tuple[j]
            attempts = 0
            while True:
                for col in free_rest:
                    row[col] = (max_val + i + 1) if col in distinct_fields \
                        else rng.randint(1, max_val)
                for col in lhs_own_nongrain:
                    row[col] = rng.randint(1, max_val)
                if target is not None:
                    lhs_vals = []
                    for c in lhs:
                        if c in row:
                            lhs_vals.append(row[c])
                        else:
                            # cross: an R1-side field, looked up through the join key
                            r1_row = r1_by_jk.get(jk_tuple) if r1_by_jk else None
                            lhs_vals.append(r1_row[c] if r1_row is not None else -1)
                    row[target] = _fd_value(tag, target, tuple(lhs_vals))
                g_tuple = tuple(row[c] for c in grain)
                if g_tuple not in seen:
                    seen.add(g_tuple)
                    break
                attempts += 1
                if attempts > 200:
                    return None
            for col in fields:
                if col not in row:
                    row[col] = hash((tag, col, g_tuple)) % 1000
            rows.append(row)
        return rows

    rows = try_build(distinct_jk)
    if rows is None and not distinct_jk:
        rows = try_build(True)
    if rows is None:
        raise RuntimeError(
            f"Cannot realize grain {grain} as a key together with {fd} on {tag}")
    return rows
