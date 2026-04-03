"""
Tests for FD-respecting data generation.

Verifies:
  1. Grain tuples are unique per table (FD compliance)
  2. All expected columns present in every row
  3. R1/R2 share Jk values (non-empty join guarantee)
  4. All 4 distributions produce valid data
  5. Deterministic given seed
"""

from hypothesis import given, settings

from config import Config, make_config
from generators import equijoin_config
from data_gen import generate_data


DISTRIBUTIONS = ("uniform", "skewed", "extreme_low", "extreme_high")


# ---------- Grain uniqueness (FD compliance) ----------

@given(config=equijoin_config(max_jk=4, max_r_only=3))
@settings(max_examples=200)
def test_grain_uniqueness(config: Config):
    """Grain tuples are distinct in each table for all distributions."""
    for dist in DISTRIBUTIONS:
        r1, r2 = generate_data(config, n_rows=10, distribution=dist)

        g1_tuples = [tuple(row[c] for c in config.g1) for row in r1]
        g2_tuples = [tuple(row[c] for c in config.g2) for row in r2]

        assert len(set(g1_tuples)) == 10, (
            f"R1 grain not unique with {dist}: {len(set(g1_tuples))}/10"
        )
        assert len(set(g2_tuples)) == 10, (
            f"R2 grain not unique with {dist}: {len(set(g2_tuples))}/10"
        )


# ---------- Join-key overlap ----------

@given(config=equijoin_config(max_jk=4, max_r_only=3))
@settings(max_examples=200)
def test_jk_overlap(config: Config):
    """At least one Jk-value tuple appears in both R1 and R2."""
    for dist in DISTRIBUTIONS:
        r1, r2 = generate_data(config, n_rows=10, distribution=dist)

        jk = list(config.jk)
        r1_jk = {tuple(row[c] for c in jk) for row in r1}
        r2_jk = {tuple(row[c] for c in jk) for row in r2}

        assert r1_jk & r2_jk, f"No Jk overlap with {dist}"


# ---------- Column coverage ----------

@given(config=equijoin_config(max_jk=4, max_r_only=3))
@settings(max_examples=200)
def test_column_coverage(config: Config):
    """Every row contains exactly the expected columns."""
    r1, r2 = generate_data(config, n_rows=5)

    for row in r1:
        assert set(row.keys()) == set(config.r1_fields), (
            f"R1 columns mismatch: {sorted(row.keys())} vs {sorted(config.r1_fields)}"
        )
    for row in r2:
        assert set(row.keys()) == set(config.r2_fields), (
            f"R2 columns mismatch: {sorted(row.keys())} vs {sorted(config.r2_fields)}"
        )


# ---------- Row count ----------

@given(config=equijoin_config(max_jk=4, max_r_only=3))
@settings(max_examples=50)
def test_row_count(config: Config):
    """Each table has exactly n_rows rows."""
    for n in (1, 5, 20):
        r1, r2 = generate_data(config, n_rows=n)
        assert len(r1) == n, f"R1 has {len(r1)} rows, expected {n}"
        assert len(r2) == n, f"R2 has {len(r2)} rows, expected {n}"


# ---------- Determinism ----------

def test_deterministic():
    """Same config + seed produces identical data."""
    cfg = make_config(
        ["a0", "j0", "j1"], ["j0", "j1", "b0"], ["j0", "j1"],
        ["a0", "j0"], ["j1", "b0"],
    )

    r1a, r2a = generate_data(cfg, n_rows=10, seed=99)
    r1b, r2b = generate_data(cfg, n_rows=10, seed=99)
    assert r1a == r1b
    assert r2a == r2b


def test_different_seeds():
    """Different seeds produce different data."""
    cfg = make_config(
        ["a0", "j0", "j1"], ["j0", "j1", "b0"], ["j0", "j1"],
        ["a0", "j0"], ["j1", "b0"],
    )

    r1a, _ = generate_data(cfg, n_rows=10, seed=1)
    r1b, _ = generate_data(cfg, n_rows=10, seed=2)
    assert r1a != r1b


# ---------- All distributions ----------

def test_all_distributions_valid():
    """All 4 distributions produce structurally valid data for a fixed config."""
    cfg = make_config(
        ["a0", "a1", "j0", "j1"],
        ["j0", "j1", "b0", "b1"],
        ["j0", "j1"],
        ["a0", "j0"],
        ["j1", "b0"],
    )

    for dist in DISTRIBUTIONS:
        r1, r2 = generate_data(cfg, n_rows=20, distribution=dist)

        # Correct row count
        assert len(r1) == 20, f"{dist}: R1 has {len(r1)} rows"
        assert len(r2) == 20, f"{dist}: R2 has {len(r2)} rows"

        # Grain unique
        g1 = {tuple(row[c] for c in cfg.g1) for row in r1}
        g2 = {tuple(row[c] for c in cfg.g2) for row in r2}
        assert len(g1) == 20, f"{dist}: R1 grain not unique ({len(g1)}/20)"
        assert len(g2) == 20, f"{dist}: R2 grain not unique ({len(g2)}/20)"

        # Jk overlap
        jk = list(cfg.jk)
        r1_jk = {tuple(row[c] for c in jk) for row in r1}
        r2_jk = {tuple(row[c] for c in jk) for row in r2}
        assert r1_jk & r2_jk, f"{dist}: no Jk overlap"


# ---------- Edge cases ----------

def test_single_row():
    """n_rows=1 works and produces a non-empty join."""
    cfg = make_config(["j0"], ["j0", "b0"], ["j0"], ["j0"], ["j0"])

    r1, r2 = generate_data(cfg, n_rows=1)
    assert len(r1) == 1
    assert len(r2) == 1
    assert r1[0]["j0"] == r2[0]["j0"]  # Jk overlap guaranteed


def test_no_rest_columns():
    """Config where g_rest is empty for both tables."""
    cfg = make_config(["j0", "j1"], ["j0", "j1"], ["j0", "j1"],
                      ["j0", "j1"], ["j0", "j1"])

    r1, r2 = generate_data(cfg, n_rows=10)

    g1 = {tuple(row[c] for c in cfg.g1) for row in r1}
    g2 = {tuple(row[c] for c in cfg.g2) for row in r2}
    assert len(g1) == 10
    assert len(g2) == 10


def test_many_rest_columns():
    """Config with several non-Jk grain columns."""
    cfg = make_config(
        ["a0", "a1", "a2", "j0"], ["j0", "b0", "b1", "b2"],
        ["j0"], ["a0", "a1", "a2", "j0"], ["j0", "b0", "b1", "b2"],
    )

    r1, r2 = generate_data(cfg, n_rows=15, distribution="skewed")

    g1 = {tuple(row[c] for c in cfg.g1) for row in r1}
    g2 = {tuple(row[c] for c in cfg.g2) for row in r2}
    assert len(g1) == 15
    assert len(g2) == 15
