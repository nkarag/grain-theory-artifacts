"""
Hand-crafted edge case configurations for Mode C boundary testing.

Each function returns a Config representing a specific boundary condition
of the equi-join grain inference theorem.  These 16 cases target structural
extremes that random generation is unlikely to produce with high frequency.
"""

from config import Config, make_config


# ---------------------------------------------------------------------------
# Case 1: G[Ri] entirely inside join key  (G_rest = empty)
# ---------------------------------------------------------------------------

def case_01_grain_inside_jk() -> Config:
    """G[R1] is a subset of Jk -- no rest columns in the grain."""
    return make_config(
        r1_fields=["j0", "j1", "a0", "a1"],
        r2_fields=["j0", "j1", "b0"],
        jk=["j0", "j1"],
        g1=["j0"],          # grain entirely in Jk
        g2=["j0", "b0"],    # grain spans Jk and private
    )


# ---------------------------------------------------------------------------
# Case 2: G[Ri] entirely outside join key  (G_jk = empty)
# ---------------------------------------------------------------------------

def case_02_grain_outside_jk() -> Config:
    """G[R1] has no intersection with Jk."""
    return make_config(
        r1_fields=["j0", "a0", "a1"],
        r2_fields=["j0", "b0"],
        jk=["j0"],
        g1=["a0", "a1"],   # grain entirely outside Jk
        g2=["j0", "b0"],
    )


# ---------------------------------------------------------------------------
# Case 3: G[R1] = R1 (grain equals the full type)
# ---------------------------------------------------------------------------

def case_03_grain_is_full_type() -> Config:
    """Grain of R1 is the entire relation -- no non-grain columns."""
    return make_config(
        r1_fields=["j0", "j1", "a0"],
        r2_fields=["j0", "j1", "b0"],
        jk=["j0", "j1"],
        g1=["j0", "j1", "a0"],  # grain = all of R1
        g2=["j0", "b0"],
    )


# ---------------------------------------------------------------------------
# Case 4: |G[Ri]| = 1 (single-field grain)
# ---------------------------------------------------------------------------

def case_04_single_field_grain() -> Config:
    """Both grains are single-column."""
    return make_config(
        r1_fields=["j0", "j1", "a0"],
        r2_fields=["j0", "j1", "b0"],
        jk=["j0", "j1"],
        g1=["a0"],   # single field, outside Jk
        g2=["b0"],   # single field, outside Jk
    )


# ---------------------------------------------------------------------------
# Case 5: Natural join (Jk = R1 intersection R2, maximum overlap)
# ---------------------------------------------------------------------------

def case_05_natural_join() -> Config:
    """All shared columns are join key columns (natural join)."""
    return make_config(
        r1_fields=["j0", "j1", "j2", "a0"],
        r2_fields=["j0", "j1", "j2", "b0"],
        jk=["j0", "j1", "j2"],
        g1=["j0", "j1", "a0"],
        g2=["j0", "j2", "b0"],
    )


# ---------------------------------------------------------------------------
# Case 6: |Jk| = 1 (single-field join key)
# ---------------------------------------------------------------------------

def case_06_single_field_jk() -> Config:
    """Minimal join key: a single column."""
    return make_config(
        r1_fields=["j0", "a0", "a1"],
        r2_fields=["j0", "b0", "b1"],
        jk=["j0"],
        g1=["j0", "a0"],
        g2=["j0", "b0"],
    )


# ---------------------------------------------------------------------------
# Case 7: G1^Jk and G2^Jk differ by exactly 1 field
# ---------------------------------------------------------------------------

def case_07_jk_portions_differ_by_one() -> Config:
    """Jk-grain-portions are proper subset, differing by exactly one field."""
    return make_config(
        r1_fields=["j0", "j1", "j2", "a0"],
        r2_fields=["j0", "j1", "j2", "b0"],
        jk=["j0", "j1", "j2"],
        g1=["j0", "a0"],          # G1^Jk = {j0}
        g2=["j0", "j1", "b0"],    # G2^Jk = {j0, j1}  -- differs by j1
    )


# ---------------------------------------------------------------------------
# Case 8: Self-join (R1 = R2, identical schemas)
# ---------------------------------------------------------------------------

def case_08_self_join() -> Config:
    """Self-join: R1 and R2 have identical schemas, equal grains."""
    # For a valid config, R1 and R2 must share Jk columns.
    # Private columns get _r1/_r2 suffixes in the result, so we
    # use distinct private-column names (a0 vs b0) to avoid ambiguity
    # in the result table, but the schemas are structurally identical
    # (same number & role of columns).
    return make_config(
        r1_fields=["j0", "j1", "a0"],
        r2_fields=["j0", "j1", "b0"],
        jk=["j0", "j1"],
        g1=["j0", "a0"],
        g2=["j0", "b0"],   # symmetric structure
    )


# ---------------------------------------------------------------------------
# Case 9: G[Ri] inside Jk for BOTH inputs
# ---------------------------------------------------------------------------

def case_09_both_grains_inside_jk() -> Config:
    """Both grains are entirely within the join key."""
    return make_config(
        r1_fields=["j0", "j1", "j2", "a0"],
        r2_fields=["j0", "j1", "j2", "b0"],
        jk=["j0", "j1", "j2"],
        g1=["j0", "j1"],       # entirely in Jk
        g2=["j0", "j1", "j2"], # entirely in Jk
    )


# ---------------------------------------------------------------------------
# Case 10: Large |Jk_nongrain| (many non-grain join fields)
# ---------------------------------------------------------------------------

def case_10_large_jk_nongrain() -> Config:
    """Many join key fields that are NOT part of either grain."""
    return make_config(
        r1_fields=["j0", "j1", "j2", "j3", "j4", "a0"],
        r2_fields=["j0", "j1", "j2", "j3", "j4", "b0"],
        jk=["j0", "j1", "j2", "j3", "j4"],
        g1=["j0", "a0"],    # only j0 from Jk
        g2=["j0", "b0"],    # only j0 from Jk -- j1..j4 are non-grain Jk
    )


# ---------------------------------------------------------------------------
# Case 11: G1^Jk = G2^Jk but G1_rest != G2_rest
# ---------------------------------------------------------------------------

def case_11_equal_jk_different_rest() -> Config:
    """Jk-portions are equal, but rest portions differ in content."""
    return make_config(
        r1_fields=["j0", "j1", "a0", "a1"],
        r2_fields=["j0", "j1", "b0"],
        jk=["j0", "j1"],
        g1=["j0", "a0", "a1"],   # G1^Jk = {j0}, G1_rest = {a0, a1}
        g2=["j0", "b0"],         # G2^Jk = {j0}, G2_rest = {b0}
    )


# ---------------------------------------------------------------------------
# Case 12: G[R1] = Jk and G[R2] has no Jk (extreme asymmetry)
# ---------------------------------------------------------------------------

def case_12_extreme_asymmetry() -> Config:
    """R1's grain is exactly Jk; R2's grain is entirely outside Jk."""
    return make_config(
        r1_fields=["j0", "j1", "a0"],
        r2_fields=["j0", "j1", "b0", "b1"],
        jk=["j0", "j1"],
        g1=["j0", "j1"],       # G1 = Jk
        g2=["b0", "b1"],       # G2 has no Jk overlap
    )


# ---------------------------------------------------------------------------
# Case 13: |R1| = 1, |R2| large (size imbalance)
# ---------------------------------------------------------------------------

def case_13_size_imbalance() -> Config:
    """R1 has a single column (= Jk), R2 has many columns."""
    return make_config(
        r1_fields=["j0"],
        r2_fields=["j0", "b0", "b1", "b2", "b3"],
        jk=["j0"],
        g1=["j0"],               # single-column R1, grain = R1
        g2=["j0", "b0", "b1"],
    )


# ---------------------------------------------------------------------------
# Case 14: G[R1] and G[R2] are disjoint (no shared grain fields)
# ---------------------------------------------------------------------------

def case_14_disjoint_grains() -> Config:
    """Grains share no fields at all."""
    return make_config(
        r1_fields=["j0", "j1", "a0"],
        r2_fields=["j0", "j1", "b0"],
        jk=["j0", "j1"],
        g1=["j0", "a0"],    # grain uses j0
        g2=["j1", "b0"],    # grain uses j1 -- no overlap with g1
    )


# ---------------------------------------------------------------------------
# Case 15: G[R1] = G[R2] (identical grains, same column names)
# ---------------------------------------------------------------------------

def case_15_identical_grains() -> Config:
    """Both grains are identical (same Jk columns, no rest)."""
    return make_config(
        r1_fields=["j0", "j1", "a0"],
        r2_fields=["j0", "j1", "b0"],
        jk=["j0", "j1"],
        g1=["j0", "j1"],    # grain = {j0, j1}
        g2=["j0", "j1"],    # grain = {j0, j1} -- identical
    )


# ---------------------------------------------------------------------------
# Case 16: Jk = R1 = R2 (everything is join key, no private columns)
# ---------------------------------------------------------------------------

def case_16_everything_is_jk() -> Config:
    """Degenerate: all columns are join key columns, no private columns."""
    return make_config(
        r1_fields=["j0", "j1"],
        r2_fields=["j0", "j1"],
        jk=["j0", "j1"],
        g1=["j0", "j1"],    # grain = all cols = Jk
        g2=["j0", "j1"],    # grain = all cols = Jk
    )


# ---------------------------------------------------------------------------
# Registry
# ---------------------------------------------------------------------------

ALL_EDGE_CASES = [
    ("01_grain_inside_jk",           case_01_grain_inside_jk),
    ("02_grain_outside_jk",          case_02_grain_outside_jk),
    ("03_grain_is_full_type",        case_03_grain_is_full_type),
    ("04_single_field_grain",        case_04_single_field_grain),
    ("05_natural_join",              case_05_natural_join),
    ("06_single_field_jk",           case_06_single_field_jk),
    ("07_jk_portions_differ_by_one", case_07_jk_portions_differ_by_one),
    ("08_self_join",                 case_08_self_join),
    ("09_both_grains_inside_jk",     case_09_both_grains_inside_jk),
    ("10_large_jk_nongrain",         case_10_large_jk_nongrain),
    ("11_equal_jk_different_rest",   case_11_equal_jk_different_rest),
    ("12_extreme_asymmetry",         case_12_extreme_asymmetry),
    ("13_size_imbalance",            case_13_size_imbalance),
    ("14_disjoint_grains",           case_14_disjoint_grains),
    ("15_identical_grains",          case_15_identical_grains),
    ("16_everything_is_jk",          case_16_everything_is_jk),
]
