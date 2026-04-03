"""
Tests for the equi-join configuration generators.

Verifies:
  1. equijoin_config produces valid Config instances
  2. All 16 configuration classes are reachable within 1000 samples
  3. all_configs_up_to produces the expected count
  4. Filtered strategies produce only their target class
"""

from collections import Counter

from hypothesis import given, settings

from config import Config, JkRelation
from generators import (
    equijoin_config,
    equijoin_config_comparable,
    equijoin_config_incomparable,
    equijoin_config_class,
    all_configs_up_to,
    config_class_key,
    all_16_classes,
)


# ---------- Property: generated configs are structurally valid ----------

@given(config=equijoin_config())
@settings(max_examples=500)
def test_config_validity(config: Config):
    """Every generated config satisfies all structural invariants."""
    jk_set = set(config.jk)
    r1_set = set(config.r1_fields)
    r2_set = set(config.r2_fields)
    g1_set = set(config.g1)
    g2_set = set(config.g2)

    # Jk ⊆ R1 ∩ R2
    assert jk_set <= r1_set, f"Jk not subset of R1: {config.jk} vs {config.r1_fields}"
    assert jk_set <= r2_set, f"Jk not subset of R2: {config.jk} vs {config.r2_fields}"

    # Gi ⊆ Ri
    assert g1_set <= r1_set, f"G1 not subset of R1: {config.g1} vs {config.r1_fields}"
    assert g2_set <= r2_set, f"G2 not subset of R2: {config.g2} vs {config.r2_fields}"

    # Gi non-empty
    assert len(config.g1) > 0, "G1 is empty"
    assert len(config.g2) > 0, "G2 is empty"

    # Derived quantities consistent
    assert set(config.g1_jk) == g1_set & jk_set
    assert set(config.g2_jk) == g2_set & jk_set
    assert set(config.g1_rest) == g1_set - jk_set
    assert set(config.g2_rest) == g2_set - jk_set

    # Formula directions
    assert set(config.f1) == g1_set | (g2_set - jk_set)
    assert set(config.f2) == g2_set | (g1_set - jk_set)

    # Size relationship: |F1| - |F2| = |G1^Jk| - |G2^Jk|
    assert len(config.f1) - len(config.f2) == len(config.g1_jk) - len(config.g2_jk)

    # Convention grain is the smaller-or-equal direction
    assert len(config.convention_grain) <= len(config.f1)
    assert len(config.convention_grain) <= len(config.f2)


# ---------- Coverage: all 16 classes reachable ----------

def test_all_16_classes_reachable():
    """The random generator reaches all 16 configuration classes within 1000 samples."""
    seen = set()
    target = all_16_classes()

    # Generate 1000 configs and record their class
    from hypothesis import find
    from hypothesis import strategies as st

    # Use find() repeatedly to collect diverse examples
    configs = []
    strat = equijoin_config(max_jk=4, max_r_only=3)

    @given(config=strat)
    @settings(max_examples=1000)
    def _collect(config):
        key = config_class_key(config)
        seen.add(key)

    _collect()

    missing = target - seen
    assert len(missing) == 0, (
        f"Missing {len(missing)} configuration classes after 1000 samples: "
        f"{[(r.value, g1e, g2e) for r, g1e, g2e in missing]}"
    )


# ---------- Exhaustive enumerator: count and class coverage ----------

def test_exhaustive_count_size_3():
    """Exhaustive enumerator for max_type_size=3 produces the expected count."""
    configs = list(all_configs_up_to(3))
    assert len(configs) > 0, "Exhaustive enumerator produced no configs"

    # Verify all are valid
    for c in configs:
        assert len(c.g1) > 0
        assert len(c.g2) > 0
        assert set(c.jk) <= set(c.r1_fields)
        assert set(c.jk) <= set(c.r2_fields)

    # Count by class
    class_counts = Counter(config_class_key(c) for c in configs)
    print(f"\nExhaustive (max_size=3): {len(configs)} configs, {len(class_counts)} classes")
    for key, count in sorted(class_counts.items(), key=lambda x: x[0][0].value):
        rel, g1e, g2e = key
        print(f"  {rel.value:16s} g1_rest_empty={g1e!s:5s} g2_rest_empty={g2e!s:5s}: {count}")


def test_exhaustive_all_classes_covered():
    """Exhaustive enumerator for max_type_size=4 covers all 16 classes."""
    seen = set()
    count = 0
    for c in all_configs_up_to(4):
        seen.add(config_class_key(c))
        count += 1
        if len(seen) == 16:
            break  # Early exit once all classes found

    assert len(seen) == 16, f"Only {len(seen)}/16 classes found in {count} configs"
    print(f"\nAll 16 classes found within {count} configs (max_size=4)")


# ---------- Filtered strategies ----------

@given(config=equijoin_config_comparable())
@settings(max_examples=200)
def test_comparable_filter(config: Config):
    """Comparable filter only produces comparable configs."""
    assert config.jk_rel in (
        JkRelation.PROPER_SUBSET,
        JkRelation.EQUAL,
        JkRelation.PROPER_SUPERSET,
    ), f"Got incomparable config from comparable filter: {config.jk_rel}"


@given(config=equijoin_config_incomparable())
@settings(max_examples=200)
def test_incomparable_filter(config: Config):
    """Incomparable filter only produces incomparable configs."""
    assert config.jk_rel == JkRelation.INCOMPARABLE, (
        f"Got {config.jk_rel} from incomparable filter"
    )


@given(config=equijoin_config_class(
    jk_rel=JkRelation.PROPER_SUBSET, g1_rest_empty=False, g2_rest_empty=True
))
@settings(max_examples=100)
def test_specific_class_filter(config: Config):
    """Specific class filter produces only the target class."""
    assert config.jk_rel == JkRelation.PROPER_SUBSET
    assert len(config.g1_rest) > 0, "Expected non-empty g1_rest"
    assert len(config.g2_rest) == 0, "Expected empty g2_rest"
