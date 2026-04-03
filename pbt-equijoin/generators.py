"""
Hypothesis strategies for generating equi-join configurations.

Provides:
  - equijoin_config():           random config covering all 16 classes
  - equijoin_config_comparable(): only comparable Jk-portions (proper_subset or equal)
  - equijoin_config_incomparable(): only incomparable Jk-portions
  - equijoin_config_class():     specific configuration class
  - all_configs_up_to():         exhaustive enumerator for bounded model checking
"""

from itertools import product as iterproduct
from typing import Iterator, Optional

from hypothesis import assume, strategies as st

from config import Config, JkRelation, make_config


def _mask_to_subset(fields: list, mask: int) -> list:
    """Convert a bitmask to a subset of fields."""
    return [fields[i] for i in range(len(fields)) if mask & (1 << i)]


@st.composite
def equijoin_config(draw, max_jk=8, max_r_only=6):
    """Generate a random equi-join configuration.

    Covers all 16 configuration classes (4 Jk-portion relations × 2 G1_rest
    emptiness × 2 G2_rest emptiness) with natural Hypothesis shrinking.

    Args:
        max_jk: Maximum number of join key columns (1–max_jk).
        max_r_only: Maximum number of R_i-only columns (0–max_r_only).
    """
    # 1. Draw sizes
    n_jk = draw(st.integers(min_value=1, max_value=max_jk))
    n_r1_only = draw(st.integers(min_value=0, max_value=max_r_only))
    n_r2_only = draw(st.integers(min_value=0, max_value=max_r_only))

    # 2. Name fields
    jk_fields = [f"j{i}" for i in range(n_jk)]
    r1_only_fields = [f"a{i}" for i in range(n_r1_only)]
    r2_only_fields = [f"b{i}" for i in range(n_r2_only)]
    r1_fields = r1_only_fields + jk_fields
    r2_fields = jk_fields + r2_only_fields

    # 3. Draw grain subsets (non-empty bitmasks)
    g1_mask = draw(st.integers(min_value=1, max_value=(1 << len(r1_fields)) - 1))
    g2_mask = draw(st.integers(min_value=1, max_value=(1 << len(r2_fields)) - 1))
    g1 = _mask_to_subset(r1_fields, g1_mask)
    g2 = _mask_to_subset(r2_fields, g2_mask)

    return make_config(r1_fields, r2_fields, jk_fields, g1, g2)


@st.composite
def equijoin_config_comparable(draw, max_jk=6, max_r_only=4):
    """Generate configs with comparable Jk-portions only (proper_subset or equal)."""
    config = draw(equijoin_config(max_jk=max_jk, max_r_only=max_r_only))
    assume(config.jk_rel in (JkRelation.PROPER_SUBSET, JkRelation.EQUAL,
                              JkRelation.PROPER_SUPERSET))
    return config


@st.composite
def equijoin_config_incomparable(draw, max_jk=6, max_r_only=4):
    """Generate configs with incomparable Jk-portions only."""
    config = draw(equijoin_config(max_jk=max_jk, max_r_only=max_r_only))
    assume(config.jk_rel == JkRelation.INCOMPARABLE)
    return config


@st.composite
def equijoin_config_class(
    draw,
    jk_rel: JkRelation,
    g1_rest_empty: Optional[bool] = None,
    g2_rest_empty: Optional[bool] = None,
    max_jk=6,
    max_r_only=4,
):
    """Generate configs matching a specific configuration class.

    Args:
        jk_rel: Required Jk-portion relationship.
        g1_rest_empty: If True, require G1_rest = ∅. If False, require non-empty. If None, any.
        g2_rest_empty: Same for G2_rest.
    """
    config = draw(equijoin_config(max_jk=max_jk, max_r_only=max_r_only))
    assume(config.jk_rel == jk_rel)
    if g1_rest_empty is not None:
        assume((len(config.g1_rest) == 0) == g1_rest_empty)
    if g2_rest_empty is not None:
        assume((len(config.g2_rest) == 0) == g2_rest_empty)
    return config


def all_configs_up_to(max_type_size: int = 5) -> Iterator[Config]:
    """Exhaustively enumerate all valid configurations with |Ri| ≤ max_type_size.

    This is bounded model checking: every possible (R1, R2, Jk, G1, G2) is generated,
    subject to the structural constraints (Jk ⊆ R1 ∩ R2, Gi ⊆ Ri, Gi non-empty).

    Args:
        max_type_size: Maximum number of columns per relation.

    Yields:
        Config instances for every valid configuration.
    """
    for n_jk in range(1, max_type_size + 1):
        for n_r1_only in range(0, max_type_size - n_jk + 1):
            for n_r2_only in range(0, max_type_size - n_jk + 1):
                r1_size = n_r1_only + n_jk
                r2_size = n_r2_only + n_jk

                # Name fields
                jk_fields = [f"j{i}" for i in range(n_jk)]
                r1_only_fields = [f"a{i}" for i in range(n_r1_only)]
                r2_only_fields = [f"b{i}" for i in range(n_r2_only)]
                r1_fields = r1_only_fields + jk_fields
                r2_fields = jk_fields + r2_only_fields

                # Enumerate all non-empty grain subsets
                for g1_mask in range(1, 1 << r1_size):
                    g1 = _mask_to_subset(r1_fields, g1_mask)
                    for g2_mask in range(1, 1 << r2_size):
                        g2 = _mask_to_subset(r2_fields, g2_mask)
                        yield make_config(r1_fields, r2_fields, jk_fields, g1, g2)


def config_class_key(config: Config) -> tuple:
    """Return the (jk_rel, g1_rest_empty, g2_rest_empty) classification key."""
    return (config.jk_rel, len(config.g1_rest) == 0, len(config.g2_rest) == 0)


def all_16_classes():
    """Return the set of all 16 configuration class keys."""
    classes = set()
    for jk_rel in JkRelation:
        for g1e in (True, False):
            for g2e in (True, False):
                classes.add((jk_rel, g1e, g2e))
    return classes
