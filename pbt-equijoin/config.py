"""
Configuration types for equi-join grain inference property-based testing.

Defines the Config dataclass representing a single equi-join configuration,
and the JkRelation enum classifying the Jk-grain-portion relationship.
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import List


class JkRelation(Enum):
    """Classification of the Jk-grain-portion relationship between R1 and R2.

    Given G1_Jk = G[R1] ∩ Jk and G2_Jk = G[R2] ∩ Jk:
    - PROPER_SUBSET:  G1_Jk ⊊ G2_Jk  (convention-compliant: R1 has smaller portion)
    - EQUAL:          G1_Jk = G2_Jk
    - PROPER_SUPERSET: G1_Jk ⊋ G2_Jk  (convention violated: R1 has larger portion)
    - INCOMPARABLE:   neither is a subset of the other
    """
    PROPER_SUBSET = "proper_subset"
    EQUAL = "equal"
    PROPER_SUPERSET = "proper_superset"
    INCOMPARABLE = "incomparable"


@dataclass(frozen=True)
class Config:
    """A single equi-join configuration for testing.

    Represents R1 ⋈_{Jk} R2 with specified grains G[R1] and G[R2].

    Derived quantities (g1_jk, g2_jk, g1_rest, g2_rest, jk_rel, f1, f2,
    convention_grain) are computed from the primary fields.
    """
    # Primary fields
    r1_fields: tuple  # All columns of R1
    r2_fields: tuple  # All columns of R2
    jk: tuple         # Join key columns (subset of R1 ∩ R2)
    g1: tuple         # Grain of R1 (subset of R1)
    g2: tuple         # Grain of R2 (subset of R2)

    # Derived: Jk-grain-portions
    g1_jk: tuple = field(default=())    # G[R1] ∩ Jk
    g2_jk: tuple = field(default=())    # G[R2] ∩ Jk
    g1_rest: tuple = field(default=())  # G[R1] \ Jk
    g2_rest: tuple = field(default=())  # G[R2] \ Jk

    # Derived: classification
    jk_rel: JkRelation = JkRelation.EQUAL

    # Derived: formula directions
    f1: tuple = field(default=())  # G[R1] ∪ (G[R2] \ Jk) — Direction 1
    f2: tuple = field(default=())  # G[R2] ∪ (G[R1] \ Jk) — Direction 2
    convention_grain: tuple = field(default=())  # The naming-convention-compliant grain


def classify_jk_relation(g1_jk_set: set, g2_jk_set: set) -> JkRelation:
    """Classify the Jk-grain-portion relationship."""
    if g1_jk_set == g2_jk_set:
        return JkRelation.EQUAL
    elif g1_jk_set < g2_jk_set:
        return JkRelation.PROPER_SUBSET
    elif g1_jk_set > g2_jk_set:
        return JkRelation.PROPER_SUPERSET
    else:
        return JkRelation.INCOMPARABLE


def make_config(
    r1_fields: List[str],
    r2_fields: List[str],
    jk: List[str],
    g1: List[str],
    g2: List[str],
) -> Config:
    """Create a Config with all derived quantities computed.

    Args:
        r1_fields: All columns of R1
        r2_fields: All columns of R2
        jk: Join key columns
        g1: Grain columns of R1
        g2: Grain columns of R2

    Returns:
        Config with all derived fields populated.

    Raises:
        ValueError: If inputs violate structural constraints.
    """
    jk_set = set(jk)
    g1_set = set(g1)
    g2_set = set(g2)

    # Validate
    if not jk_set <= set(r1_fields):
        raise ValueError(f"Jk must be subset of R1: {jk} not in {r1_fields}")
    if not jk_set <= set(r2_fields):
        raise ValueError(f"Jk must be subset of R2: {jk} not in {r2_fields}")
    if not g1_set <= set(r1_fields):
        raise ValueError(f"G1 must be subset of R1: {g1} not in {r1_fields}")
    if not g2_set <= set(r2_fields):
        raise ValueError(f"G2 must be subset of R2: {g2} not in {r2_fields}")
    if not g1_set:
        raise ValueError("G1 must be non-empty")
    if not g2_set:
        raise ValueError("G2 must be non-empty")

    # Derived quantities
    g1_jk = sorted(g1_set & jk_set)
    g2_jk = sorted(g2_set & jk_set)
    g1_rest = sorted(g1_set - jk_set)
    g2_rest = sorted(g2_set - jk_set)

    # Classification
    g1_jk_set = set(g1_jk)
    g2_jk_set = set(g2_jk)
    jk_rel = classify_jk_relation(g1_jk_set, g2_jk_set)

    # Formula directions
    f1 = sorted(g1_set | (g2_set - jk_set))  # G[R1] ∪ (G[R2] \ Jk)
    f2 = sorted(g2_set | (g1_set - jk_set))  # G[R2] ∪ (G[R1] \ Jk)

    # Convention-compliant grain
    if jk_rel == JkRelation.PROPER_SUBSET:
        convention_grain = tuple(f1)  # R1 has smaller Jk-portion → F1 is smaller
    elif jk_rel == JkRelation.EQUAL:
        convention_grain = tuple(f1)  # Equal Jk-portions → F1 = F2
    elif jk_rel == JkRelation.PROPER_SUPERSET:
        convention_grain = tuple(f2)  # Swap: R2 has smaller Jk-portion → F2 is smaller
    else:  # INCOMPARABLE — both directions valid, pick the smaller
        convention_grain = tuple(f1) if len(f1) <= len(f2) else tuple(f2)

    return Config(
        r1_fields=tuple(r1_fields),
        r2_fields=tuple(r2_fields),
        jk=tuple(jk),
        g1=tuple(g1),
        g2=tuple(g2),
        g1_jk=tuple(g1_jk),
        g2_jk=tuple(g2_jk),
        g1_rest=tuple(g1_rest),
        g2_rest=tuple(g2_rest),
        jk_rel=jk_rel,
        f1=tuple(f1),
        f2=tuple(f2),
        convention_grain=convention_grain,
    )
