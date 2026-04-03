"""
Property-based tests for equi-join grain inference.

Tests the corrected formula:
    G[Res] ≡_g G[R1] ∪_typ (G[R2] -_typ Jk)

with the naming convention:
    R1 denotes the input with G1^Jk ⊆_typ G2^Jk (when comparable).

Properties tested:
    1. Uniqueness — both directions produce unique identifiers
    2. Minimality — convention-compliant direction is minimal (irreducible)
    3. Wrong direction fails minimality (comparable, non-equal Jk-portions)
    4. Incomparable — both directions are minimal
    5. Size relationship — |F1| - |F2| = |G1^Jk| - |G2^Jk|
    6. Convention grain is smallest — |convention_grain| ≤ min(|F1|, |F2|)

Modes:
    Mode A (exhaustive): all configs with |Ri| ≤ 5
    Mode B (random): 10,000 random configs with |Ri| ≤ 15
    Mode C (edge cases): 16 targeted boundary configurations

See BULLETPROOF_EQUIJOIN_PLAN.md for full specification.
"""

# Properties will be implemented in TASK_20260403_05_pbt-properties
