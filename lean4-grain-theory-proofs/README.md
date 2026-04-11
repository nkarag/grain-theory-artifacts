# Lean 4 Mechanized Proofs of Grain Theory

Machine-checked formalization of all theorems from the PODS 2027 paper
"Grain Theory: A Type-Level Framework for Correctness of Data Transformations."

## Overview

All 26 formal statements from the PODS appendix (Sections 3--9) have been
mechanically verified in Lean 4 with Mathlib. The formalization uses an
abstract axiomatization: data types and grain are opaque structures with
assumed properties, and all theorems are proved from these axioms. This
mirrors the paper's proof style.

**Key statistics:**
- 33 Lean modules across 8 directories
- 0 `sorry` (unfinished proof) obligations
- Covers: foundations, grain relations, entity keys, inference rules
  (including the equi-join centerpiece), dependency theory, CalcG
  correctness, and error detection

## Building

**Prerequisites:** Lean 4 v4.29.0-rc8 (specified in `lean-toolchain`)

```bash
lake exe cache get   # Download prebuilt Mathlib (recommended, ~5 min)
lake build           # Build and verify all proofs (~2 min)
```

## Module Structure

```
GrainTheory/
  Basic.lean                         -- Core axioms (GrainStructure class)
  Foundations/
    GrainDef.lean                    -- Def 1-3: type subset, grain, IsGrainOf
    Factorization.lean               -- Universal factorization
    MultipleGrains.lean              -- Multiple grains isomorphism
    Uniqueness.lean                  -- Grain uniqueness
    Idempotency.lean                 -- G[G[R]] = G[R]
    Product.lean                     -- G[R1 x R2] = G[R1] x G[R2]
    Sum.lean                         -- G[R1 + R2] = G[R1] + G[R2]
  Relations/
    GrainEquality.lean               -- Def 4, Thm 4.2, preservation
    GrainOrdering.lean               -- Def 5, partial order, preservation
    GrainSubset.lean                 -- Grain subset + corollary
    GrainInference.lean              -- Grain Inference Theorem (IsGrainOf)
    IntersectionUnion.lean           -- Intersection/union with grain
    Incomparability.lean             -- Def 6, incomparability preservation
    Armstrong.lean                   -- Axioms A1-A9 (soundness)
    Lattice.lean                     -- Grain lattice structure
  Entity/
    EntityDef.lean                   -- Entity, entity key definitions
    EKHierarchy.lean                 -- EK subset G[R] subset R
  Inference/
    EquiJoinAxioms.lean              -- EquiJoinStructure axioms
    EquiJoinSub.lean                 -- F1 subset Res
    EquiJoinBootstrap.lean           -- Bootstrapping lemma
    EquiJoinIrred.lean               -- Condition (iii): grain fixpoint
    EquiJoinIdentity.lean            -- IsGrainOf F1 Res (capstone)
    EquiJoin.lean                    -- Main equi-join theorem
    GeneralizedJoin.lean             -- Generalized equi-join (grain equality)
    JoinSpecialCases.lean            -- Prop 6.2: equal/ordered/incomparable/natural
    RAOperations.lean                -- All 9 RA operations (Table 1)
  DependencyTheory/
    Completeness.lean                -- Armstrong completeness
    Determination.lean               -- Determination problem
  CalcG/
    CalcGDef.lean                    -- CalcG definition + correctness
    ZeroCost.lean                    -- Zero-cost verification corollary
  ErrorDetection/
    FanTrap.lean                     -- Fan trap characterization
    ChasmTrap.lean                   -- Chasm trap characterization
```

## Axiomatization

The formalization rests on two type classes:

- **`GrainStructure`** (33 axioms in `Basic.lean`): Type subset, isomorphism,
  grain operator, and type-level operations (product, sum, union, intersection,
  difference) with structural properties.

- **`EquiJoinStructure`** (9 axioms in `EquiJoinAxioms.lean`): Join-specific
  hypotheses for the equi-join grain inference theorem.

All theorems are proved from these axioms alone. The only statement not
re-derived from first principles is the completeness direction of the
Armstrong system (`armstrong_complete` in `Completeness.lean`), which
transfers directly from Armstrong's classical 1974 result.

## Correspondence to PODS Paper

| Paper Section | Lean Module(s) | Key Theorems |
|---------------|----------------|--------------|
| Section 3 (Foundations) | `Foundations/*` | `grain_idempotent`, `grain_product`, `grain_sum`, `factorization`, `grain_unique` |
| Section 4 (Relations) | `Relations/*` | `grainEq_iff_iso`, `grainLe_preservation`, `grainIncomp_preservation`, Armstrong A1-A9 |
| Section 5 (Entity) | `Entity/*` | `ek_grain_type_hierarchy` |
| Section 6 (Inference) | `Inference/*` | `equijoin_grain_identity` (IsGrainOf), all 9 RA rules, 4 join special cases |
| Section 7 (Dependency) | `DependencyTheory/*` | `armstrong_sound`, `grainLe_iff_derivable`, `determination_square` |
| Section 8 (CalcG) | `CalcG/*` | `calcG_isGrainOf`, `grainCorrect_iff_isGrainOf` |
| Section 9 (Errors) | `ErrorDetection/*` | `fan_trap_detection`, `safe_chain_iff_total` |

## License

MIT License. See top-level `LICENSE` file.
