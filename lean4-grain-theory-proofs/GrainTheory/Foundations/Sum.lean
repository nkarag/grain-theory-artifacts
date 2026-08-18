/-
  GrainTheory.Foundations.Sum — Grain of sum (coproduct) types

  PODS Theorem 3.9: G[R₁ + R₂] ≅ G[R₁] + G[R₂].

  The sum of grains is itself a grain of the sum type.
  The proof establishes that sum (grain R₁) (grain R₂) satisfies the
  three grain axioms for sum R₁ R₂, then uses antisymmetry to conclude
  iso with the canonical grain.

  New axioms used (added to Basic.lean):
  - sub_sum: sum preserves type subset
  - sum_iso: sum preserves isomorphism
  - sum_irred: sums of irreducible types are irreducible

  Reference: PODS 2027 paper, §3, Theorem grain-sum.
-/

import GrainTheory.Foundations.GrainDef
import GrainTheory.Foundations.MultipleGrains

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-- The sum of grains satisfies `IsGrainOf` for the sum type.

    - Isomorphism: `grain Rᵢ ≅ Rᵢ`, and sum preserves iso (`sum_iso`).
    - Irreducibility: each `grain Rᵢ` is structurally irreducible, and the
      sum of irreducible types is irreducible (`sum_irred`).

    **No independence hypothesis** — unlike the product case (Thm 3.8), the
    summands of a coproduct are disjoint alternatives, so no determination can
    hold across them (arXiv Remark 4.3). -/
theorem sum_grain_isGrainOf (R₁ R₂ : D) :
    IsGrainOf (sum (grain R₁) (grain R₂)) (sum R₁ R₂) :=
  ⟨sum_iso _ _ _ _ (grain_iso R₁) (grain_iso R₂),
   fun S h_ssub h_iso =>
     sum_irred _ _ _ _ S
       (fun T => grain_irred R₁ T) (fun T => grain_irred R₂ T)
       h_ssub h_iso⟩

/-- arXiv Theorem 3.9: Grain of sum types.
    G[R₁ + R₂] ≅ G[R₁] + G[R₂].

    Both `sum (grain R₁) (grain R₂)` and the canonical `grain (sum R₁ R₂)` are
    grains of `sum R₁ R₂`, so they are isomorphic (`multiple_grains_iso`). -/
theorem grain_sum (R₁ R₂ : D) :
    iso (grain (sum R₁ R₂)) (sum (grain R₁) (grain R₂)) :=
  multiple_grains_iso (grain_isGrainOf (sum R₁ R₂)) (sum_grain_isGrainOf R₁ R₂)

end GrainTheory.Foundations
