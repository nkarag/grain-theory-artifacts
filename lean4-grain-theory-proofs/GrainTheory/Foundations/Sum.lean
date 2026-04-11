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

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-- PODS Theorem 3.9: Grain of sum (coproduct) types.
    G[R₁ + R₂] ≅ G[R₁] + G[R₂].

    Proof outline:
    1. Show sum (grain R₁) (grain R₂) is a grain of sum R₁ R₂:
       - Subset: grain Rᵢ ⊆_typ Rᵢ, so sum preserves this (sub_sum)
       - Isomorphism: grain Rᵢ ≅ Rᵢ, so sum preserves this (sum_iso)
       - Irreducibility: grains are irreducible, so sum of irred is irred (sum_irred)
    2. Since both grain (sum R₁ R₂) and sum (grain R₁) (grain R₂) are grains
       of sum R₁ R₂, they are isomorphic:
       - iso_sub + grain_sub gives grain (sum R₁ R₂) ⊆_typ sum (grain R₁) (grain R₂)
       - sum_irred + grain_iso gives the reverse inclusion
       - sub_antisymm concludes -/
theorem grain_sum (R₁ R₂ : D) :
    iso (grain (sum R₁ R₂)) (sum (grain R₁) (grain R₂)) := by
  -- Step 1: sum (grain R₁) (grain R₂) satisfies the three grain axioms for sum R₁ R₂
  -- (a) Subset: sum (grain R₁) (grain R₂) ⊆_typ sum R₁ R₂
  have h_sub : sub (sum (grain R₁) (grain R₂)) (sum R₁ R₂) :=
    sub_sum _ _ _ _ (grain_sub R₁) (grain_sub R₂)
  -- (b) Isomorphism: sum (grain R₁) (grain R₂) ≅ sum R₁ R₂
  have h_iso : iso (sum (grain R₁) (grain R₂)) (sum R₁ R₂) :=
    sum_iso _ _ _ _ (grain_iso R₁) (grain_iso R₂)
  -- (c) Irreducibility: sum of irreducible types is irreducible
  have h_irred : ∀ S : D, sub S (sum (grain R₁) (grain R₂)) →
      iso S (sum R₁ R₂) → sub (sum (grain R₁) (grain R₂)) S :=
    fun S h_s h_i => sum_irred _ _ _ _ S
      (fun T => grain_irred R₁ T) (fun T => grain_irred R₂ T) h_s h_i
  -- Step 2: Both grain (sum R₁ R₂) and sum (grain R₁) (grain R₂) are grains,
  -- so they must be isomorphic.
  -- (d) grain (sum R₁ R₂) ⊆_typ sum (grain R₁) (grain R₂)
  --     By iso_sub: h_iso : sum(grain..) ≅ sum R₁ R₂, and
  --     grain_sub : grain(sum R₁ R₂) ⊆_typ sum R₁ R₂,
  --     so grain(sum R₁ R₂) ⊆_typ sum(grain R₁)(grain R₂)
  have h1 : sub (grain (sum R₁ R₂)) (sum (grain R₁) (grain R₂)) :=
    iso_sub _ _ _ h_iso (grain_sub (sum R₁ R₂))
  -- (e) sum (grain R₁) (grain R₂) ⊆_typ grain (sum R₁ R₂)
  --     From h1 and grain_iso, by h_irred
  have h2 : sub (sum (grain R₁) (grain R₂)) (grain (sum R₁ R₂)) :=
    h_irred _ h1 (grain_iso (sum R₁ R₂))
  -- (f) Antisymmetry: both directions give isomorphism
  exact sub_antisymm _ _ h1 h2

/-- The sum of grains satisfies `IsGrainOf` for the sum type.
    This packages the three grain properties for downstream use. -/
theorem sum_grain_isGrainOf (R₁ R₂ : D) :
    IsGrainOf (sum (grain R₁) (grain R₂)) (sum R₁ R₂) :=
  ⟨sum_iso _ _ _ _ (grain_iso R₁) (grain_iso R₂),
   fun S h_sub h_iso =>
     sum_irred _ _ _ _ S
       (fun T => grain_irred R₁ T) (fun T => grain_irred R₂ T)
       h_sub h_iso⟩

end GrainTheory.Foundations
