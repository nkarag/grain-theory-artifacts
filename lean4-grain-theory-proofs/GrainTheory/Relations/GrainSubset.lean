/-
  GrainTheory.Relations.GrainSubset — Grain subset theorem and corollary

  PODS Theorem 3.4: If G[R₁] ⊆_typ G[R₂], then R₂ ≤_g R₁.
  PODS Corollary 3.5: If R' ⊆_typ R, then G[R] ≤_g R'.
-/

import GrainTheory.Relations.GrainOrdering
import GrainTheory.Foundations.Idempotency

namespace GrainTheory.Relations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-! ## PODS Theorem 3.4: Grain Subset -/

/-- PODS Thm 3.4: If G[R₁] ⊆_typ G[R₂], then R₂ ≤_g R₁.
    Trivially definitional — validates that our grainLe encoding captures
    the subset-based ordering. -/
theorem grain_subset {R₁ R₂ : D} (h : sub (grain R₁) (grain R₂)) : grainLe R₂ R₁ :=
  h

/-! ## PODS Corollary 3.5: Grain Determines All Subsets -/

/-- PODS Cor 3.5: The grain of a type determines any subset of that type's fields.
    If R' ⊆_typ R, then G[R] ≤_g R'.

    Proof: G[R] ≅ R (grain_iso) and R' ⊆ R (hypothesis), so by iso_sub,
    R' ⊆ G[R]. Then G[R'] ⊆ R' ⊆ G[R] ⊆ G[G[R]] (idempotency). -/
theorem grain_determines_subsets {R R' : D} (h : sub R' R) :
    grainLe (grain R) R' := by
  -- Goal: sub (grain R') (grain (grain R))
  -- Step 1: R' ⊆_typ G[R] (via iso_sub: G[R] ≅ R and R' ⊆ R)
  have h_R'_sub_GR : sub R' (grain R) :=
    iso_sub _ _ _ (grain_iso R) h
  -- Step 2: G[R'] ⊆_typ G[R] (via G[R'] ⊆ R' ⊆ G[R])
  have h_GR'_sub_GR : sub (grain R') (grain R) :=
    sub_trans _ _ _ (grain_sub R') h_R'_sub_GR
  -- Step 3: G[R] ⊆_typ G[G[R]] (from idempotency proof)
  have h_GR_sub_GGR : sub (grain R) (grain (grain R)) :=
    grain_irred R (grain (grain R)) (grain_sub (grain R))
      (iso_trans _ _ _ (grain_iso (grain R)) (grain_iso R))
  -- Step 4: G[R'] ⊆_typ G[G[R]] by transitivity
  exact sub_trans _ _ _ h_GR'_sub_GR h_GR_sub_GGR

end GrainTheory.Relations
