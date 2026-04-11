/-
  GrainTheory.Foundations.Idempotency — Grain operator idempotency

  PODS Theorem 3.7: G[G[R]] ≅ G[R] for all data types R.

  The proof is direct from the GrainStructure axioms:
  grain_sub, grain_iso, grain_irred, iso_trans, sub_antisymm.
-/

import GrainTheory.Foundations.GrainDef

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-- PODS Theorem 3.7: Grain operator idempotency. G[G[R]] ≅ G[R].

  Proof: G[G[R]] ⊆_typ G[R] (grain_sub). By transitivity of iso,
  G[G[R]] ≅ G[R] ≅ R, so G[G[R]] ≅ R. By irreducibility of G[R],
  G[R] ⊆_typ G[G[R]]. Antisymmetry gives G[G[R]] ≅ G[R]. -/
theorem grain_idempotent (R : D) : iso (grain (grain R)) (grain R) := by
  -- G[G[R]] ⊆_typ G[R]
  have h_sub : sub (grain (grain R)) (grain R) := grain_sub (grain R)
  -- G[G[R]] ≅ R (by transitivity: G[G[R]] ≅ G[R] ≅ R)
  have h_iso_R : iso (grain (grain R)) R :=
    iso_trans _ _ _ (grain_iso (grain R)) (grain_iso R)
  -- Irreducibility of G[R]: since G[G[R]] ⊆_typ G[R] and G[G[R]] ≅ R, we get G[R] ⊆_typ G[G[R]]
  have h_sub_rev : sub (grain R) (grain (grain R)) :=
    grain_irred R (grain (grain R)) h_sub h_iso_R
  -- Antisymmetry: both directions of ⊆_typ give ≅
  exact sub_antisymm _ _ h_sub h_sub_rev

/-- The grain of the grain is itself a grain of R. -/
theorem grain_grain_isGrainOf (R : D) : IsGrainOf (grain (grain R)) R :=
  ⟨iso_trans _ _ _ (grain_iso (grain R)) (grain_iso R),
   fun S h_sub h_iso =>
     -- h_sub : S ⊆_typ G[G[R]], h_iso : S ≅ R
     -- Goal: G[G[R]] ⊆_typ S
     -- S ⊆_typ G[R] by transitivity through G[G[R]]
     have h_sub_GR : sub S (grain R) :=
       sub_trans _ _ _ h_sub (grain_sub (grain R))
     -- G[R] ⊆_typ S by irreducibility of G[R]
     have h_GR_sub_S : sub (grain R) S :=
       grain_irred R S h_sub_GR h_iso
     -- G[G[R]] ⊆_typ G[R] ⊆_typ S by transitivity
     sub_trans _ _ _ (grain_sub (grain R)) h_GR_sub_S⟩

end GrainTheory.Foundations
