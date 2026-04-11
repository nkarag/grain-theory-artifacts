/-
  GrainTheory.Foundations.Factorization — Universal factorization (PODS §3.3)

  PODS Proposition (Universal Factorization):
  For any type R₁ ≅ R, the isomorphism factors through the grain:
  R₁ ≅ G[R] ≅ R.

  In our abstract axiomatization (iso is an opaque relation, not
  constructive functions), this is the type-level consequence:
  iso R₁ R → iso R₁ (grain R).
-/

import GrainTheory.Basic

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure (iso grain iso_trans iso_symm grain_iso)

/-- PODS Proposition (Universal Factorization):
    Every isomorphism R₁ ≅ R factors through the grain G[R].

    If R₁ ≅ R, then R₁ ≅ G[R].

    Proof: R₁ ≅ R ≅⁻¹ G[R] (by grain_iso and iso_symm). -/
theorem factorization (R₁ R : D) (h : iso R₁ R) : iso R₁ (grain R) :=
  iso_trans _ _ _ h (iso_symm _ _ (grain_iso R))

end GrainTheory.Foundations
