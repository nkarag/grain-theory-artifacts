/-
  GrainTheory.Foundations.MultipleGrains — Multiple grains isomorphism (PODS §3)

  PODS Theorem (Multiple Grains Isomorphism):
  If G₁ and G₂ are both grains of R, then G₁ ≅ G₂.

  Proof: G₁ ≅ R ≅⁻¹ G₂ by composing the two grain isomorphisms.
-/

import GrainTheory.Foundations.GrainDef

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure (iso iso_trans iso_symm)

/-- PODS Theorem (Multiple Grains Isomorphism):
    If G₁ and G₂ are both grains of R, then G₁ ≅ G₂.

    Proof: G₁ ≅ R (from h₁) composed with R ≅⁻¹ G₂ (from h₂). -/
theorem multiple_grains_iso {G₁ G₂ R : D}
    (h₁ : IsGrainOf G₁ R) (h₂ : IsGrainOf G₂ R) : iso G₁ G₂ :=
  iso_trans _ _ _ h₁.toIso (iso_symm _ _ h₂.toIso)

end GrainTheory.Foundations
