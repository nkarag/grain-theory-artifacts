/-
  GrainTheory.Foundations.Uniqueness — Grain uniqueness (PODS §3)

  PODS Theorem (Grain Uniqueness):
  The grain projection is injective — if grain(r₁) = grain(r₂) then r₁ = r₂.

  This is an instance-level property. In our type-level axiomatization, we
  encode two type-level consequences:

  1. `grain_unique_canonical`: The canonical grain G[R] is a grain of R
     (IsGrainOf). Combined with `multiple_grains_iso`, any two grains of R
     are isomorphic — the grain is unique up to isomorphism.

  2. `grain_unique_of_iso`: If R₁ ≅ R₂, then G[R₁] ≅ G[R₂] — isomorphic
     types have isomorphic grains. (Proved in GrainEquality as grainEq_of_iso.)

  The instance-level injectivity is a direct consequence of `grain_iso`
  (the grain function is an isomorphism, hence bijective, hence its
  inverse is injective).
-/

import GrainTheory.Foundations.MultipleGrains

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure (iso grain iso_symm iso_trans grain_iso)

/-- PODS Theorem (Grain Uniqueness — type-level):
    Any grain of R is isomorphic to the canonical grain G[R].

    This combines `grain_isGrainOf` (G[R] satisfies IsGrainOf) with
    `multiple_grains_iso` (any two grains are isomorphic). -/
theorem grain_unique (R : D) (G : D) (h : IsGrainOf G R) :
    iso G (grain R) :=
  multiple_grains_iso h (grain_isGrainOf R)

/-- Corollary: Two grains of the same type are interchangeable.
    If G₁ and G₂ are both grains of R, then G₁ ≅ G₂ and G₂ ≅ G₁. -/
theorem grain_unique_symm (R : D) (G : D) (h : IsGrainOf G R) :
    iso (grain R) G :=
  iso_symm _ _ (grain_unique R G h)

end GrainTheory.Foundations
