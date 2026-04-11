/-
  GrainTheory.Relations.GrainEquality — Grain equality (PODS §4.1)

  PODS Definition 4: R₁ ≡_g R₂ iff G[R₁] ≅ G[R₂].

  Results:
  - Equivalence relation: reflexive, symmetric, transitive
  - Theorem 4.2: R₁ ≡_g R₂ ⟺ R₁ ≅ R₂
  - Corollary (Preservation): R₁ ≡_g R₂ ⟺ G[R₁] ≡_g G[R₂]

  The definition `grainEq` lives in GrainOrdering.lean (needed by
  grainLe_antisymm). This file imports it and proves all properties.
-/

import GrainTheory.Relations.GrainOrdering
import GrainTheory.Foundations.Idempotency

namespace GrainTheory.Relations

variable {D : Type*} [GrainStructure D]

open GrainStructure (iso grain iso_refl iso_symm iso_trans grain_iso)

/-! ## Equivalence Relation Properties -/

/-- Grain equality is reflexive: R ≡_g R. -/
theorem grainEq_refl (R : D) : grainEq R R :=
  iso_refl (grain R)

/-- Grain equality is symmetric: R₁ ≡_g R₂ → R₂ ≡_g R₁. -/
theorem grainEq_symm {R₁ R₂ : D} (h : grainEq R₁ R₂) : grainEq R₂ R₁ :=
  iso_symm _ _ h

/-- Grain equality is transitive: R₁ ≡_g R₂ → R₂ ≡_g R₃ → R₁ ≡_g R₃. -/
theorem grainEq_trans {R₁ R₂ R₃ : D}
    (h₁ : grainEq R₁ R₂) (h₂ : grainEq R₂ R₃) : grainEq R₁ R₃ :=
  iso_trans _ _ _ h₁ h₂

/-! ## Theorem 4.2: Grain Equality ⟺ Isomorphism -/

/-- PODS Theorem 4.2 (⟸): Isomorphic types have equal grain.
    If R₁ ≅ R₂, then G[R₁] ≅ G[R₂].

    Proof: G[R₁] ≅ R₁ ≅ R₂ ≅⁻¹ G[R₂]. -/
theorem grainEq_of_iso {R₁ R₂ : D} (h : iso R₁ R₂) : grainEq R₁ R₂ :=
  iso_trans _ _ _ (iso_trans _ _ _ (grain_iso R₁) h) (iso_symm _ _ (grain_iso R₂))

/-- PODS Theorem 4.2 (⟹): Equal grain implies isomorphism.
    If G[R₁] ≅ G[R₂], then R₁ ≅ R₂.

    Proof: R₁ ≅⁻¹ G[R₁] ≅ G[R₂] ≅ R₂. -/
theorem iso_of_grainEq {R₁ R₂ : D} (h : grainEq R₁ R₂) : iso R₁ R₂ :=
  iso_trans _ _ _ (iso_symm _ _ (grain_iso R₁)) (iso_trans _ _ _ h (grain_iso R₂))

/-- PODS Theorem 4.2: R₁ ≡_g R₂ ⟺ R₁ ≅ R₂. -/
theorem grainEq_iff_iso (R₁ R₂ : D) : grainEq R₁ R₂ ↔ iso R₁ R₂ :=
  ⟨iso_of_grainEq, grainEq_of_iso⟩

/-! ## Corollary: Grain Equality Preservation -/

/-- PODS Corollary (Grain Equality Preservation):
    R₁ ≡_g R₂ ⟺ G[R₁] ≡_g G[R₂].

    (⟹) grainEq R₁ R₂ = iso (grain R₁) (grain R₂).
    By idempotency, grain (grain Rᵢ) ≅ grain Rᵢ, so we can
    transport the iso to iso (grain (grain R₁)) (grain (grain R₂)).

    (⟸) Same argument in reverse. -/
theorem grainEq_preservation (R₁ R₂ : D) :
    grainEq R₁ R₂ ↔ grainEq (grain R₁) (grain R₂) := by
  constructor
  · intro h
    -- h : iso (grain R₁) (grain R₂)
    -- Goal: iso (grain (grain R₁)) (grain (grain R₂))
    -- grain_idempotent : iso (grain (grain Rᵢ)) (grain Rᵢ)
    -- Need: iso (grain (grain R₁)) (grain R₁) then h then iso (grain R₂) (grain (grain R₂))
    exact iso_trans _ _ _
      (Foundations.grain_idempotent R₁)
      (iso_trans _ _ _ h (iso_symm _ _ (Foundations.grain_idempotent R₂)))
  · intro h
    -- h : iso (grain (grain R₁)) (grain (grain R₂))
    -- Goal: iso (grain R₁) (grain R₂)
    exact iso_trans _ _ _
      (iso_symm _ _ (Foundations.grain_idempotent R₁))
      (iso_trans _ _ _ h (Foundations.grain_idempotent R₂))

end GrainTheory.Relations
