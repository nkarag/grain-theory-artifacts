/-
  GrainTheory.Relations.Incomparability — Grain incomparability (PODS §4.3)

  PODS Definition 6: R₁ #_g R₂ iff ¬(R₁ ≤_g R₂) ∧ ¬(R₂ ≤_g R₁).

  Results:
  - Definition: grainIncomp R₁ R₂
  - Theorem (Incomparability Preservation): R₁ #_g R₂ ⟺ G[R₁] #_g G[R₂]
  - Corollary: grainIncomp implies ¬grainEq (the ¬≡_g condition in PODS Def 6
    is redundant given ¬≤_g in both directions)
  - Irreflexivity and symmetry (not transitive)

  The preservation theorem follows directly from grainLe_preservation (LP-13).
-/

import GrainTheory.Relations.GrainOrdering

namespace GrainTheory.Relations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-! ## Grain Incomparability (PODS Def 6) -/

/-- PODS Definition 6: Grain incomparability.
    R₁ #_g R₂ iff neither R₁ ≤_g R₂ nor R₂ ≤_g R₁.

    The PODS paper also includes ¬(R₁ ≡_g R₂), but this is redundant:
    grain equality implies grain ordering in both directions (via iso_sub),
    so ¬(R₁ ≤_g R₂) already entails ¬(R₁ ≡_g R₂). See `grainIncomp_not_eq`. -/
def grainIncomp (R₁ R₂ : D) : Prop := ¬grainLe R₁ R₂ ∧ ¬grainLe R₂ R₁

scoped infixl:50 " #_g " => grainIncomp

/-! ## Basic Properties -/

/-- Grain incomparability is irreflexive: no type is incomparable with itself. -/
theorem grainIncomp_irrefl (R : D) : ¬grainIncomp R R := by
  intro ⟨h, _⟩
  exact h (grainLe_refl R)

/-- Grain incomparability is symmetric: R₁ #_g R₂ → R₂ #_g R₁. -/
theorem grainIncomp_symm {R₁ R₂ : D} (h : grainIncomp R₁ R₂) : grainIncomp R₂ R₁ :=
  ⟨h.2, h.1⟩

/-- Grain equality implies grain ordering (forward direction).
    If R₁ ≡_g R₂, then R₁ ≤_g R₂.

    Proof: grainEq R₁ R₂ = iso (grain R₁) (grain R₂).
    By iso_sub with sub_refl, we get sub (grain R₂) (grain R₁) = grainLe R₁ R₂. -/
theorem grainLe_of_grainEq {R₁ R₂ : D} (h : grainEq R₁ R₂) : grainLe R₁ R₂ :=
  iso_sub _ _ _ h (sub_refl (grain R₂))

/-- Grain equality implies grain ordering (reverse direction).
    If R₁ ≡_g R₂, then R₂ ≤_g R₁. -/
theorem grainLe_of_grainEq' {R₁ R₂ : D} (h : grainEq R₁ R₂) : grainLe R₂ R₁ :=
  iso_sub _ _ _ (iso_symm _ _ h) (sub_refl (grain R₁))

/-- PODS Def 6 redundancy: grain incomparability implies ¬grainEq.
    The ¬(R₁ ≡_g R₂) condition in the PODS definition is redundant,
    because grain equality implies ≤_g in both directions. -/
theorem grainIncomp_not_eq {R₁ R₂ : D} (h : grainIncomp R₁ R₂) : ¬grainEq R₁ R₂ := by
  intro heq
  exact h.1 (grainLe_of_grainEq heq)

/-! ## Incomparability Preservation -/

/-- PODS Theorem (Grain Incomparability Preservation):
    R₁ #_g R₂ ⟺ G[R₁] #_g G[R₂].

    Both directions follow from grainLe_preservation:
    R₁ ≤_g R₂ ⟺ G[R₁] ≤_g G[R₂] (and similarly with R₁, R₂ swapped).

    (⟹) If G[R₁] ≤_g G[R₂], then R₁ ≤_g R₂ — contradicting the hypothesis.
    (⟸) If R₁ ≤_g R₂, then G[R₁] ≤_g G[R₂] — contradicting the hypothesis. -/
theorem grainIncomp_preservation (R₁ R₂ : D) :
    grainIncomp R₁ R₂ ↔ grainIncomp (grain R₁) (grain R₂) := by
  constructor
  · intro ⟨h₁, h₂⟩
    exact ⟨fun hle => h₁ ((grainLe_preservation R₁ R₂).mpr hle),
           fun hle => h₂ ((grainLe_preservation R₂ R₁).mpr hle)⟩
  · intro ⟨h₁, h₂⟩
    exact ⟨fun hle => h₁ ((grainLe_preservation R₁ R₂).mp hle),
           fun hle => h₂ ((grainLe_preservation R₂ R₁).mp hle)⟩

end GrainTheory.Relations
