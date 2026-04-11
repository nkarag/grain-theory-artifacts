/-
  GrainTheory.Relations.Armstrong — Armstrong axioms A1-A9

  PODS §4: Soundness of grain axioms for the grain ordering.
  A1 (self-determination), A2 (reflexivity), A4 (transitivity) are
  re-exports of prior results. A3 (augmentation) is the key new axiom,
  requiring grain_union. A5-A9 derive from A1-A4 + structural axioms.
-/

import GrainTheory.Relations.GrainOrdering
import GrainTheory.Relations.GrainSubset

namespace GrainTheory.Relations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-! ## Helper lemmas -/

/-- From iso we can extract sub in forward direction: A ≅ B → A ⊆_typ B -/
theorem sub_of_iso {A B : D} (h : iso A B) : sub A B :=
  iso_sub B A A (iso_symm _ _ h) (sub_refl A)

/-- From iso we can extract sub in reverse direction: A ≅ B → B ⊆_typ A -/
theorem sub_of_iso_rev {A B : D} (h : iso A B) : sub B A :=
  iso_sub A B B h (sub_refl B)

/-! ## Armstrong Axioms A1-A9 -/

/-- A1 (Self-determination): R ≤_g R -/
theorem armstrong_A1 (R : D) : grainLe R R :=
  grainLe_refl R

/-- A2 (Reflexivity / Subset): G[R₁] ⊆_typ G[R₂] → R₂ ≤_g R₁ -/
theorem armstrong_A2 {R₁ R₂ : D} (h : sub (grain R₁) (grain R₂)) : grainLe R₂ R₁ :=
  grain_subset h

/-- A3 (Augmentation): R₁ ≤_g R₂ → (R₁ ∪ R₃) ≤_g (R₂ ∪ R₃)

    Proof sketch: Via grain_union, reduce to showing
    union(G[R₂])(G[R₃]) ⊆_typ union(G[R₁])(G[R₃]),
    which follows from the hypothesis G[R₂] ⊆_typ G[R₁]. -/
theorem armstrong_A3 {R₁ R₂ R₃ : D}
    (h : grainLe R₁ R₂) : grainLe (union R₁ R₃) (union R₂ R₃) := by
  -- h : sub (grain R₂) (grain R₁)
  -- Goal: sub (grain (union R₂ R₃)) (grain (union R₁ R₃))
  have hiso₁ := grain_union R₁ R₃
  have hiso₂ := grain_union R₂ R₃
  -- sub (grain R₂) (union (grain R₁) (grain R₃))
  have h1 : sub (grain R₂) (union (grain R₁) (grain R₃)) :=
    sub_trans _ _ _ h (sub_union_left (grain R₁) (grain R₃))
  -- sub (union (grain R₂) (grain R₃)) (union (grain R₁) (grain R₃))
  have h2 : sub (union (grain R₂) (grain R₃)) (union (grain R₁) (grain R₃)) :=
    union_sub _ _ _ h1 (sub_union_right (grain R₁) (grain R₃))
  -- Chain: grain(R₂∪R₃) ⊆ union(G[R₂])(G[R₃]) ⊆ union(G[R₁])(G[R₃]) ⊆ grain(R₁∪R₃)
  exact sub_trans _ _ _ (sub_trans _ _ _ (sub_of_iso hiso₂) h2) (sub_of_iso_rev hiso₁)

/-- A4 (Transitivity): R₁ ≤_g R₂ → R₂ ≤_g R₃ → R₁ ≤_g R₃ -/
theorem armstrong_A4 {R₁ R₂ R₃ : D}
    (h₁ : grainLe R₁ R₂) (h₂ : grainLe R₂ R₃) : grainLe R₁ R₃ :=
  grainLe_trans h₁ h₂

/-- A5 (Union): R₁ ≤_g R₂ → R₁ ≤_g R₃ → R₁ ≤_g (R₂ ∪ R₃)

    If R₁ is finer than both R₂ and R₃, it is finer than their union. -/
theorem armstrong_A5 {R₁ R₂ R₃ : D}
    (h₁ : grainLe R₁ R₂) (h₂ : grainLe R₁ R₃) : grainLe R₁ (union R₂ R₃) := by
  -- h₁ : sub (grain R₂) (grain R₁), h₂ : sub (grain R₃) (grain R₁)
  -- Goal: sub (grain (union R₂ R₃)) (grain R₁)
  have hiso := grain_union R₂ R₃
  exact sub_trans _ _ _ (sub_of_iso hiso) (union_sub _ _ _ h₁ h₂)

/-- A6 (Decomposition): R₁ ≤_g (R₂ ∪ R₃) → R₁ ≤_g R₂ ∧ R₁ ≤_g R₃

    If R₁ is finer than a union, it is finer than each component. -/
theorem armstrong_A6 {R₁ R₂ R₃ : D}
    (h : grainLe R₁ (union R₂ R₃)) : grainLe R₁ R₂ ∧ grainLe R₁ R₃ := by
  -- h : sub (grain (union R₂ R₃)) (grain R₁)
  have hiso := grain_union R₂ R₃
  have hmid : sub (union (grain R₂) (grain R₃)) (grain (union R₂ R₃)) :=
    sub_of_iso_rev hiso
  exact ⟨sub_trans _ _ _ (sub_trans _ _ _ (sub_union_left _ _) hmid) h,
         sub_trans _ _ _ (sub_trans _ _ _ (sub_union_right _ _) hmid) h⟩

/-- A7 (Composition): R₁ ≤_g R₂ → R₃ ≤_g R₄ → (R₁ ∪ R₃) ≤_g (R₂ ∪ R₄) -/
theorem armstrong_A7 {R₁ R₂ R₃ R₄ : D}
    (h₁ : grainLe R₁ R₂) (h₂ : grainLe R₃ R₄) :
    grainLe (union R₁ R₃) (union R₂ R₄) := by
  -- h₁ : sub (grain R₂) (grain R₁), h₂ : sub (grain R₄) (grain R₃)
  -- Goal: sub (grain (union R₂ R₄)) (grain (union R₁ R₃))
  have hiso₁ := grain_union R₁ R₃
  have hiso₂ := grain_union R₂ R₄
  have ha : sub (grain R₂) (union (grain R₁) (grain R₃)) :=
    sub_trans _ _ _ h₁ (sub_union_left _ _)
  have hb : sub (grain R₄) (union (grain R₁) (grain R₃)) :=
    sub_trans _ _ _ h₂ (sub_union_right _ _)
  have hc : sub (union (grain R₂) (grain R₄)) (union (grain R₁) (grain R₃)) :=
    union_sub _ _ _ ha hb
  exact sub_trans _ _ _ (sub_trans _ _ _ (sub_of_iso hiso₂) hc) (sub_of_iso_rev hiso₁)

/-- A8 (Pseudotransitivity): R₁ ≤_g R₂ → (R₂ ∪ R₄) ≤_g R₃ → (R₁ ∪ R₄) ≤_g R₃

    Follows from A3 + A4: augment R₁≤R₂ with R₄, then compose. -/
theorem armstrong_A8 {R₁ R₂ R₃ R₄ : D}
    (h₁ : grainLe R₁ R₂) (h₂ : grainLe (union R₂ R₄) R₃) :
    grainLe (union R₁ R₄) R₃ :=
  grainLe_trans (armstrong_A3 h₁) h₂

/-- A9 (Darwen's Theorem): R₁ ≤_g R₂ → R₃ ≤_g R₄ → (R₁ ∪ (R₃ \ R₂)) ≤_g (R₂ ∪ R₄)

    Key insight: sub_union_diff gives R₃ ⊆_typ R₂ ∪ (R₃\R₂), which lets us
    chain G[R₃] through G[R₂ ∪ (R₃\R₂)] to reach union(G[R₁])(G[R₃\R₂]). -/
theorem armstrong_A9 {R₁ R₂ R₃ R₄ : D}
    (h₁ : grainLe R₁ R₂) (h₂ : grainLe R₃ R₄) :
    grainLe (union R₁ (diff R₃ R₂)) (union R₂ R₄) := by
  -- h₁ : sub (grain R₂) (grain R₁), h₂ : sub (grain R₄) (grain R₃)
  -- Goal: sub (grain (union R₂ R₄)) (grain (union R₁ (diff R₃ R₂)))
  have hiso_L := grain_union R₁ (diff R₃ R₂)
  have hiso_R := grain_union R₂ R₄
  -- Part A: sub (grain R₂) (union (grain R₁) (grain (diff R₃ R₂)))
  have ha : sub (grain R₂) (union (grain R₁) (grain (diff R₃ R₂))) :=
    sub_trans _ _ _ h₁ (sub_union_left _ _)
  -- Part B: sub (grain R₄) (union (grain R₁) (grain (diff R₃ R₂)))
  -- Chain: G[R₄] ⊆ G[R₃] ⊆ G[R₂∪(R₃\R₂)] ⊆ union(G[R₂])(G[R₃\R₂]) ⊆ union(G[R₁])(G[R₃\R₂])
  have h_R₃_sub : sub R₃ (grain (union R₂ (diff R₃ R₂))) :=
    iso_sub _ _ _ (grain_iso (union R₂ (diff R₃ R₂))) (sub_union_diff R₃ R₂)
  have h_gR₃_sub : sub (grain R₃) (grain (union R₂ (diff R₃ R₂))) :=
    sub_trans _ _ _ (grain_sub R₃) h_R₃_sub
  have h_expand : sub (grain (union R₂ (diff R₃ R₂))) (union (grain R₂) (grain (diff R₃ R₂))) :=
    sub_of_iso (grain_union R₂ (diff R₃ R₂))
  have h_shift : sub (union (grain R₂) (grain (diff R₃ R₂)))
      (union (grain R₁) (grain (diff R₃ R₂))) :=
    union_sub _ _ _ (sub_trans _ _ _ h₁ (sub_union_left _ _)) (sub_union_right _ _)
  have hb : sub (grain R₄) (union (grain R₁) (grain (diff R₃ R₂))) :=
    sub_trans _ _ _ h₂
      (sub_trans _ _ _ h_gR₃_sub (sub_trans _ _ _ h_expand h_shift))
  -- Combine and transfer via iso
  have hmid : sub (union (grain R₂) (grain R₄)) (union (grain R₁) (grain (diff R₃ R₂))) :=
    union_sub _ _ _ ha hb
  exact sub_trans _ _ _ (sub_trans _ _ _ (sub_of_iso hiso_R) hmid) (sub_of_iso_rev hiso_L)

end GrainTheory.Relations
