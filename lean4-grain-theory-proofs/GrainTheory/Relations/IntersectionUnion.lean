/-
  GrainTheory.Relations.IntersectionUnion — Intersection and union with grain

  PODS Theorem intersection-grain:
    If G[R₁] ⊆_typ G[R₂], then R₁ ≡_g (R₁ ∩ R₂).
    Equivalently: G[R₁] ≡_g G[R₁ ∩ R₂].

  PODS Theorem union-grain:
    If G[R₁] ⊆_typ G[R₂], then R₂ ≡_g (R₁ ∪ R₂).
    Equivalently: G[R₂] ≡_g G[R₁ ∪ R₂].

  Both proofs verify the conditions of the Grain Inference Sufficient
  Condition (Theorem 4.9) for the appropriate G and target type.

  Reference: PODS 2027 paper, §4, Theorems 4.10-4.11; Appendix proofs.
-/

import GrainTheory.Relations.GrainInference
import GrainTheory.Relations.GrainSubset
import GrainTheory.Relations.Armstrong

namespace GrainTheory.Relations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-! ## PODS Theorem: Intersection with Grain -/

/-- PODS Thm (Intersection with Grain):
    If G[R₁] ⊆_typ G[R₂], then R₁ ≡_g (R₁ ∩ R₂).
    Equivalently: G[R₁] ≡_g G[R₁ ∩ R₂] (grain equivalence of grains).

    Intersecting two types whose grains are ordered preserves the coarser
    grain: since G[R₁]'s fields appear in both R₁ and R₂, they survive
    the intersection intact.

    Proof via grain inference (conditions (i) and (ii)):
    (i) G[R₁] ⊆_typ (R₁ ∩ R₂): G[R₁] ⊆ R₁ (grain_sub) and
        G[R₁] ⊆ G[R₂] ⊆ R₂ (premise + grain_sub), so by sub_inter,
        G[R₁] ⊆ R₁ ∩ R₂.
    (ii) G[R₁] ≤_g (R₁ ∩ R₂): since (R₁ ∩ R₂) ⊆ R₁, by
        grain_determines_subsets, grain(R₁) ≤_g (R₁ ∩ R₂).

    grain_inference gives grainEq (grain R₁) (grain (inter R₁ R₂)),
    which is grainEq R₁ (inter R₁ R₂) by idempotency (applied on both sides). -/
theorem intersection_grain {R₁ R₂ : D}
    (h : sub (grain R₁) (grain R₂)) :
    grainEq R₁ (inter R₁ R₂) := by
  -- Condition (i): G[R₁] ⊆_typ (R₁ ∩ R₂)
  have h_sub_R₁ : sub (grain R₁) R₁ := grain_sub R₁
  have h_sub_R₂ : sub (grain R₁) R₂ :=
    sub_trans _ _ _ h (grain_sub R₂)
  have h_sub_inter : sub (grain R₁) (inter R₁ R₂) :=
    sub_inter _ _ _ h_sub_R₁ h_sub_R₂
  -- Condition (ii): G[R₁] ≤_g (R₁ ∩ R₂)
  -- (R₁ ∩ R₂) ⊆_typ R₁, so grain_determines_subsets gives grainLe (grain R₁) (R₁ ∩ R₂)
  have h_le : grainLe (grain R₁) (inter R₁ R₂) :=
    grain_determines_subsets (inter_sub_left R₁ R₂)
  -- grain_inference gives: grainEq (grain R₁) (grain (inter R₁ R₂))
  -- i.e., iso (grain (grain R₁)) (grain (grain (inter R₁ R₂)))
  have h_eqg := grain_inference h_sub_inter h_le
  -- Compose with idempotency on both sides to get iso (grain R₁) (grain (inter R₁ R₂))
  -- i.e., grainEq R₁ (inter R₁ R₂)
  exact iso_trans _ _ _ (iso_symm _ _ (Foundations.grain_idempotent R₁))
    (iso_trans _ _ _ h_eqg (Foundations.grain_idempotent (inter R₁ R₂)))

/-- PODS Thm (Intersection with Grain, strengthened to IsGrainOf):
    If G[R₁] ⊆_typ G[R₂], then IsGrainOf (grain R₁) (R₁ ∩ R₂):
    G[R₁] is a grain of (R₁ ∩ R₂) — not just grain-equivalent, but
    satisfying both isomorphism and irreducibility.

    Condition (iii): G[G[R₁]] ≅ G[R₁] by grain idempotency. -/
theorem intersection_grain_isGrainOf {R₁ R₂ : D}
    (h : sub (grain R₁) (grain R₂)) :
    Foundations.IsGrainOf (grain R₁) (inter R₁ R₂) := by
  have h_sub_R₁ : sub (grain R₁) R₁ := grain_sub R₁
  have h_sub_R₂ : sub (grain R₁) R₂ :=
    sub_trans _ _ _ h (grain_sub R₂)
  have h_sub_inter : sub (grain R₁) (inter R₁ R₂) :=
    sub_inter _ _ _ h_sub_R₁ h_sub_R₂
  have h_le : grainLe (grain R₁) (inter R₁ R₂) :=
    grain_determines_subsets (inter_sub_left R₁ R₂)
  have h_idem : iso (grain (grain R₁)) (grain R₁) :=
    Foundations.grain_idempotent R₁
  exact grain_inference_isGrainOf h_sub_inter h_le h_idem

/-! ## PODS Theorem: Union with Grain -/

/-- PODS Thm (Union with Grain):
    If G[R₁] ⊆_typ G[R₂], then R₂ ≡_g (R₁ ∪ R₂).
    Equivalently: G[R₂] ≡_g G[R₁ ∪ R₂] (grain equivalence of grains).

    This is the dual of intersection-grain: while ∩ preserves the coarser
    grain, ∪ preserves the finer grain. Adding R₁'s fields to R₂ via union
    does not make the grain finer, because G[R₂] already functionally
    determines all of R₁'s fields.

    Proof via grain inference (conditions (i) and (ii)):
    (i) G[R₂] ⊆_typ (R₁ ∪ R₂): G[R₂] ⊆ R₂ ⊆ (R₁ ∪ R₂).
    (ii) G[R₂] ≤_g (R₁ ∪ R₂): by armstrong A5 from
        G[R₂] ≤_g R₂ and G[R₂] ≤_g R₁ (the latter via
        G[R₁] ⊆ G[R₂] → grainLe (grain R₂) R₁). -/
theorem union_grain {R₁ R₂ : D}
    (h : sub (grain R₁) (grain R₂)) :
    grainEq R₂ (union R₁ R₂) := by
  -- Condition (i): G[R₂] ⊆_typ (R₁ ∪ R₂)
  have h_sub_union : sub (grain R₂) (union R₁ R₂) :=
    sub_trans _ _ _ (grain_sub R₂) (sub_union_right R₁ R₂)
  -- Condition (ii): G[R₂] ≤_g (R₁ ∪ R₂)
  -- First: G[R₂] ≤_g R₂ (grain determines its own type)
  have h_le_R₂ : grainLe (grain R₂) R₂ :=
    grain_determines_subsets (sub_refl R₂)
  -- Second: G[R₂] ≤_g R₁
  -- grainLe (grain R₂) R₁ = sub (grain R₁) (grain (grain R₂))
  -- From h + idempotency: iso_sub transfers sub (grain R₁) (grain R₂) to
  -- sub (grain R₁) (grain (grain R₂))
  have h_le_R₁ : grainLe (grain R₂) R₁ :=
    iso_sub _ _ _ (Foundations.grain_idempotent R₂) h
  -- A5 (Union): G[R₂] ≤_g R₁ ∧ G[R₂] ≤_g R₂ → G[R₂] ≤_g (R₁ ∪ R₂)
  have h_le : grainLe (grain R₂) (union R₁ R₂) :=
    armstrong_A5 h_le_R₁ h_le_R₂
  -- grain_inference gives: grainEq (grain R₂) (grain (union R₁ R₂))
  have h_eqg := grain_inference h_sub_union h_le
  -- Compose with idempotency on both sides
  exact iso_trans _ _ _ (iso_symm _ _ (Foundations.grain_idempotent R₂))
    (iso_trans _ _ _ h_eqg (Foundations.grain_idempotent (union R₁ R₂)))

/-- PODS Thm (Union with Grain, strengthened to IsGrainOf):
    If G[R₁] ⊆_typ G[R₂], then IsGrainOf (grain R₂) (R₁ ∪ R₂):
    G[R₂] is a grain of (R₁ ∪ R₂).

    Condition (iii): G[G[R₂]] ≅ G[R₂] by grain idempotency. -/
theorem union_grain_isGrainOf {R₁ R₂ : D}
    (h : sub (grain R₁) (grain R₂)) :
    Foundations.IsGrainOf (grain R₂) (union R₁ R₂) := by
  have h_sub_union : sub (grain R₂) (union R₁ R₂) :=
    sub_trans _ _ _ (grain_sub R₂) (sub_union_right R₁ R₂)
  have h_le_R₂ : grainLe (grain R₂) R₂ :=
    grain_determines_subsets (sub_refl R₂)
  have h_le_R₁ : grainLe (grain R₂) R₁ :=
    iso_sub _ _ _ (Foundations.grain_idempotent R₂) h
  have h_le : grainLe (grain R₂) (union R₁ R₂) :=
    armstrong_A5 h_le_R₁ h_le_R₂
  have h_idem : iso (grain (grain R₂)) (grain R₂) :=
    Foundations.grain_idempotent R₂
  exact grain_inference_isGrainOf h_sub_union h_le h_idem

end GrainTheory.Relations
