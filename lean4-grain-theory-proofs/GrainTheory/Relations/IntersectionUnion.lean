/-
  GrainTheory.Relations.IntersectionUnion — Lattice absorption laws

  PODS Theorem (Lattice Absorption): For any data types R₁, R₂ with
  R₂ ≤_g R₁ (equivalently G[R₁] ⊆_typ G[R₂] by Thm Grain Subset):
    G[R₁ ∩ R₂] ≡_g G[R₁]   (lub absorbs to coarser grain)
    G[R₁ ∪ R₂] ≡_g G[R₂]   (glb absorbs to finer grain)

  These are the standard lattice absorption laws applied to the grain
  lattice, with ∩_typ as the lub and ∪_typ as the glb. The lub/glb
  characterization extends naturally to any algebraic data type
  (PODS §2 natural-extension paragraph); the field-set formulas
  realize it on product types.

  Mechanized as two lemmas (intersection_grain, union_grain) plus a
  combined theorem (lattice_absorption). Both lemmas verify the
  conditions of the Grain Inference Sufficient Condition for the
  appropriate G and target type.

  Reference: PODS 2027 paper, §4.3, Theorem (Lattice Absorption);
  Appendix proof.
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
    (h_int₁ : ssub (grain R₁) R₁) (h : ssub (grain R₁) (grain R₂))
    (h_int₂ : ssub (grain R₂) R₂) :
    grainEq R₁ (inter R₁ R₂) := by
  -- Condition (i): G[R₁] ⊆_typ (R₁ ∩ R₂)
  -- Structural containment throughout: `inter` is the field-set operation, and
  -- the semantic glb property it would otherwise need is FALSE
  -- (`Model/AxiomCheck.lean`). See the note on the theorem statement.
  have h_sub_R₂ : ssub (grain R₁) R₂ := ssub_trans _ _ _ h h_int₂
  have h_sub_inter : sub (grain R₁) (inter R₁ R₂) :=
    ssub_sub _ _ (ssub_inter _ _ _ h_int₁ h_sub_R₂)
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

    Condition (iii): G[R₁] is irreducible (`grain_irreducible`). -/
theorem intersection_grain_isGrainOf {R₁ R₂ : D}
    (h_int₁ : ssub (grain R₁) R₁) (h : ssub (grain R₁) (grain R₂))
    (h_int₂ : ssub (grain R₂) R₂) :
    Foundations.IsGrainOf (grain R₁) (inter R₁ R₂) := by
  -- Structural containment throughout: `inter` is the field-set operation, and
  -- the semantic glb property it would otherwise need is FALSE
  -- (`Model/AxiomCheck.lean`). See the note on the theorem statement.
  have h_sub_R₂ : ssub (grain R₁) R₂ := ssub_trans _ _ _ h h_int₂
  have h_sub_inter : sub (grain R₁) (inter R₁ R₂) :=
    ssub_sub _ _ (ssub_inter _ _ _ h_int₁ h_sub_R₂)
  have h_le : grainLe (grain R₁) (inter R₁ R₂) :=
    grain_determines_subsets (inter_sub_left R₁ R₂)
  -- Condition (iii): G[R₁] is structurally irreducible — directly from the
  -- grain axioms, no transport across an isomorphism required.
  have h_irred : Foundations.IsIrreducible (grain R₁) :=
    Foundations.grain_irreducible R₁
  exact grain_inference_isGrainOf h_sub_inter h_le h_irred

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

    Condition (iii): G[R₂] is irreducible (`grain_irreducible`). -/
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
  -- Condition (iii): G[R₂] is structurally irreducible.
  have h_irred : Foundations.IsIrreducible (grain R₂) :=
    Foundations.grain_irreducible R₂
  exact grain_inference_isGrainOf h_sub_union h_le h_irred

/-! ## PODS Theorem: Lattice Absorption (combined) -/

/-- PODS Thm (Lattice Absorption): Both absorption laws of the grain
    lattice combined. When G[R₁] ⊆_typ G[R₂] (equivalently R₂ ≤_g R₁
    by the Grain Subset Theorem):
      - G[R₁ ∩ R₂] ≡_g G[R₁]   (lub absorbs to coarser grain)
      - G[R₁ ∪ R₂] ≡_g G[R₂]   (glb absorbs to finer grain)

    Direct corollary of intersection_grain and union_grain. -/
theorem lattice_absorption {R₁ R₂ : D}
    (h_int₁ : ssub (grain R₁) R₁) (h : ssub (grain R₁) (grain R₂))
    (h_int₂ : ssub (grain R₂) R₂) :
    grainEq R₁ (inter R₁ R₂) ∧ grainEq R₂ (union R₁ R₂) :=
  ⟨intersection_grain h_int₁ h h_int₂, union_grain (ssub_sub _ _ h)⟩

end GrainTheory.Relations
