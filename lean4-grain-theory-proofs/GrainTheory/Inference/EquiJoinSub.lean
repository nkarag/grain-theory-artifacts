/-
  GrainTheory.Inference.EquiJoinSub — Lemma A: candidate ⊆ Res

  Proves that the candidate grain F₁ = G[R₁] ∪ (G[R₂] \ Jk) is a
  type-subset of the join result Res.

  This is Condition 1 (sub-product step) of the equi-join grain
  inference theorem's sufficient condition.

  The join result schema is characterized by mutual containment
  (not isomorphism) to avoid the unsound iso_sub axiom:
    sub (prod ...) Res  (product embeds into Res)
    sub Res (prod ...)  (Res embeds into product)

  Reference: PODS 2027 paper, §6, Equi-join grain inference proof;
  THEORY_GAP_CASE_B.md §6 (sub-product step).
-/

import GrainTheory.Inference.EquiJoinAxioms

namespace GrainTheory.Inference

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub iso grain union inter diff prod
  sub_refl sub_trans sub_antisymm
  iso_refl iso_symm iso_trans
  grain_sub grain_iso grain_irred
  sub_union_left sub_union_right union_sub
  inter_sub_left inter_sub_right sub_inter
  sub_diff sub_union_diff
  sub_prod_left sub_prod_right)

/-- Helper: R₁ ⊆_typ Res, derived from the product join result schema.

    Given h_res_sup : sub P Res (product embeds into Res), derives R₁ ⊆ Res
    by showing R₁ ⊆ P (via product components) and then sub_trans. -/
private lemma input_sub_res₁ (R₁ R₂ Jk Res : D)
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : sub R₁ Res := by
  -- Abbreviate the product
  set P := prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk
  -- R₁ \ Jk ⊆ (R₁ \ Jk) × (R₂ \ Jk)
  have h1 : sub (diff R₁ Jk) (prod (diff R₁ Jk) (diff R₂ Jk)) :=
    sub_prod_left (diff R₁ Jk) (diff R₂ Jk)
  -- (R₁ \ Jk) × (R₂ \ Jk) ⊆ P
  have h2 : sub (prod (diff R₁ Jk) (diff R₂ Jk)) P :=
    sub_prod_left (prod (diff R₁ Jk) (diff R₂ Jk)) Jk
  -- R₁ \ Jk ⊆ P
  have h3 : sub (diff R₁ Jk) P :=
    sub_trans _ _ _ h1 h2
  -- Jk ⊆ P
  have h4 : sub Jk P :=
    sub_prod_right (prod (diff R₁ Jk) (diff R₂ Jk)) Jk
  -- R₁ ⊆ Jk ∪ (R₁ \ Jk)
  have h5 : sub R₁ (union Jk (diff R₁ Jk)) :=
    sub_union_diff R₁ Jk
  -- Jk ∪ (R₁ \ Jk) ⊆ P
  have h6 : sub (union Jk (diff R₁ Jk)) P :=
    union_sub Jk (diff R₁ Jk) P h4 h3
  -- R₁ ⊆ P
  have h7 : sub R₁ P := sub_trans _ _ _ h5 h6
  -- R₁ ⊆ Res via sub_trans (P ⊆ Res)
  exact sub_trans _ _ _ h7 h_res_sup

/-- Helper: R₂ ⊆_typ Res, derived from the product join result schema.

    Symmetric to input_sub_res₁: uses R₂ ⊆ Jk ∪ (R₂ \ Jk) and the fact
    that both Jk and R₂ \ Jk appear as product components in Res. -/
private lemma input_sub_res₂ (R₁ R₂ Jk Res : D)
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : sub R₂ Res := by
  set P := prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk
  -- R₂ \ Jk ⊆ (R₁ \ Jk) × (R₂ \ Jk)
  have h1 : sub (diff R₂ Jk) (prod (diff R₁ Jk) (diff R₂ Jk)) :=
    sub_prod_right (diff R₁ Jk) (diff R₂ Jk)
  -- (R₁ \ Jk) × (R₂ \ Jk) ⊆ P
  have h2 : sub (prod (diff R₁ Jk) (diff R₂ Jk)) P :=
    sub_prod_left (prod (diff R₁ Jk) (diff R₂ Jk)) Jk
  -- R₂ \ Jk ⊆ P
  have h3 : sub (diff R₂ Jk) P :=
    sub_trans _ _ _ h1 h2
  -- Jk ⊆ P
  have h4 : sub Jk P :=
    sub_prod_right (prod (diff R₁ Jk) (diff R₂ Jk)) Jk
  -- R₂ ⊆ Jk ∪ (R₂ \ Jk)
  have h5 : sub R₂ (union Jk (diff R₂ Jk)) :=
    sub_union_diff R₂ Jk
  -- Jk ∪ (R₂ \ Jk) ⊆ P
  have h6 : sub (union Jk (diff R₂ Jk)) P :=
    union_sub Jk (diff R₂ Jk) P h4 h3
  -- R₂ ⊆ P
  have h7 : sub R₂ P := sub_trans _ _ _ h5 h6
  -- R₂ ⊆ Res via sub_trans (P ⊆ Res)
  exact sub_trans _ _ _ h7 h_res_sup

/-- **Lemma A (Equi-Join Candidate ⊆ Res).** PODS §6, sub-product step.

    The candidate grain F₁ = G[R₁] ∪_typ (G[R₂] \_typ Jk) is a
    type-subset of the join result Res.

    **Given:**
    - Jk ⊆_typ R₁, Jk ⊆_typ R₂  (join key is in both inputs)
    - (R₁ \ Jk) × (R₂ \ Jk) × Jk ⊆_typ Res  (product embeds into Res)

    **Proof:**
    - G[R₁] ⊆_typ R₁ ⊆_typ Res  (grain_sub + input_sub_res₁)
    - G[R₂] \ Jk ⊆_typ G[R₂] ⊆_typ R₂ ⊆_typ Res  (sub_diff + grain_sub + input_sub_res₂)
    - union_sub combines both into F₁ ⊆_typ Res -/
theorem equijoin_candidate_sub
    (R₁ R₂ Jk Res : D)
    (_h_jk_r1 : sub Jk R₁) (_h_jk_r2 : sub Jk R₂)
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : sub (union (grain R₁) (diff (grain R₂) Jk)) Res := by
  -- Part 1: G[R₁] ⊆_typ Res
  have h_gr1_r1 : sub (grain R₁) R₁ := grain_sub R₁
  have h_r1_res : sub R₁ Res := input_sub_res₁ R₁ R₂ Jk Res h_res_sup
  have h_gr1_res : sub (grain R₁) Res :=
    sub_trans _ _ _ h_gr1_r1 h_r1_res
  -- Part 2: G[R₂] \ Jk ⊆_typ Res
  have h_diff_gr2 : sub (diff (grain R₂) Jk) (grain R₂) := sub_diff (grain R₂) Jk
  have h_gr2_r2 : sub (grain R₂) R₂ := grain_sub R₂
  have h_r2_res : sub R₂ Res := input_sub_res₂ R₁ R₂ Jk Res h_res_sup
  have h_diff_res : sub (diff (grain R₂) Jk) Res :=
    sub_trans _ _ _ (sub_trans _ _ _ h_diff_gr2 h_gr2_r2) h_r2_res
  -- Part 3: G[R₁] ∪ (G[R₂] \ Jk) ⊆_typ Res
  exact union_sub _ _ _ h_gr1_res h_diff_res

end GrainTheory.Inference
