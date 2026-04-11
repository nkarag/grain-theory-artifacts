/-
  GrainTheory.Inference.JoinSpecialCases — Join special cases (LP-23)

  PODS Proposition 6.2: Four specializations of the equi-join grain
  inference theorem (Theorem 6.1 / `equijoin_grain_identity`):

  1. Equal grains (G[R₁] ≡_g G[R₂], G[R₁] ⊆ Jk):
     G[Res] = G[R₁]  (both grains are contained in Jk)

  2. Ordered grains (R₁ ≤_g R₂, G[R₂] ⊆ Jk):
     G[Res] = G[R₁]  (the finer grain is preserved)

  3. Incomparable grains (G[R₁] #_g G[R₂]):
     Both labelings yield IsGrainOf (no naming convention needed)

  4. Natural join (Jk = R₁ ∩ R₂):
     G[Res] = G[R₁] ∪_typ (G[R₂] -_typ R₁)

  Each case is a corollary of `equijoin_grain_identity` from EquiJoin.lean.
-/

import GrainTheory.Inference.EquiJoin
import GrainTheory.Relations.GrainEquality
import GrainTheory.Relations.Incomparability

namespace GrainTheory.Inference

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub iso grain union inter diff prod
  sub_refl sub_trans sub_antisymm
  iso_refl iso_symm iso_trans iso_sub
  grain_sub grain_iso grain_irred
  sub_union_left sub_union_right union_sub
  inter_sub_left inter_sub_right sub_inter
  sub_diff sub_union_diff sub_inter_union_diff
  diff_inter_empty diff_sub_left)

open GrainTheory.Relations (grainEq grainEq_of_iso grainEq_symm
  grainLe grainIncomp)

open GrainTheory.Foundations (IsGrainOf grain_idempotent)

/-! ## Helper lemmas for diff simplification -/

/-- When A ⊆_typ B, the difference A -_typ B is empty (a bottom element):
    it is a sub-type of any T.

    Proof: A \ B ⊆ A ⊆ B, so A \ B ⊆ (A \ B) ∩ B (by sub_inter),
    and (A \ B) ∩ B ⊆ T (by diff_inter_empty). -/
theorem diff_sub_of_sub (A B T : D) (h : sub A B) :
    sub (diff A B) T := by
  have h1 : sub (diff A B) B := sub_trans _ _ _ (sub_diff A B) h
  have h2 : sub (diff A B) (inter (diff A B) B) :=
    sub_inter _ _ _ (sub_refl (diff A B)) h1
  exact sub_trans _ _ _ h2 (diff_inter_empty A B T)

/-- When A ⊆_typ B, the union C ∪_typ (A -_typ B) ≅ C.

    Since A \ B is empty (diff_sub_of_sub), it is ⊆ C.
    Then union_sub gives C ∪ (A \ B) ⊆ C, and sub_union_left gives C ⊆ C ∪ (A \ B).
    Antisymmetry yields iso. -/
theorem union_diff_iso_of_sub (A B C : D) (h : sub A B) :
    iso (union C (diff A B)) C := by
  have h1 : sub (diff A B) C := diff_sub_of_sub A B C h
  have h2 : sub (union C (diff A B)) C := union_sub _ _ _ (sub_refl C) h1
  have h3 : sub C (union C (diff A B)) := sub_union_left C (diff A B)
  exact sub_antisymm _ _ h2 h3

/-- Diff is anti-monotone in the second argument (backward direction):
    sub (diff A B) (diff A (inter B C)).

    Removing more (B) gives a smaller result than removing less (B ∩ C).
    No extra hypotheses needed.

    Proof: Decompose A \ B via sub_inter_union_diff into the (B ∩ C)-part
    and its complement. The (B ∩ C)-part is empty (it intersects B,
    contradicting diff), so A \ B ⊆ A \ (B ∩ C). -/
private theorem diff_sub_diff_inter (A B C : D) :
    sub (diff A B) (diff A (inter B C)) := by
  -- Decompose: A\B ⊆ ((A\B) ∩ (B∩C)) ∪ ((A\B) \ (B∩C))
  have h_decomp : sub (diff A B) (union (inter (diff A B) (inter B C))
                                         (diff (diff A B) (inter B C))) :=
    sub_inter_union_diff (diff A B) (inter B C)
  -- Part 1: (A\B) ∩ (B∩C) is empty (⊆ any T)
  -- (A\B) ∩ (B∩C) ⊆ (B∩C) ⊆ B  and  (A\B) ∩ (B∩C) ⊆ (A\B)
  -- So (A\B) ∩ (B∩C) ⊆ (A\B) ∩ B ⊆ T
  have h_inter_bc_sub_b : sub (inter B C) B := inter_sub_left B C
  have h_part1_sub_b : sub (inter (diff A B) (inter B C)) B :=
    sub_trans _ _ _ (inter_sub_right (diff A B) (inter B C)) h_inter_bc_sub_b
  have h_part1_sub_dab : sub (inter (diff A B) (inter B C)) (diff A B) :=
    inter_sub_left (diff A B) (inter B C)
  have h_part1_in_dab_b : sub (inter (diff A B) (inter B C)) (inter (diff A B) B) :=
    sub_inter _ _ _ h_part1_sub_dab h_part1_sub_b
  have h_part1_empty : sub (inter (diff A B) (inter B C)) (diff A (inter B C)) :=
    sub_trans _ _ _ h_part1_in_dab_b (diff_inter_empty A B (diff A (inter B C)))
  -- Part 2: (A\B) \ (B∩C) ⊆ A \ (B∩C)
  -- From diff_sub_left: (A\B) ⊆ A → ((A\B) \ (B∩C)) ⊆ (A \ (B∩C))
  have h_part2 : sub (diff (diff A B) (inter B C)) (diff A (inter B C)) :=
    diff_sub_left (diff A B) A (inter B C) (sub_diff A B)
  -- Combine via union_sub
  have h_union : sub (union (inter (diff A B) (inter B C))
                            (diff (diff A B) (inter B C)))
                     (diff A (inter B C)) :=
    union_sub _ _ _ h_part1_empty h_part2
  exact sub_trans _ _ _ h_decomp h_union

/-- Diff is anti-monotone in the second argument (forward direction):
    sub A C → sub (diff A (inter B C)) (diff A B).

    When A ⊆ C, removing B ∩ C is the same as removing B:
    a field in A \ (B ∩ C) that is not in B is automatically not in B ∩ C.
    The converse holds because A ⊆ C: any field of A in B is in B ∩ C.

    Proof: Decompose A \ (B∩C) into B-part and non-B-part.
    The B-part is in B and in C (since A ⊆ C), hence in B ∩ C,
    contradicting that it's in A \ (B∩C). So it's empty. -/
private theorem diff_inter_sub_diff_of_sub (A B C : D) (h : sub A C) :
    sub (diff A (inter B C)) (diff A B) := by
  -- Decompose: A\(B∩C) ⊆ ((A\(B∩C)) ∩ B) ∪ ((A\(B∩C)) \ B)
  have h_decomp : sub (diff A (inter B C))
      (union (inter (diff A (inter B C)) B) (diff (diff A (inter B C)) B)) :=
    sub_inter_union_diff (diff A (inter B C)) B
  -- Part 1: (A\(B∩C)) ∩ B is empty (⊆ any T)
  -- (A\(B∩C)) ⊆ A ⊆ C, so (A\(B∩C)) ∩ B ⊆ C ∩ B = B ∩ C
  -- Also (A\(B∩C)) ∩ B ⊆ A\(B∩C)
  -- So (A\(B∩C)) ∩ B ⊆ (A\(B∩C)) ∩ (B∩C) ⊆ T (diff_inter_empty)
  have h_dab_sub_c : sub (diff A (inter B C)) C :=
    sub_trans _ _ _ (sub_diff A (inter B C)) h
  have h_p1_sub_b : sub (inter (diff A (inter B C)) B) B :=
    inter_sub_right (diff A (inter B C)) B
  have h_p1_sub_c : sub (inter (diff A (inter B C)) B) C :=
    sub_trans _ _ _ (inter_sub_left (diff A (inter B C)) B) h_dab_sub_c
  have h_p1_sub_bc : sub (inter (diff A (inter B C)) B) (inter B C) :=
    sub_inter _ _ _ h_p1_sub_b h_p1_sub_c
  have h_p1_sub_dab : sub (inter (diff A (inter B C)) B) (diff A (inter B C)) :=
    inter_sub_left (diff A (inter B C)) B
  have h_p1_in_dab_bc : sub (inter (diff A (inter B C)) B)
      (inter (diff A (inter B C)) (inter B C)) :=
    sub_inter _ _ _ h_p1_sub_dab h_p1_sub_bc
  have h_p1_empty : sub (inter (diff A (inter B C)) B) (diff A B) :=
    sub_trans _ _ _ h_p1_in_dab_bc (diff_inter_empty A (inter B C) (diff A B))
  -- Part 2: (A\(B∩C)) \ B ⊆ A \ B
  -- From diff_sub_left: (A\(B∩C)) ⊆ A → ((A\(B∩C)) \ B) ⊆ (A \ B)
  have h_p2 : sub (diff (diff A (inter B C)) B) (diff A B) :=
    diff_sub_left (diff A (inter B C)) A B (sub_diff A (inter B C))
  -- Combine
  have h_union : sub (union (inter (diff A (inter B C)) B)
      (diff (diff A (inter B C)) B)) (diff A B) :=
    union_sub _ _ _ h_p1_empty h_p2
  exact sub_trans _ _ _ h_decomp h_union

/-- When A ⊆_typ C, diff commutes with intersection on the second argument:
    (A -_typ (B ∩_typ C)) ≅ (A -_typ B).

    Set-theoretically: fields of A not in B ∩ C are exactly those not in B,
    because A ⊆ C makes the C-condition vacuous. -/
theorem diff_inter_iso_of_sub (A B C : D) (h : sub A C) :
    iso (diff A (inter B C)) (diff A B) :=
  sub_antisymm _ _
    (diff_inter_sub_diff_of_sub A B C h)
    (diff_sub_diff_inter A B C)

/-! ## Case 1: Equal Grains -/

/-- **PODS Prop 6.2, Case 1: Equal grains with G[R₁] ⊆_typ Jk.**

    When G[R₁] ≡_g G[R₂] and G[R₁] ⊆_typ Jk, the equi-join formula
    simplifies: G[R₂] ⊆ Jk (since G[R₂] ≅ G[R₁] ⊆ Jk), so
    G[R₂] -_typ Jk = ∅, and F₁ = G[R₁] ∪ ∅ ≅ G[R₁].

    Result: G[Res] ≡_g G[R₁], i.e., the result has the same grain as R₁. -/
theorem equijoin_equal_grains
    (R₁ R₂ Jk Res : D)
    (h_eq : grainEq R₁ R₂)
    (h_g1_jk : sub (grain R₁) Jk)
    (h_jk_r1 : sub Jk R₁) (h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : grainEq Res R₁ := by
  -- Step 1: G[R₂] ⊆ Jk (from G[R₁] ≡_g G[R₂] and G[R₁] ⊆ Jk)
  have h_g2_sub_g1 : sub (grain R₂) (grain R₁) :=
    iso_sub _ _ _ h_eq (sub_refl (grain R₂))
  have h_g2_jk : sub (grain R₂) Jk :=
    sub_trans _ _ _ h_g2_sub_g1 h_g1_jk
  -- Step 2: F₁ ≅ G[R₁] (since G[R₂] \ Jk is empty)
  have h_F1_iso : iso (union (grain R₁) (diff (grain R₂) Jk)) (grain R₁) :=
    union_diff_iso_of_sub (grain R₂) Jk (grain R₁) h_g2_jk
  -- Step 3: IsGrainOf F₁ Res (main theorem)
  have h_main : IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res :=
    equijoin_grain_identity R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup
  -- Step 4: G[R₁] ≅ Res (transitivity: G[R₁] ≅⁻¹ F₁ ≅ Res)
  have h_gR1_Res : iso (grain R₁) Res :=
    iso_trans _ _ _ (iso_symm _ _ h_F1_iso) h_main.1
  -- Step 5: grainEq Res R₁ = iso (grain Res) (grain R₁)
  -- From iso (grain R₁) Res, get grainEq (grain R₁) Res
  -- = iso (grain (grain R₁)) (grain Res)
  have h_gg_gres : iso (grain (grain R₁)) (grain Res) :=
    grainEq_of_iso h_gR1_Res
  -- By idempotency: grain (grain R₁) ≅ grain R₁
  have h_gR1_gRes : iso (grain R₁) (grain Res) :=
    iso_trans _ _ _ (iso_symm _ _ (grain_idempotent R₁)) h_gg_gres
  -- iso_symm gives grainEq Res R₁
  exact iso_symm _ _ h_gR1_gRes

/-! ## Case 2: Ordered Grains -/

/-- **PODS Prop 6.2, Case 2: Ordered grains (R₁ finer) with G[R₂] ⊆_typ Jk.**

    When R₁ ≤_g R₂ (G[R₂] ⊆ G[R₁], R₁ has finer grain) and G[R₂] ⊆_typ Jk,
    then G[R₂] -_typ Jk = ∅, so F₁ = G[R₁] ∪ ∅ ≅ G[R₁].

    Result: G[Res] ≡_g G[R₁] — the finer grain is preserved.
    This is the common 1-to-many join pattern (e.g., OrderDetail ⋈ Order). -/
theorem equijoin_ordered_grains
    (R₁ R₂ Jk Res : D)
    (_h_le : grainLe R₁ R₂)
    (h_g2_jk : sub (grain R₂) Jk)
    (h_jk_r1 : sub Jk R₁) (h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : grainEq Res R₁ := by
  -- Step 1: F₁ ≅ G[R₁] (since G[R₂] ⊆ Jk, diff is empty)
  have h_F1_iso : iso (union (grain R₁) (diff (grain R₂) Jk)) (grain R₁) :=
    union_diff_iso_of_sub (grain R₂) Jk (grain R₁) h_g2_jk
  -- Step 2: IsGrainOf F₁ Res (main theorem)
  have h_main : IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res :=
    equijoin_grain_identity R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup
  -- Step 3: G[R₁] ≅ Res
  have h_gR1_Res : iso (grain R₁) Res :=
    iso_trans _ _ _ (iso_symm _ _ h_F1_iso) h_main.1
  -- Step 4: grainEq Res R₁ = iso (grain Res) (grain R₁)
  have h_gg_gres : iso (grain (grain R₁)) (grain Res) :=
    grainEq_of_iso h_gR1_Res
  have h_gR1_gRes : iso (grain R₁) (grain Res) :=
    iso_trans _ _ _ (iso_symm _ _ (grain_idempotent R₁)) h_gg_gres
  exact iso_symm _ _ h_gR1_gRes

/-! ## Case 3: Incomparable Grains -/

/-- **PODS Prop 6.2, Case 3: Incomparable grains — both labelings are valid.**

    When G[R₁] #_g G[R₂], the formula G[Res] = G[R₁] ∪_typ (G[R₂] -_typ Jk)
    yields IsGrainOf for either labeling: both F₁ and F₂ satisfy the Grain
    Inference Theorem conditions (because `equijoin_grain_identity` requires
    no naming convention).

    This theorem shows both F₁ = G[R₁] ∪ (G[R₂] \ Jk) and
    F₂ = G[R₂] ∪ (G[R₁] \ Jk) are grains of Res. -/
theorem equijoin_incomparable_grains
    (R₁ R₂ Jk Res : D)
    (_h_incomp : grainIncomp R₁ R₂)
    (h_jk_r1 : sub Jk R₁) (h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res
    ∧ IsGrainOf (union (grain R₂) (diff (grain R₁) Jk)) Res := by
  constructor
  -- F₁ = G[R₁] ∪ (G[R₂] \ Jk) is a grain of Res
  · exact equijoin_grain_identity R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup
  -- F₂ = G[R₂] ∪ (G[R₁] \ Jk) is a grain of Res
  -- Swap R₁ and R₂: the result schema is symmetric via product commutativity
  · have h_comm : iso (prod (diff R₁ Jk) (diff R₂ Jk)) (prod (diff R₂ Jk) (diff R₁ Jk)) :=
      GrainStructure.prod_comm_iso (diff R₁ Jk) (diff R₂ Jk)
    have h_prod_comm : iso (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk)
                           (prod (prod (diff R₂ Jk) (diff R₁ Jk)) Jk) :=
      GrainStructure.prod_iso _ _ _ _ h_comm (iso_refl Jk)
    have h_res_sub' : sub Res (prod (prod (diff R₂ Jk) (diff R₁ Jk)) Jk) :=
      sub_trans _ _ _ h_res_sub (iso_sub _ _ _ (iso_symm _ _ h_prod_comm) (sub_refl _))
    have h_res_sup' : sub (prod (prod (diff R₂ Jk) (diff R₁ Jk)) Jk) Res :=
      sub_trans _ _ _ (iso_sub _ _ _ h_prod_comm (sub_refl _)) h_res_sup
    exact equijoin_grain_identity R₂ R₁ Jk Res h_jk_r2 h_jk_r1 h_res_sub' h_res_sup'

/-! ## Case 4: Natural Join -/

/-- **PODS Prop 6.2, Case 4: Natural join (Jk = R₁ ∩ R₂).**

    When the join key is the full intersection of the input schemas,
    the equi-join formula specializes to:

      G[Res] = G[R₁] ∪_typ (G[R₂] -_typ (R₁ ∩_typ R₂))

    The join key sub-hypotheses Jk ⊆ R₁ and Jk ⊆ R₂ are automatic from
    inter_sub_left and inter_sub_right. -/
theorem equijoin_natural_join
    (R₁ R₂ Res : D)
    (h_res_sub : sub Res
      (prod (prod (diff R₁ (inter R₁ R₂))
                  (diff R₂ (inter R₁ R₂)))
            (inter R₁ R₂)))
    (h_res_sup : sub
      (prod (prod (diff R₁ (inter R₁ R₂))
                  (diff R₂ (inter R₁ R₂)))
            (inter R₁ R₂))
      Res)
    : IsGrainOf
        (union (grain R₁) (diff (grain R₂) (inter R₁ R₂)))
        Res :=
  equijoin_grain_identity R₁ R₂ (inter R₁ R₂) Res
    (inter_sub_left R₁ R₂)
    (inter_sub_right R₁ R₂)
    h_res_sub h_res_sup

/-- **PODS simplification: G[R₂] -_typ (R₁ ∩ R₂) ≅ G[R₂] -_typ R₁.**

    In the natural join case, the diff in the formula simplifies:
    since G[R₂] ⊆_typ R₂ (grain_sub), removing fields in R₁ ∩ R₂
    is the same as removing fields in R₁ (the R₂-condition is vacuous).

    This gives the final form: G[Res] = G[R₁] ∪_typ (G[R₂] -_typ R₁). -/
theorem natural_join_diff_simplify (R₁ R₂ : D) :
    iso (diff (grain R₂) (inter R₁ R₂)) (diff (grain R₂) R₁) :=
  diff_inter_iso_of_sub (grain R₂) R₁ R₂ (grain_sub R₂)

/-- **PODS Prop 6.2, Case 4 (simplified form): Natural join.**

    G[Res] = G[R₁] ∪_typ (G[R₂] -_typ R₁)

    Captures all of G[R₁] plus grain fields of R₂ unique to R₂.
    This is the simplified form from the PODS paper, using the identity
    G[R₂] -_typ (R₁ ∩ R₂) ≅ G[R₂] -_typ R₁ (since G[R₂] ⊆ R₂). -/
theorem equijoin_natural_join_simplified
    (R₁ R₂ Res : D)
    (h_res_sub : sub Res
      (prod (prod (diff R₁ (inter R₁ R₂))
                  (diff R₂ (inter R₁ R₂)))
            (inter R₁ R₂)))
    (h_res_sup : sub
      (prod (prod (diff R₁ (inter R₁ R₂))
                  (diff R₂ (inter R₁ R₂)))
            (inter R₁ R₂))
      Res)
    : IsGrainOf
        (union (grain R₁) (diff (grain R₂) R₁))
        Res := by
  -- Get IsGrainOf with the unsimplified formula
  have h_main : IsGrainOf (union (grain R₁) (diff (grain R₂) (inter R₁ R₂))) Res :=
    equijoin_natural_join R₁ R₂ Res h_res_sub h_res_sup
  -- The simplified formula is iso to the unsimplified one
  have h_diff_iso : iso (diff (grain R₂) (inter R₁ R₂)) (diff (grain R₂) R₁) :=
    natural_join_diff_simplify R₁ R₂
  -- F_unsimplified ≅ F_simplified:
  -- union (G[R₁]) (G[R₂]\(R₁∩R₂)) ≅ union (G[R₁]) (G[R₂]\R₁)
  set F_u := union (grain R₁) (diff (grain R₂) (inter R₁ R₂))
  set F_s := union (grain R₁) (diff (grain R₂) R₁)
  -- Forward: F_u ⊆ F_s
  -- iso_sub (iso_symm h_diff_iso) (sub_refl _) gives
  --   sub (diff..inter) (diff..R₁)
  have h_diff_fwd : sub (diff (grain R₂) (inter R₁ R₂))
      (diff (grain R₂) R₁) :=
    iso_sub _ _ _ (iso_symm _ _ h_diff_iso)
      (sub_refl (diff (grain R₂) (inter R₁ R₂)))
  have h_fu_fs : sub F_u F_s := union_sub _ _ _
    (sub_union_left (grain R₁) (diff (grain R₂) R₁))
    (sub_trans _ _ _ h_diff_fwd
      (sub_union_right (grain R₁) (diff (grain R₂) R₁)))
  -- Backward: F_s ⊆ F_u
  -- iso_sub h_diff_iso (sub_refl _) gives
  --   sub (diff..R₁) (diff..inter)
  have h_diff_bwd : sub (diff (grain R₂) R₁)
      (diff (grain R₂) (inter R₁ R₂)) :=
    iso_sub _ _ _ h_diff_iso
      (sub_refl (diff (grain R₂) R₁))
  have h_fs_fu : sub F_s F_u := union_sub _ _ _
    (sub_union_left (grain R₁)
      (diff (grain R₂) (inter R₁ R₂)))
    (sub_trans _ _ _ h_diff_bwd
      (sub_union_right (grain R₁)
        (diff (grain R₂) (inter R₁ R₂))))
  have h_formula_iso : iso F_u F_s :=
    sub_antisymm _ _ h_fu_fs h_fs_fu
  -- Transfer IsGrainOf: F_u is a grain, F_u ≅ F_s, so F_s is a grain
  -- iso: F_s ≅ Res
  have h_iso : iso F_s Res :=
    iso_trans _ _ _ (iso_symm _ _ h_formula_iso) h_main.1
  -- irred: any S ⊆ F_s with S ≅ Res implies F_s ⊆ S
  have h_irred : ∀ S : D, sub S F_s → iso S Res → sub F_s S := by
    intro S h_s_sub h_s_iso
    -- S ⊆ F_s ⊆ F_u (via h_fs_fu)
    have h_s_fu : sub S F_u :=
      sub_trans _ _ _ h_s_sub h_fs_fu
    -- F_u ⊆ S (by h_main.2)
    have h_fu_s : sub F_u S := h_main.2 S h_s_fu h_s_iso
    -- F_s ⊆ F_u ⊆ S
    exact sub_trans _ _ _ h_fs_fu h_fu_s
  exact ⟨h_iso, h_irred⟩

end GrainTheory.Inference
