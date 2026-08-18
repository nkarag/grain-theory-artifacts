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
  inter_sub_left inter_sub_right 
  sub_diff sub_union_diff sub_inter_union_diff
  diff_inter_empty 
  ssub ssub_refl ssub_trans ssub_antisymm ssub_sub
  ssub_union_left ssub_union_right union_ssub
  inter_ssub_left inter_ssub_right ssub_inter
  ssub_diff ssub_inter_union_diff diff_ssub_left)

open GrainTheory.Relations (grainEq grainEq_of_iso grainEq_symm
  grainLe grainIncomp)

open GrainTheory.Foundations (IsGrainOf grain_idempotent)

/-! ## Helper lemmas for diff simplification -/

/-- When `A ⊑ B`, the difference `A -_typ B` is empty (a bottom element):
    it is a structural subtype of any T.

    **Structural, not semantic.** The `⊆_typ` form is false: `B` can *determine*
    `A` without containing a single one of `A`'s columns, in which case
    `A -_typ B = A` is not empty. Refuted in `Model/AxiomCheck.lean`.

    Proof: `A \ B ⊑ A ⊑ B`, so `A \ B ⊑ (A \ B) ∩ B`, which is empty. -/
theorem diff_ssub_of_ssub (A B T : D) (h : ssub A B) :
    ssub (diff A B) T := by
  have h1 : ssub (diff A B) B := ssub_trans _ _ _ (ssub_diff A B) h
  have h2 : ssub (diff A B) (inter (diff A B) B) :=
    ssub_inter _ _ _ (ssub_refl (diff A B)) h1
  exact ssub_trans _ _ _ h2 (diff_inter_empty A B T)

/-- When A ⊆_typ B, the union C ∪_typ (A -_typ B) ≅ C.

    Since A \ B is empty (diff_sub_of_sub), it is ⊆ C.
    Then union_sub gives C ∪ (A \ B) ⊆ C, and sub_union_left gives C ⊆ C ∪ (A \ B).
    Antisymmetry yields iso. -/
theorem union_diff_iso_of_sub (A B C : D) (h : ssub A B) :
    iso (union C (diff A B)) C := by
  have h1 : sub (diff A B) C := ssub_sub _ _ (diff_ssub_of_ssub A B C h)
  have h2 : sub (union C (diff A B)) C := union_sub _ _ _ (sub_refl C) h1
  have h3 : sub C (union C (diff A B)) := sub_union_left C (diff A B)
  exact sub_antisymm _ _ h2 h3

/-! ### Anti-monotonicity of difference in its second argument

  These are field-set identities and hold **structurally**. Semantic versions
  were removed: `⊆_typ` means *determines*, and determination does not survive
  set difference — `diff_sub_left` is refuted in `Model/AxiomCheck.lean`.

  The structural versions are also what the natural-join simplification needs:
  transferring *grain-hood* requires `⊑`, since irreducibility does not survive
  a bare isomorphism. -/

/-- Structural form of `diff_sub_diff_inter`: `(A \ B) ⊑ (A \ (B ∩ C))`. -/
theorem diff_ssub_diff_inter (A B C : D) :
    ssub (diff A B) (diff A (inter B C)) := by
  have h_decomp : ssub (diff A B) (union (inter (diff A B) (inter B C))
                                          (diff (diff A B) (inter B C))) :=
    ssub_inter_union_diff (diff A B) (inter B C)
  have h_part1_sub_b : ssub (inter (diff A B) (inter B C)) B :=
    ssub_trans _ _ _ (inter_ssub_right (diff A B) (inter B C)) (inter_ssub_left B C)
  have h_part1_sub_dab : ssub (inter (diff A B) (inter B C)) (diff A B) :=
    inter_ssub_left (diff A B) (inter B C)
  have h_part1_in_dab_b : ssub (inter (diff A B) (inter B C)) (inter (diff A B) B) :=
    ssub_inter _ _ _ h_part1_sub_dab h_part1_sub_b
  have h_part1_empty : ssub (inter (diff A B) (inter B C)) (diff A (inter B C)) :=
    ssub_trans _ _ _ h_part1_in_dab_b (diff_inter_empty A B (diff A (inter B C)))
  have h_part2 : ssub (diff (diff A B) (inter B C)) (diff A (inter B C)) :=
    diff_ssub_left (diff A B) A (inter B C) (ssub_diff A B)
  exact ssub_trans _ _ _ h_decomp (union_ssub _ _ _ h_part1_empty h_part2)

/-- Structural form of `diff_inter_sub_diff_of_sub`:
    if `A ⊑ C` then `(A \ (B ∩ C)) ⊑ (A \ B)`.

    The hypothesis is now `A ⊑ C` rather than `A ⊆_typ C`. In the natural-join
    application `A = G[R₂]` and `C = R₂`, so this asks that R₂'s grain be
    **internal** — a real restriction the semantic version hid, since
    `G[R₂] ⊆_typ R₂` holds even for an external grain. -/
theorem diff_inter_ssub_diff_of_ssub (A B C : D) (h : ssub A C) :
    ssub (diff A (inter B C)) (diff A B) := by
  have h_decomp : ssub (diff A (inter B C))
      (union (inter (diff A (inter B C)) B) (diff (diff A (inter B C)) B)) :=
    ssub_inter_union_diff (diff A (inter B C)) B
  have h_dab_sub_c : ssub (diff A (inter B C)) C :=
    ssub_trans _ _ _ (ssub_diff A (inter B C)) h
  have h_p1_sub_b : ssub (inter (diff A (inter B C)) B) B :=
    inter_ssub_right (diff A (inter B C)) B
  have h_p1_sub_c : ssub (inter (diff A (inter B C)) B) C :=
    ssub_trans _ _ _ (inter_ssub_left (diff A (inter B C)) B) h_dab_sub_c
  have h_p1_sub_bc : ssub (inter (diff A (inter B C)) B) (inter B C) :=
    ssub_inter _ _ _ h_p1_sub_b h_p1_sub_c
  have h_p1_sub_dab : ssub (inter (diff A (inter B C)) B) (diff A (inter B C)) :=
    inter_ssub_left (diff A (inter B C)) B
  have h_p1_in_dab_bc : ssub (inter (diff A (inter B C)) B)
      (inter (diff A (inter B C)) (inter B C)) :=
    ssub_inter _ _ _ h_p1_sub_dab h_p1_sub_bc
  have h_p1_empty : ssub (inter (diff A (inter B C)) B) (diff A B) :=
    ssub_trans _ _ _ h_p1_in_dab_bc (diff_inter_empty A (inter B C) (diff A B))
  have h_p2 : ssub (diff (diff A (inter B C)) B) (diff A B) :=
    diff_ssub_left (diff A (inter B C)) A B (ssub_diff A (inter B C))
  exact ssub_trans _ _ _ h_decomp (union_ssub _ _ _ h_p1_empty h_p2)

/-- When `A ⊑ C`, difference commutes with intersection on the second argument:
    `(A -_typ (B ∩_typ C)) ≅ (A -_typ B)`.

    Field-set reading: the components of A outside `B ∩ C` are exactly those
    outside B, because `A ⊑ C` makes the C-condition vacuous. The hypothesis is
    structural — `A ⊆_typ C` is too weak, since a *declared* surjection carries
    no information about which components A has. -/
theorem diff_inter_iso_of_sub (A B C : D) (h : ssub A C) :
    iso (diff A (inter B C)) (diff A B) :=
  ssub_antisymm _ _
    (diff_inter_ssub_diff_of_ssub A B C h)
    (diff_ssub_diff_inter A B C)

/-! ## Case 1: Equal Grains -/

/-- **PODS Prop 6.2, Case 1: Equal grains with G[R₁] ⊆_typ Jk.**

    When G[R₁] ≡_g G[R₂] and G[R₁] ⊆_typ Jk, the equi-join formula
    simplifies: G[R₂] ⊆ Jk (since G[R₂] ≅ G[R₁] ⊆ Jk), so
    G[R₂] -_typ Jk = ∅, and F₁ = G[R₁] ∪ ∅ ≅ G[R₁].

    Result: G[Res] ≡_g G[R₁], i.e., the result has the same grain as R₁. -/
theorem equijoin_equal_grains
    (R₁ R₂ Jk Res : D)
    (h_eq : grainEq R₁ R₂)
    (_h_g1_jk : ssub (grain R₁) Jk) (h_g2_jk_struct : ssub (grain R₂) Jk)
    (h_jk_r1 : ssub Jk R₁) (h_jk_r2 : ssub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    (h_indep : InformationallyIndependent (grain R₁) (diff (grain R₂) Jk))
    (h_adm : AdmissibleLabeling R₁ R₂ Jk)
    : grainEq Res R₁ := by
  -- Step 1: G[R₂] ⊆ Jk (from G[R₁] ≡_g G[R₂] and G[R₁] ⊆ Jk)
  have h_g2_sub_g1 : sub (grain R₂) (grain R₁) :=
    iso_sub _ _ _ h_eq (sub_refl (grain R₂))
  -- Case 1 assumes the join key covers *both* grains structurally, exactly as
  -- arXiv Prop 7.3 case 1 states it (`G[R₁] ⊑ Jk` and `G[R₂] ⊑ Jk`). It cannot
  -- be derived from `h_eq` alone: grain equality is semantic, and a semantic
  -- containment does not yield the structural one the difference lemma needs.
  have h_g2_jk : ssub (grain R₂) Jk := h_g2_jk_struct
  -- Step 2: F₁ ≅ G[R₁] (since G[R₂] \ Jk is empty)
  have h_F1_iso : iso (union (grain R₁) (diff (grain R₂) Jk)) (grain R₁) :=
    union_diff_iso_of_sub (grain R₂) Jk (grain R₁) h_g2_jk
  -- Step 3: IsGrainOf F₁ Res (main theorem)
  have h_main : IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res :=
    equijoin_grain_identity R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup h_indep h_adm
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
    (h_g2_jk : ssub (grain R₂) Jk)
    (h_jk_r1 : ssub Jk R₁) (h_jk_r2 : ssub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    (h_indep : InformationallyIndependent (grain R₁) (diff (grain R₂) Jk))
    (h_adm : AdmissibleLabeling R₁ R₂ Jk)
    : grainEq Res R₁ := by
  -- Step 1: F₁ ≅ G[R₁] (since G[R₂] ⊆ Jk, diff is empty)
  have h_F1_iso : iso (union (grain R₁) (diff (grain R₂) Jk)) (grain R₁) :=
    union_diff_iso_of_sub (grain R₂) Jk (grain R₁) h_g2_jk
  -- Step 2: IsGrainOf F₁ Res (main theorem)
  have h_main : IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res :=
    equijoin_grain_identity R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup h_indep h_adm
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
    yields IsGrainOf for **either** labeling.

    This is the second bullet of arXiv Thm 7.2, and it is the one case where
    the labeling hypothesis is *derived* rather than assumed: when the two
    join-key grain portions are structurally incomparable, neither is a
    proper structural subtype of the other, so `AdmissibleLabeling` holds in
    both directions (`admissible_of_incomparable`). Both candidates are then
    grains of Res, and by Multiple Grains they are isomorphic.

    Incomparability is stated on the **Jk-portions** `G[Rᵢ] ∩ Jk`, which is
    what Thm 7.2 gates on; `grainIncomp R₁ R₂` alone (incomparability of the
    full grains) does not settle it. -/
theorem equijoin_incomparable_grains
    (R₁ R₂ Jk Res : D)
    (_h_incomp : grainIncomp R₁ R₂)
    (h_inc₁ : ¬ GrainStructure.ssub (inter (grain R₁) Jk) (inter (grain R₂) Jk))
    (h_inc₂ : ¬ GrainStructure.ssub (inter (grain R₂) Jk) (inter (grain R₁) Jk))
    (h_jk_r1 : ssub Jk R₁) (h_jk_r2 : ssub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    (h_indep₁₂ : InformationallyIndependent (grain R₁) (diff (grain R₂) Jk))
    (h_indep₂₁ : InformationallyIndependent (grain R₂) (diff (grain R₁) Jk))
    : IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res
    ∧ IsGrainOf (union (grain R₂) (diff (grain R₁) Jk)) Res := by
  obtain ⟨h_adm₁₂, h_adm₂₁⟩ := admissible_of_incomparable h_inc₁ h_inc₂
  constructor
  -- F₁ = G[R₁] ∪ (G[R₂] \ Jk) is a grain of Res
  · exact equijoin_grain_identity R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup
      h_indep₁₂ h_adm₁₂
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
      h_indep₂₁ h_adm₂₁

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
    (h_indep : InformationallyIndependent (grain R₁) (diff (grain R₂) (inter R₁ R₂)))
    (h_adm : AdmissibleLabeling R₁ R₂ (inter R₁ R₂))
    : IsGrainOf
        (union (grain R₁) (diff (grain R₂) (inter R₁ R₂)))
        Res :=
  equijoin_grain_identity R₁ R₂ (inter R₁ R₂) Res
    (inter_ssub_left R₁ R₂)
    (inter_ssub_right R₁ R₂)
    h_res_sub h_res_sup h_indep h_adm

/-- **PODS simplification: G[R₂] -_typ (R₁ ∩ R₂) ≅ G[R₂] -_typ R₁.**

    In the natural join case, the diff in the formula simplifies:
    since G[R₂] ⊆_typ R₂ (grain_sub), removing fields in R₁ ∩ R₂
    is the same as removing fields in R₁ (the R₂-condition is vacuous).

    This gives the final form: G[Res] = G[R₁] ∪_typ (G[R₂] -_typ R₁). -/
theorem natural_join_diff_simplify (R₁ R₂ : D) (h_int : ssub (grain R₂) R₂) :
    iso (diff (grain R₂) (inter R₁ R₂)) (diff (grain R₂) R₁) :=
  diff_inter_iso_of_sub (grain R₂) R₁ R₂ h_int

/-- **PODS Prop 6.2, Case 4 (simplified form): Natural join.**

    G[Res] = G[R₁] ∪_typ (G[R₂] -_typ R₁)

    Captures all of G[R₁] plus grain fields of R₂ unique to R₂, using the
    identity G[R₂] -_typ (R₁ ∩ R₂) = G[R₂] -_typ R₁.

    **`h_g2_internal` is a new hypothesis.** The identity needs R₂'s grain to
    sit *structurally* inside R₂ (an internal grain). The earlier version used
    `grain_sub : G[R₂] ⊆_typ R₂`, which is weaker — it also holds of an
    external grain such as `BalanceDate` for `Coll MonthlyBalance`, where
    `G[R₂]` shares no component with `R₂` and the difference simplification
    is not licensed. Mechanizing the notation split surfaced the gap. -/
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
    (h_indep : InformationallyIndependent (grain R₁) (diff (grain R₂) (inter R₁ R₂)))
    (h_adm : AdmissibleLabeling R₁ R₂ (inter R₁ R₂))
    (h_g2_internal : ssub (grain R₂) R₂)
    : IsGrainOf
        (union (grain R₁) (diff (grain R₂) R₁))
        Res := by
  -- Grain-hood with the unsimplified formula
  have h_main : IsGrainOf (union (grain R₁) (diff (grain R₂) (inter R₁ R₂))) Res :=
    equijoin_natural_join R₁ R₂ Res h_res_sub h_res_sup h_indep h_adm
  set F_u := union (grain R₁) (diff (grain R₂) (inter R₁ R₂))
  set F_s := union (grain R₁) (diff (grain R₂) R₁)
  -- The two formulas have the *same components*, not merely isomorphic
  -- carriers — which is what grain-hood transfer now requires.
  have h_diff_fwd : ssub (diff (grain R₂) (inter R₁ R₂)) (diff (grain R₂) R₁) :=
    diff_inter_ssub_diff_of_ssub (grain R₂) R₁ R₂ h_g2_internal
  have h_diff_bwd : ssub (diff (grain R₂) R₁) (diff (grain R₂) (inter R₁ R₂)) :=
    diff_ssub_diff_inter (grain R₂) R₁ R₂
  have h_fu_fs : ssub F_u F_s := union_ssub _ _ _
    (ssub_union_left (grain R₁) (diff (grain R₂) R₁))
    (ssub_trans _ _ _ h_diff_fwd (ssub_union_right (grain R₁) (diff (grain R₂) R₁)))
  have h_fs_fu : ssub F_s F_u := union_ssub _ _ _
    (ssub_union_left (grain R₁) (diff (grain R₂) (inter R₁ R₂)))
    (ssub_trans _ _ _ h_diff_bwd
      (ssub_union_right (grain R₁) (diff (grain R₂) (inter R₁ R₂))))
  exact h_main.of_ssub_antisymm h_fu_fs h_fs_fu

end GrainTheory.Inference
