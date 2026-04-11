/-
  GrainTheory.Inference.EquiJoinBootstrap — Lemma B: candidate determines Res

  Proves that the candidate grain F₁ = G[R₁] ∪ (G[R₂] \ Jk) determines
  the join result Res. This is the bootstrapping argument: F₁ contains
  enough information to recover both input types, hence the result.

  This is Condition 2 (determination step) of the equi-join grain
  inference theorem's sufficient condition.

  The join result schema is characterized by mutual containment:
    sub Res P  and  sub P Res,  where P = (R₁ \ Jk) × (R₂ \ Jk) × Jk

  The final step uses `determines_prod` to combine determination of the
  three product components, then `determines_sub` to transfer since
  Res ⊆_typ P (from the first containment direction).

  Reference: PODS 2027 paper, §6, Equi-join grain inference proof;
  THEORY_GAP_CASE_B.md §6 (bootstrapping argument).
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

open EquiJoinStructure (determines grain_determines determines_mono
  determines_sub determines_iso_of_sub determines_union determines_prod
  determines_trans determines_self determines_of_sub)

/-- **Lemma B (Equi-Join Candidate Determines Res).** PODS §6, bootstrapping.

    The candidate grain F₁ = G[R₁] ∪_typ (G[R₂] \_typ Jk) determines
    the join result Res.

    **Hypotheses:**
    - `h_jk_r1`: Jk ⊆_typ R₁ (join key present in left input)
    - `h_res_sub`: Res ⊆_typ (R₁ \ Jk) × (R₂ \ Jk) × Jk

    **Bootstrapping chain:**
    1. G[R₁] ⊆ F₁, so F₁ → R₁            (grain\_determines + determines\_mono)
    2. Jk ⊆ R₁ and F₁ → R₁, so F₁ → Jk   (determines\_sub)
    3. G[R₂]\\Jk ⊆ F₁, so F₁ → G[R₂]\\Jk (determines\_of\_sub)
    4. F₁ → Jk ∪ (G[R₂]\\Jk)              (determines\_union)
    5. G[R₂] ⊆ Jk ∪ (G[R₂]\\Jk)           (sub\_union\_diff)
    6. F₁ → G[R₂]                          (determines\_sub from 4–5)
    7. G[R₂] → R₂, so F₁ → R₂            (determines\_trans)
    8. F₁ → R₁\\Jk, R₂\\Jk, Jk           (determines\_sub)
    9. F₁ → (R₁\\Jk) × (R₂\\Jk) × Jk    (determines\_prod, twice)
   10. Res ⊆ product, so F₁ → Res         (determines\_sub) -/
theorem equijoin_candidate_determines
    (R₁ R₂ Jk Res : D)
    (h_jk_r1 : sub Jk R₁) (_h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    : determines (union (grain R₁) (diff (grain R₂) Jk)) Res := by
  -- Abbreviate the candidate grain and the product
  set F₁ := union (grain R₁) (diff (grain R₂) Jk)
  set P := prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk
  -- ── Step 1: F₁ determines R₁ ──
  have h_gr1_sub_f : sub (grain R₁) F₁ :=
    sub_union_left (grain R₁) (diff (grain R₂) Jk)
  have h_gr1_det_r1 : determines (grain R₁) R₁ :=
    grain_determines R₁
  have h_f_det_r1 : determines F₁ R₁ :=
    determines_mono (grain R₁) F₁ R₁ h_gr1_det_r1 h_gr1_sub_f
  -- ── Step 2: F₁ determines Jk ──
  have h_f_det_jk : determines F₁ Jk :=
    determines_sub F₁ R₁ Jk h_f_det_r1 h_jk_r1
  -- ── Step 3: F₁ determines G[R₂] \ Jk ──
  have h_diff_sub_f : sub (diff (grain R₂) Jk) F₁ :=
    sub_union_right (grain R₁) (diff (grain R₂) Jk)
  have h_f_det_diff : determines F₁ (diff (grain R₂) Jk) :=
    determines_of_sub F₁ (diff (grain R₂) Jk) h_diff_sub_f
  -- ── Step 4: F₁ determines Jk ∪ (G[R₂] \ Jk) ──
  have h_f_det_jk_union_diff : determines F₁ (union Jk (diff (grain R₂) Jk)) :=
    determines_union F₁ Jk (diff (grain R₂) Jk) h_f_det_jk h_f_det_diff
  -- ── Step 5–6: F₁ determines G[R₂] ──
  have h_gr2_sub_union : sub (grain R₂) (union Jk (diff (grain R₂) Jk)) :=
    sub_union_diff (grain R₂) Jk
  have h_f_det_gr2 : determines F₁ (grain R₂) :=
    determines_sub F₁ (union Jk (diff (grain R₂) Jk)) (grain R₂)
      h_f_det_jk_union_diff h_gr2_sub_union
  -- ── Step 7: F₁ determines R₂ ──
  have h_gr2_det_r2 : determines (grain R₂) R₂ :=
    grain_determines R₂
  have h_f_det_r2 : determines F₁ R₂ :=
    determines_trans F₁ (grain R₂) R₂ h_f_det_gr2 h_gr2_det_r2
  -- ── Step 8: F₁ determines each product component ──
  have h_f_det_r1_priv : determines F₁ (diff R₁ Jk) :=
    determines_sub F₁ R₁ (diff R₁ Jk) h_f_det_r1 (sub_diff R₁ Jk)
  have h_f_det_r2_priv : determines F₁ (diff R₂ Jk) :=
    determines_sub F₁ R₂ (diff R₂ Jk) h_f_det_r2 (sub_diff R₂ Jk)
  -- ── Step 9: F₁ determines the product (R₁\Jk) × (R₂\Jk) × Jk ──
  have h_f_det_inner : determines F₁ (prod (diff R₁ Jk) (diff R₂ Jk)) :=
    determines_prod F₁ (diff R₁ Jk) (diff R₂ Jk) h_f_det_r1_priv h_f_det_r2_priv
  have h_f_det_prod : determines F₁ P :=
    determines_prod F₁ (prod (diff R₁ Jk) (diff R₂ Jk)) Jk h_f_det_inner h_f_det_jk
  -- ── Step 10: F₁ determines Res ──
  -- Res ⊆ P (h_res_sub), so determines_sub gives F₁ → Res
  exact determines_sub F₁ P Res h_f_det_prod h_res_sub

end GrainTheory.Inference
