/-
  GrainTheory.Inference.EquiJoin — Main equi-join grain inference theorem (LP-21)

  PODS 2027, §6, Theorem 6.1:

    For any equi-join of R₁ and R₂ on Jk, with join result schema
      Res ↔ (R₁ \ Jk) × (R₂ \ Jk) × Jk    (mutual containment)

      G[Res] = G[R₁] ∪_typ (G[R₂] -_typ Jk)

  The capstone theorem (equijoin_grain_identity) establishes grain identity
  via the strengthened Grain Inference Theorem (grain_inference_isGrainOf):

    IsGrainOf F₁ Res  where  F₁ = G[R₁] ∪_typ (G[R₂] -_typ Jk)

  Proof structure:
  1. GIT condition (i): F₁ ⊆ Res  (Lemma A, EquiJoinSub.lean)
  2. GIT condition (ii): F₁ ≤_g Res  (derived from Lemmas A+B → F₁ ≅ Res)
  3. GIT condition (iii): G[F₁] ≅ F₁  (EquiJoinIdentity.lean)
  4. grain_inference_isGrainOf → IsGrainOf F₁ Res

  Additional results:
  - equijoin_grain: F₁ ≡_g G[Res]  (grain equivalence, weaker corollary)
  - equijoin_grain_contains: G[Res] ⊆ F₁  (grain containment)
  - equijoin_convention_sub: F₁ ⊆ F₂  (naming convention minimality)
-/

import GrainTheory.Inference.EquiJoinSub
import GrainTheory.Inference.EquiJoinBootstrap
import GrainTheory.Inference.EquiJoinIrred
import GrainTheory.Inference.EquiJoinIdentity
import GrainTheory.Foundations.Idempotency
import GrainTheory.Foundations.GrainDef
import GrainTheory.Relations.GrainEquality
import GrainTheory.Relations.GrainInference

namespace GrainTheory.Inference

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub iso grain union inter diff prod
  sub_refl iso_trans iso_symm iso_sub grain_iso)

open EquiJoinStructure (determines determines_iso_of_sub)

open GrainTheory.Relations (grainEq grainLe grainEq_of_iso)

/-- **Equi-Join Grain Inference Theorem (LP-21, PODS Thm 6.1 corrected).**

    For an equi-join of R₁ and R₂ on join key Jk:

      G[Res] ≡_g G[R₁] ∪_typ (G[R₂] -_typ Jk)

    where the naming convention ensures G₁^{Jk} ⊆_typ G₂^{Jk}
    (i.e., R₁ is the side with the smaller Jk-portion of the grain).

    **Hypotheses:**
    - `h_convention`: G[R₁] ∩ Jk ⊆_typ G[R₂] ∩ Jk  (naming convention)
    - `h_jk_r1`, `h_jk_r2`: Jk ⊆_typ R₁, Jk ⊆_typ R₂
    - `h_res_sub`: Res ⊆_typ (R₁ \ Jk) × (R₂ \ Jk) × Jk
    - `h_res_sup`: (R₁ \ Jk) × (R₂ \ Jk) × Jk ⊆_typ Res

    **Proof (iso_sub–free, 5 steps):**
    1. F₁ ⊆ Res                  (Lemma A — sub_trans through product)
    2. F₁ determines Res          (Lemma B — bootstrapping chain)
    3. F₁ ≅ Res                   (determines_iso_of_sub from 1+2)
    4. G[F₁] ≅ G[Res]            (PODS Thm 4.2: grainEq_of_iso)
    5. G[F₁] ≅ G[G[Res]]        (compose with PODS Thm 3.7: grain_idempotent)
    This is grainEq F₁ (grain Res) by definition. -/
theorem equijoin_grain
    (R₁ R₂ Jk Res : D)
    (_h_convention : sub (inter (grain R₁) Jk) (inter (grain R₂) Jk))
    (h_jk_r1 : sub Jk R₁) (h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : grainEq (union (grain R₁) (diff (grain R₂) Jk)) (grain Res) := by
  set F₁ := union (grain R₁) (diff (grain R₂) Jk)
  -- Step 1: F₁ ⊆ Res (Lemma A)
  have h_sub : sub F₁ Res :=
    equijoin_candidate_sub R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sup
  -- Step 2: F₁ determines Res (Lemma B)
  have h_det : determines F₁ Res :=
    equijoin_candidate_determines R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub
  -- Step 3: F₁ ≅ Res (determines + sub → iso)
  have h_iso : iso F₁ Res :=
    determines_iso_of_sub F₁ Res h_det h_sub
  -- Step 4: G[F₁] ≅ G[Res] (PODS Theorem 4.2: grainEq_of_iso)
  have h_grain_compat : iso (grain F₁) (grain Res) :=
    grainEq_of_iso h_iso
  -- Step 5: G[F₁] ≅ G[G[Res]] (compose with grain idempotency, PODS Thm 3.7)
  exact iso_trans _ _ _ h_grain_compat
    (iso_symm _ _ (Foundations.grain_idempotent Res))

/-- **Complete Equi-Join Grain Inference Theorem (LP-21, PODS Thm 6.1).**

    The full theorem establishes three properties of the candidate grain
    $F_1 = G[R_1] \cup_{typ} (G[R_2] -_{typ} J_k)$:

    1. **Grain equivalence:** $F_1 \equiv_g G[\text{Res}]$
       ($F_1$ has the same grain as $\text{Res}$)

    2. **Grain containment:** $G[\text{Res}] \subseteq_{typ} F_1$
       (the actual grain sits inside $F_1$ — every superkey contains the grain)

    3. **Convention minimality:** $F_1 \subseteq_{typ} F_2$ where
       $F_2 = G[R_2] \cup_{typ} (G[R_1] -_{typ} J_k)$
       (the naming convention selects the smaller candidate)

    Together: $G[\text{Res}] \subseteq F_1 \subseteq F_2$, with $F_1 \equiv_g G[\text{Res}]$.

    The naming convention `h_convention` ($G_1^{J_k} \subseteq_{typ} G_2^{J_k}$) is
    used in conjunct 3.  Without it, the formula may produce a non-minimal
    candidate (see THEORY_GAP_CASE_B_v2.md §4, Example 3).

    **Proof sketch:**
    - Conjunct 1: Lemma A + B → F₁ ≅ Res → PODS Thm 4.2 → grain idempotency
    - Conjunct 2: Lemma A + B → F₁ is a superkey → determines_grain_sub
    - Conjunct 3: Decompose G[R₁] into Jk/non-Jk parts; convention routes Jk-part -/
theorem equijoin_grain_complete
    (R₁ R₂ Jk Res : D)
    (h_convention : sub (inter (grain R₁) Jk) (inter (grain R₂) Jk))
    (h_jk_r1 : sub Jk R₁) (h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : grainEq (union (grain R₁) (diff (grain R₂) Jk)) (grain Res)
    ∧ sub (grain Res) (union (grain R₁) (diff (grain R₂) Jk))
    ∧ sub (union (grain R₁) (diff (grain R₂) Jk))
          (union (grain R₂) (diff (grain R₁) Jk)) :=
  ⟨equijoin_grain R₁ R₂ Jk Res h_convention h_jk_r1 h_jk_r2 h_res_sub h_res_sup,
   equijoin_grain_contains R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup,
   equijoin_convention_sub R₁ R₂ Jk h_convention⟩

/-- **Equi-Join Grain Identity (PODS §6, Theorem 6.1 — via strengthened GIT).**

    $G[\text{Res}] = G[R_1] \cup_{typ} (G[R_2] -_{typ} J_k)$

    This is the capstone theorem: `IsGrainOf F₁ Res` where
    $F_1 = G[R_1] \cup_{typ} (G[R_2] -_{typ} J_k)$.

    **Proof via Grain Inference Theorem (grain_inference_isGrainOf):**
    Verify the three GIT conditions for G = F₁ and R = Res:
    (i)   F₁ ⊆ Res           — Lemma A (equijoin_candidate_sub)
    (ii)  F₁ ≤_g Res          — derived: Lemmas A+B → F₁ ≅ Res → grainLe
    (iii) G[F₁] ≅ F₁          — equijoin_candidate_idempotent

    **No naming convention or disjointness hypothesis needed.** -/
theorem equijoin_grain_identity
    (R₁ R₂ Jk Res : D)
    (h_jk_r1 : sub Jk R₁) (h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : Foundations.IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res := by
  set F₁ := union (grain R₁) (diff (grain R₂) Jk)
  -- GIT condition (i): F₁ ⊆ Res (Lemma A)
  have h_sub : sub F₁ Res :=
    equijoin_candidate_sub R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sup
  -- F₁ determines Res (Lemma B)
  have h_det : determines F₁ Res :=
    equijoin_candidate_determines R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub
  -- F₁ ≅ Res (determines + sub → iso)
  have h_iso : iso F₁ Res :=
    determines_iso_of_sub F₁ Res h_det h_sub
  -- GIT condition (ii): grainLe F₁ Res (= sub (grain Res) (grain F₁))
  have h_grain_iso : iso (grain F₁) (grain Res) :=
    grainEq_of_iso h_iso
  have h_le : grainLe F₁ Res :=
    iso_sub _ _ _ h_grain_iso (sub_refl (grain Res))
  -- GIT condition (iii): G[F₁] ≅ F₁
  have h_idem : iso (grain F₁) F₁ :=
    equijoin_candidate_idempotent R₁ R₂ Jk
  -- Apply strengthened GIT → IsGrainOf F₁ Res
  exact Relations.grain_inference_isGrainOf h_sub h_le h_idem

end GrainTheory.Inference
