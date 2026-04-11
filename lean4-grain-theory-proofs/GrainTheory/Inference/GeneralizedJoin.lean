/-
  GrainTheory.Inference.GeneralizedJoin — Generalized equi-join grain inference (LP-22)

  PODS 2027, §6, Theorem (Generalized Grain Inference for Equi-Joins):

    When join key types are isomorphic (Jk₁ ≅ Jk₂) rather than identical,
    the equi-join grain inference theorem generalizes:

      G[Res] = G[R₁] ∪_typ (G[R₂] -_typ Jk₂)

    with result schema Res ≅ (R₁ \ Jk₁) × (R₂ \ Jk₂) × Jk₁.

  The proof adapts the standard equi-join proof (LP-21) with:
  - Two distinct join keys: Jk₁ ⊆ R₁, Jk₂ ⊆ R₂, Jk₁ ≅ Jk₂
  - Additional hypothesis: determines Jk₁ Jk₂ (the join condition
    φ(Jk₁-values) = Jk₂-values bridges the two key spaces)
  - Condition (iii) reuses equijoin_candidate_idempotent R₁ R₂ Jk₂

  The capstone result is IsGrainOf (grain identity), which is strictly
  stronger than the paper's claim of ≡_g (grain equality).
-/

import GrainTheory.Inference.EquiJoinIdentity
import GrainTheory.Foundations.Idempotency
import GrainTheory.Foundations.GrainDef
import GrainTheory.Relations.GrainEquality
import GrainTheory.Relations.GrainInference

namespace GrainTheory.Inference

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub iso grain union inter diff prod
  sub_refl sub_trans sub_antisymm
  iso_refl iso_symm iso_trans iso_sub
  grain_sub grain_iso grain_irred
  sub_union_left sub_union_right union_sub
  inter_sub_left inter_sub_right sub_inter
  sub_diff sub_union_diff
  sub_prod_left sub_prod_right)

open EquiJoinStructure (determines grain_determines determines_mono
  determines_sub determines_iso_of_sub determines_union determines_prod
  determines_trans determines_self determines_of_sub)

open GrainTheory.Relations (grainEq grainLe grainEq_of_iso)

-- ════════════════════════════════════════════════════════════════
-- Lemma A (generalized): F₁ ⊆ Res
-- ════════════════════════════════════════════════════════════════

/-- Helper: G[R₂] \ Jk₂ ⊆ Res, derived from the generalized result schema.

    G[R₂] \ Jk₂ ⊆ G[R₂] ⊆ R₂, and G[R₂] \ Jk₂ ⊆ R₂ \ Jk₂ (by diff_sub_left).
    R₂ \ Jk₂ appears as a product component in Res. -/
private lemma gen_diff_sub_res (R₁ R₂ Jk₁ Jk₂ Res : D)
    (h_res_sup : sub (prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁) Res)
    : sub (diff (grain R₂) Jk₂) Res := by
  set P := prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁
  -- G[R₂] \ Jk₂ ⊆ R₂ \ Jk₂  (diff_sub_left from grain_sub)
  have h1 : sub (diff (grain R₂) Jk₂) (diff R₂ Jk₂) :=
    GrainStructure.diff_sub_left _ _ _ (grain_sub R₂)
  -- R₂ \ Jk₂ ⊆ (R₁ \ Jk₁) × (R₂ \ Jk₂)
  have h2 : sub (diff R₂ Jk₂) (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) :=
    sub_prod_right (diff R₁ Jk₁) (diff R₂ Jk₂)
  -- (R₁ \ Jk₁) × (R₂ \ Jk₂) ⊆ P
  have h3 : sub (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) P :=
    sub_prod_left (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁
  -- Chain: G[R₂] \ Jk₂ ⊆ R₂ \ Jk₂ ⊆ inner prod ⊆ P ⊆ Res
  exact sub_trans _ _ _ (sub_trans _ _ _ (sub_trans _ _ _ h1 h2) h3) h_res_sup

/-- Helper: G[R₁] ⊆ Res, derived from the generalized result schema.

    G[R₁] ⊆ R₁. R₁ decomposes as Jk₁ ∪ (R₁ \ Jk₁), and both
    components appear in the product Res. -/
private lemma gen_grain_r1_sub_res (R₁ R₂ Jk₁ Jk₂ Res : D)
    (h_jk1_r1 : sub Jk₁ R₁)
    (h_res_sup : sub (prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁) Res)
    : sub (grain R₁) Res := by
  set P := prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁
  -- R₁ \ Jk₁ ⊆ inner product ⊆ P
  have h1 : sub (diff R₁ Jk₁) P :=
    sub_trans _ _ _ (sub_prod_left (diff R₁ Jk₁) (diff R₂ Jk₂))
      (sub_prod_left (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁)
  -- Jk₁ ⊆ P
  have h2 : sub Jk₁ P :=
    sub_prod_right (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁
  -- R₁ ⊆ Jk₁ ∪ (R₁ \ Jk₁)
  have h3 : sub R₁ (union Jk₁ (diff R₁ Jk₁)) :=
    sub_union_diff R₁ Jk₁
  -- Jk₁ ∪ (R₁ \ Jk₁) ⊆ P
  have h4 : sub (union Jk₁ (diff R₁ Jk₁)) P :=
    union_sub Jk₁ (diff R₁ Jk₁) P h2 h1
  -- R₁ ⊆ Res
  have h5 : sub R₁ Res := sub_trans _ _ _ (sub_trans _ _ _ h3 h4) h_res_sup
  -- G[R₁] ⊆ R₁ ⊆ Res
  exact sub_trans _ _ _ (grain_sub R₁) h5

/-- **Lemma A (Generalized): F₁ ⊆ Res.**

    The candidate grain F₁ = G[R₁] ∪_typ (G[R₂] -_typ Jk₂) is a
    type-subset of the generalized join result Res.

    **Proof:**
    - G[R₁] ⊆ R₁ ⊆ Res  (grain_sub + R₁ embeds into product)
    - G[R₂] \ Jk₂ ⊆ R₂ \ Jk₂ ⊆ Res  (diff_sub_left + R₂\Jk₂ is in product)
    - union_sub combines both -/
theorem generalized_candidate_sub
    (R₁ R₂ Jk₁ Jk₂ Res : D)
    (h_jk1_r1 : sub Jk₁ R₁)
    (h_res_sup : sub (prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁) Res)
    : sub (union (grain R₁) (diff (grain R₂) Jk₂)) Res :=
  union_sub _ _ _
    (gen_grain_r1_sub_res R₁ R₂ Jk₁ Jk₂ Res h_jk1_r1 h_res_sup)
    (gen_diff_sub_res R₁ R₂ Jk₁ Jk₂ Res h_res_sup)

-- ════════════════════════════════════════════════════════════════
-- Lemma B (generalized): F₁ determines Res
-- ════════════════════════════════════════════════════════════════

/-- **Lemma B (Generalized): F₁ determines Res.** Bootstrapping with two keys.

    The candidate grain F₁ = G[R₁] ∪_typ (G[R₂] -_typ Jk₂) determines
    the generalized join result Res.

    **Additional hypothesis:** `determines Jk₁ Jk₂` — the join condition
    φ(Jk₁-values) = Jk₂-values establishes that knowing Jk₁-values
    uniquely determines Jk₂-values.

    **Bootstrapping chain:**
    1. G[R₁] ⊆ F₁, so F₁ → R₁             (grain_determines + determines_mono)
    2. Jk₁ ⊆ R₁ and F₁ → R₁, so F₁ → Jk₁  (determines_sub)
    3. G[R₂]\Jk₂ ⊆ F₁, so F₁ → G[R₂]\Jk₂  (determines_of_sub)
    4. F₁ → Jk₁ and Jk₁ → Jk₂, so F₁ → Jk₂ (determines_trans — NEW)
    5. F₁ → Jk₂ ∪ (G[R₂]\Jk₂)              (determines_union)
    6. G[R₂] ⊆ Jk₂ ∪ (G[R₂]\Jk₂)           (sub_union_diff)
    7. F₁ → G[R₂] → R₂                      (determines_sub + determines_trans)
    8. F₁ → R₁\Jk₁, R₂\Jk₂, Jk₁            (determines_sub)
    9. F₁ → (R₁\Jk₁) × (R₂\Jk₂) × Jk₁     (determines_prod, twice)
   10. Res ⊆ product, so F₁ → Res            (determines_sub) -/
theorem generalized_candidate_determines
    (R₁ R₂ Jk₁ Jk₂ Res : D)
    (h_jk1_r1 : sub Jk₁ R₁)
    (h_det_jk : determines Jk₁ Jk₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁))
    : determines (union (grain R₁) (diff (grain R₂) Jk₂)) Res := by
  -- Abbreviate
  set F₁ := union (grain R₁) (diff (grain R₂) Jk₂)
  set P := prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁
  -- ── Step 1: F₁ determines R₁ ──
  have h_gr1_sub_f : sub (grain R₁) F₁ :=
    sub_union_left (grain R₁) (diff (grain R₂) Jk₂)
  have h_f_det_r1 : determines F₁ R₁ :=
    determines_mono (grain R₁) F₁ R₁ (grain_determines R₁) h_gr1_sub_f
  -- ── Step 2: F₁ determines Jk₁ ──
  have h_f_det_jk1 : determines F₁ Jk₁ :=
    determines_sub F₁ R₁ Jk₁ h_f_det_r1 h_jk1_r1
  -- ── Step 3: F₁ determines G[R₂] \ Jk₂ ──
  have h_diff_sub_f : sub (diff (grain R₂) Jk₂) F₁ :=
    sub_union_right (grain R₁) (diff (grain R₂) Jk₂)
  have h_f_det_diff : determines F₁ (diff (grain R₂) Jk₂) :=
    determines_of_sub F₁ (diff (grain R₂) Jk₂) h_diff_sub_f
  -- ── Step 4: F₁ determines Jk₂ (via join condition bridge) ──
  have h_f_det_jk2 : determines F₁ Jk₂ :=
    determines_trans F₁ Jk₁ Jk₂ h_f_det_jk1 h_det_jk
  -- ── Step 5: F₁ determines Jk₂ ∪ (G[R₂] \ Jk₂) ──
  have h_f_det_jk2_union_diff : determines F₁ (union Jk₂ (diff (grain R₂) Jk₂)) :=
    determines_union F₁ Jk₂ (diff (grain R₂) Jk₂) h_f_det_jk2 h_f_det_diff
  -- ── Step 6–7: F₁ determines G[R₂], then R₂ ──
  have h_gr2_sub_union : sub (grain R₂) (union Jk₂ (diff (grain R₂) Jk₂)) :=
    sub_union_diff (grain R₂) Jk₂
  have h_f_det_gr2 : determines F₁ (grain R₂) :=
    determines_sub F₁ (union Jk₂ (diff (grain R₂) Jk₂)) (grain R₂)
      h_f_det_jk2_union_diff h_gr2_sub_union
  have h_f_det_r2 : determines F₁ R₂ :=
    determines_trans F₁ (grain R₂) R₂ h_f_det_gr2 (grain_determines R₂)
  -- ── Step 8: F₁ determines each product component ──
  have h_f_det_r1_priv : determines F₁ (diff R₁ Jk₁) :=
    determines_sub F₁ R₁ (diff R₁ Jk₁) h_f_det_r1 (sub_diff R₁ Jk₁)
  have h_f_det_r2_priv : determines F₁ (diff R₂ Jk₂) :=
    determines_sub F₁ R₂ (diff R₂ Jk₂) h_f_det_r2 (sub_diff R₂ Jk₂)
  -- ── Step 9: F₁ determines the product (R₁\Jk₁) × (R₂\Jk₂) × Jk₁ ──
  have h_f_det_inner : determines F₁ (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) :=
    determines_prod F₁ (diff R₁ Jk₁) (diff R₂ Jk₂) h_f_det_r1_priv h_f_det_r2_priv
  have h_f_det_prod : determines F₁ P :=
    determines_prod F₁ (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁ h_f_det_inner h_f_det_jk1
  -- ── Step 10: F₁ determines Res ──
  exact determines_sub F₁ P Res h_f_det_prod h_res_sub

-- ════════════════════════════════════════════════════════════════
-- Main theorems
-- ════════════════════════════════════════════════════════════════

/-- **Generalized Equi-Join Grain Inference (LP-22, PODS §6).**

    For a generalized equi-join of R₁ and R₂ with isomorphic join keys
    Jk₁ ≅ Jk₂ (Jk₁ ⊆ R₁, Jk₂ ⊆ R₂):

      G[R₁] ∪_typ (G[R₂] -_typ Jk₂)  ≡_g  G[Res]

    The candidate formula uses Jk₂ (R₂'s join key) for the difference,
    matching the paper's "operations understood up to the isomorphism."

    **Hypotheses:**
    - `h_jk_iso`: Jk₁ ≅ Jk₂  (join key types are isomorphic)
    - `h_det_jk`: Jk₁ → Jk₂  (join condition bridges key spaces)
    - `h_jk1_r1`, `h_jk2_r2`: join keys are sub-types of their relations
    - `h_res_sub`, `h_res_sup`: result schema mutual containment

    **Proof (5 steps, as in standard equi-join):**
    1. F₁ ⊆ Res                  (Lemma A — generalized_candidate_sub)
    2. F₁ determines Res          (Lemma B — generalized_candidate_determines)
    3. F₁ ≅ Res                   (determines_iso_of_sub from 1+2)
    4. G[F₁] ≅ G[Res]            (grainEq_of_iso)
    5. G[F₁] ≅ G[G[Res]]        (compose with grain_idempotent) -/
theorem generalized_equijoin_grain
    (R₁ R₂ Jk₁ Jk₂ Res : D)
    (_h_jk_iso : iso Jk₁ Jk₂)
    (h_det_jk : determines Jk₁ Jk₂)
    (h_jk1_r1 : sub Jk₁ R₁) (_h_jk2_r2 : sub Jk₂ R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁))
    (h_res_sup : sub (prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁) Res)
    : grainEq (union (grain R₁) (diff (grain R₂) Jk₂)) (grain Res) := by
  set F₁ := union (grain R₁) (diff (grain R₂) Jk₂)
  -- Step 1: F₁ ⊆ Res
  have h_sub : sub F₁ Res :=
    generalized_candidate_sub R₁ R₂ Jk₁ Jk₂ Res h_jk1_r1 h_res_sup
  -- Step 2: F₁ determines Res
  have h_det : determines F₁ Res :=
    generalized_candidate_determines R₁ R₂ Jk₁ Jk₂ Res h_jk1_r1 h_det_jk h_res_sub
  -- Step 3: F₁ ≅ Res
  have h_iso : iso F₁ Res :=
    determines_iso_of_sub F₁ Res h_det h_sub
  -- Step 4: G[F₁] ≅ G[Res]
  have h_grain_compat : iso (grain F₁) (grain Res) :=
    grainEq_of_iso h_iso
  -- Step 5: G[F₁] ≅ G[G[Res]] (compose with grain idempotency)
  exact iso_trans _ _ _ h_grain_compat
    (iso_symm _ _ (Foundations.grain_idempotent Res))

/-- **Generalized Equi-Join Grain Identity (LP-22, PODS §6 — via strengthened GIT).**

    $G[\text{Res}] = G[R_1] \cup_{typ} (G[R_2] -_{typ} J_{k2})$

    This is the capstone: `IsGrainOf F₁ Res` where
    $F_1 = G[R_1] \cup_{typ} (G[R_2] -_{typ} J_{k2})$.

    Strictly stronger than the paper's ≡_g claim. The proof verifies the
    three GIT conditions:
    (i)   F₁ ⊆ Res           — generalized_candidate_sub
    (ii)  F₁ ≤_g Res          — derived: F₁ ≅ Res → grainLe
    (iii) G[F₁] ≅ F₁          — equijoin_candidate_idempotent R₁ R₂ Jk₂
          (reused from standard equi-join — the idempotency proof depends
           only on grain_union, grain_idempotent, grain_diff_idempotent,
           which are independent of the specific join key) -/
theorem generalized_equijoin_grain_identity
    (R₁ R₂ Jk₁ Jk₂ Res : D)
    (_h_jk_iso : iso Jk₁ Jk₂)
    (h_det_jk : determines Jk₁ Jk₂)
    (h_jk1_r1 : sub Jk₁ R₁) (_h_jk2_r2 : sub Jk₂ R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁))
    (h_res_sup : sub (prod (prod (diff R₁ Jk₁) (diff R₂ Jk₂)) Jk₁) Res)
    : Foundations.IsGrainOf (union (grain R₁) (diff (grain R₂) Jk₂)) Res := by
  set F₁ := union (grain R₁) (diff (grain R₂) Jk₂)
  -- GIT condition (i): F₁ ⊆ Res
  have h_sub : sub F₁ Res :=
    generalized_candidate_sub R₁ R₂ Jk₁ Jk₂ Res h_jk1_r1 h_res_sup
  -- F₁ determines Res (Lemma B, generalized)
  have h_det : determines F₁ Res :=
    generalized_candidate_determines R₁ R₂ Jk₁ Jk₂ Res h_jk1_r1 h_det_jk h_res_sub
  -- F₁ ≅ Res
  have h_iso : iso F₁ Res :=
    determines_iso_of_sub F₁ Res h_det h_sub
  -- GIT condition (ii): grainLe F₁ Res (= sub (grain Res) (grain F₁))
  have h_grain_iso : iso (grain F₁) (grain Res) :=
    grainEq_of_iso h_iso
  have h_le : grainLe F₁ Res :=
    iso_sub _ _ _ h_grain_iso (sub_refl (grain Res))
  -- GIT condition (iii): G[F₁] ≅ F₁
  -- Reuse standard equi-join idempotency with Jk₂ as the difference key
  have h_idem : iso (grain F₁) F₁ :=
    equijoin_candidate_idempotent R₁ R₂ Jk₂
  -- Apply strengthened GIT → IsGrainOf F₁ Res
  exact Relations.grain_inference_isGrainOf h_sub h_le h_idem

/-- **Generalized equi-join specializes to standard equi-join.**

    When Jk₁ = Jk₂ = Jk (identical join keys), the generalized theorem
    recovers the standard equi-join result. This is a type-checking
    verification: instantiate Jk₁ = Jk₂ = Jk and the formula matches. -/
theorem generalized_specializes_to_standard
    (R₁ R₂ Jk Res : D)
    (h_jk_r1 : sub Jk R₁) (h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : Foundations.IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res :=
  generalized_equijoin_grain_identity R₁ R₂ Jk Jk Res
    (iso_refl Jk) (determines_self Jk) h_jk_r1 h_jk_r2 h_res_sub h_res_sup

end GrainTheory.Inference
