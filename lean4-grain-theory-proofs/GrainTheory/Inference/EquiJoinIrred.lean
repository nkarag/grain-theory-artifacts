/-
  GrainTheory.Inference.EquiJoinIrred — Lemma C + D: naming convention and grain containment

  Two results that complement the main equi-join grain inference theorem:

  (C) equijoin_convention_sub:  With the naming convention G₁^{Jk} ⊆_typ G₂^{Jk},
      the "forward" candidate F₁ = G[R₁] ∪ (G[R₂] \ Jk) is a sub-type of the
      "reverse" candidate F₂ = G[R₂] ∪ (G[R₁] \ Jk).  This captures the naming
      convention's role: it selects the smaller (more minimal) candidate.

  (D) equijoin_grain_contains:  The grain of Res is contained in F₁.
      Every superkey of Res contains the grain, and F₁ is a superkey (Lemmas A+B).
      Combined with grainEq: G[Res] ⊆ F₁ ⊆ Res, with F₁ ≡_g G[Res].

  These results address THEORY_GAP_CASE_B_v2.md Gap 2 (formula asymmetry):
  without the naming convention, both F₁ and F₂ are grain-equivalent to Res,
  but only the convention-compliant direction is guaranteed minimal.

  Reference: PODS 2027 paper, §6; THEORY_GAP_CASE_B_v2.md §§4–6.
-/

import GrainTheory.Inference.EquiJoinSub
import GrainTheory.Inference.EquiJoinBootstrap

namespace GrainTheory.Inference

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub iso grain union inter diff prod
  sub_trans
  sub_union_left sub_union_right union_sub
  inter_sub_left
  sub_diff sub_inter_union_diff)

open EquiJoinStructure (determines determines_grain_sub)

/-- **Lemma C (Naming Convention Sub).** PODS §6, Gap 2 resolution.

    With the naming convention $G_1^{J_k} \subseteq_{typ} G_2^{J_k}$, the "forward"
    candidate $F_1 = G[R_1] \cup_{typ} (G[R_2] \setminus J_k)$ is a sub-type of
    the "reverse" candidate $F_2 = G[R_2] \cup_{typ} (G[R_1] \setminus J_k)$:

        sub F₁ F₂

    **Why the naming convention is needed.** Without it ($G_1^{J_k} \supsetneq G_2^{J_k}$),
    $F_1$ may contain redundant fields: fields $f \in G_1^{J_k} \setminus G_2^{J_k}$
    are recoverable via reverse bootstrapping ($G[R_2]$ complete → $R_2$ determined
    → $J_k$ known → $f$ recovered). The naming convention prevents this by ensuring
    $G_1^{J_k} \subseteq G_2^{J_k}$, so no such redundant fields exist.

    **Proof:** Decompose $G[R_1]$ into its $J_k$-part and non-$J_k$-part.  The $J_k$-part
    routes through the naming convention ($G_1^{J_k} \subseteq G_2^{J_k} \subseteq G[R_2]
    \subseteq F_2$).  The non-$J_k$-part is directly in $F_2$.  The other component
    $G[R_2] \setminus J_k$ routes through $G[R_2] \subseteq F_2$.

    See THEORY_GAP_CASE_B_v2.md §4 (formula asymmetry) and §6 (irreducibility). -/
theorem equijoin_convention_sub
    (R₁ R₂ Jk : D)
    (h_convention : sub (inter (grain R₁) Jk) (inter (grain R₂) Jk))
    : sub (union (grain R₁) (diff (grain R₂) Jk))
          (union (grain R₂) (diff (grain R₁) Jk)) := by
  set F₂ := union (grain R₂) (diff (grain R₁) Jk)
  -- By union_sub, suffices: G[R₁] ⊆ F₂ and G[R₂]\Jk ⊆ F₂
  apply union_sub
  · -- Goal: sub (grain R₁) F₂
    -- Step 1: Decompose G[R₁] into Jk-part and non-Jk-part
    have h_decomp : sub (grain R₁) (union (inter (grain R₁) Jk) (diff (grain R₁) Jk)) :=
      sub_inter_union_diff (grain R₁) Jk
    -- Step 2: Jk-part routes through naming convention
    --   G₁^Jk ⊆ G₂^Jk ⊆ G[R₂] ⊆ F₂
    have h_jk : sub (inter (grain R₁) Jk) F₂ :=
      sub_trans _ _ _
        (sub_trans _ _ _ h_convention (inter_sub_left (grain R₂) Jk))
        (sub_union_left (grain R₂) (diff (grain R₁) Jk))
    -- Step 3: Non-Jk-part is directly a component of F₂
    have h_rest : sub (diff (grain R₁) Jk) F₂ :=
      sub_union_right (grain R₂) (diff (grain R₁) Jk)
    -- Step 4: Combine via decomposition
    exact sub_trans _ _ _ h_decomp (union_sub _ _ _ h_jk h_rest)
  · -- Goal: sub (diff (grain R₂) Jk) F₂
    -- G[R₂]\Jk ⊆ G[R₂] ⊆ F₂
    exact sub_trans _ _ _
      (sub_diff (grain R₂) Jk)
      (sub_union_left (grain R₂) (diff (grain R₁) Jk))

/-- **Lemma D (Grain Containment).** The grain of Res is contained in F₁.

    sub (grain Res) F₁

    F₁ is a superkey of Res: it determines Res (Lemma B) and is a sub-type
    of Res (Lemma A). By the `determines_grain_sub` axiom, every superkey
    contains the grain. Therefore G[Res] ⊆ F₁.

    Combined with the main theorem's grainEq result:

        G[Res] ⊆ F₁ ⊆ Res    and    F₁ ≡_g G[Res]

    i.e., F₁ sits between the grain and the full result, carrying exactly
    the same information as both. -/
theorem equijoin_grain_contains
    (R₁ R₂ Jk Res : D)
    (h_jk_r1 : sub Jk R₁) (h_jk_r2 : sub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    : sub (grain Res) (union (grain R₁) (diff (grain R₂) Jk)) := by
  set F₁ := union (grain R₁) (diff (grain R₂) Jk)
  -- F₁ ⊆ Res (Lemma A)
  have h_sub : sub F₁ Res :=
    equijoin_candidate_sub R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sup
  -- F₁ → Res (Lemma B)
  have h_det : determines F₁ Res :=
    equijoin_candidate_determines R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub
  -- Superkeys contain the grain: G[Res] ⊆ F₁
  exact determines_grain_sub F₁ Res h_det h_sub

end GrainTheory.Inference
