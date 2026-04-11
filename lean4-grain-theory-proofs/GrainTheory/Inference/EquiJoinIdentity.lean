/-
  GrainTheory.Inference.EquiJoinIdentity — Condition (iii) for equi-join grain identity

  PODS 2027, §6, Theorem (Equi-Join Grain Inference) — grain identity via GIT:

    For an equi-join of R₁ and R₂ on Jk:

      G[Res] = G[R₁] ∪_typ (G[R₂] -_typ Jk)

  This file proves GIT condition (iii): G[F₁] ≅ F₁, where
  F₁ = G[R₁] ∪_typ (G[R₂] \_{typ} Jk).

  **Proof:**
  1. grain_union: G[F₁] ≅ G[G[R₁]] ∪ G[G[R₂]\Jk]
  2. grain_idempotent: G[G[R₁]] ≅ G[R₁]
  3. grain_diff_idempotent: G[G[R₂]\Jk] ≅ G[R₂]\Jk
     (since G[R₂] is a grain fixpoint by idempotency)
  4. Lift component isos to union: G[F₁] ≅ G[R₁] ∪ (G[R₂]\Jk) = F₁

  Combined with conditions (i) and (ii) (Lemmas A and B), the
  strengthened GIT (grain_inference_isGrainOf) gives IsGrainOf F₁ Res.

  Reference: PODS 2027, §6 + Appendix proof (Condition iii paragraph).
-/

import GrainTheory.Inference.EquiJoinAxioms
import GrainTheory.Foundations.Idempotency

namespace GrainTheory.Inference

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub iso grain union inter diff prod
  sub_refl sub_trans sub_antisymm
  iso_refl iso_symm iso_trans iso_sub
  grain_sub grain_iso grain_union
  grain_diff_idempotent
  sub_union_left sub_union_right union_sub)

/-- Lift component isomorphisms to union:
    if A ≅ A' and B ≅ B', then A ∪ B ≅ A' ∪ B'.
    Derived from sub in both directions + antisymmetry. -/
private theorem union_iso (A A' B B' : D) (hA : iso A A') (hB : iso B B') :
    iso (union A B) (union A' B') := by
  have h_fwd : sub (union A B) (union A' B') := by
    apply union_sub
    · exact sub_trans _ _ _
        (iso_sub _ _ _ (iso_symm _ _ hA) (sub_refl A))
        (sub_union_left A' B')
    · exact sub_trans _ _ _
        (iso_sub _ _ _ (iso_symm _ _ hB) (sub_refl B))
        (sub_union_right A' B')
  have h_bwd : sub (union A' B') (union A B) := by
    apply union_sub
    · exact sub_trans _ _ _
        (iso_sub _ _ _ hA (sub_refl A'))
        (sub_union_left A B)
    · exact sub_trans _ _ _
        (iso_sub _ _ _ hB (sub_refl B'))
        (sub_union_right A B)
  exact sub_antisymm _ _ h_fwd h_bwd

/-- **GIT Condition (iii): G[F₁] ≅ F₁.**

    The candidate grain F₁ = G[R₁] ∪ (G[R₂] \ Jk) is a grain fixpoint:
    its grain is isomorphic to itself.

    Proof:
    - grain_union: G[A ∪ B] ≅ G[A] ∪ G[B]
    - grain_idempotent: G[G[R₁]] ≅ G[R₁]
    - grain_diff_idempotent: G[G[R₂] \ Jk] ≅ G[R₂] \ Jk
      (G[R₂] is a fixpoint by idempotency)
    - union_iso lifts both to: G[F₁] ≅ F₁ -/
theorem equijoin_candidate_idempotent (R₁ R₂ Jk : D) :
    iso (grain (union (grain R₁) (diff (grain R₂) Jk)))
        (union (grain R₁) (diff (grain R₂) Jk)) := by
  set A := grain R₁
  set B := diff (grain R₂) Jk
  -- Step 1: G[A ∪ B] ≅ G[A] ∪ G[B]  (grain distributes over union)
  have h_dist : iso (grain (union A B)) (union (grain A) (grain B)) :=
    grain_union A B
  -- Step 2: G[A] = G[G[R₁]] ≅ G[R₁] = A  (idempotency)
  have h_idem_A : iso (grain A) A :=
    Foundations.grain_idempotent R₁
  -- Step 3: G[B] = G[G[R₂] \ Jk] ≅ G[R₂] \ Jk = B  (grain_diff_idempotent)
  --   G[R₂] is a fixpoint: G[G[R₂]] ≅ G[R₂]
  have h_fixpoint : iso (grain (grain R₂)) (grain R₂) :=
    Foundations.grain_idempotent R₂
  have h_idem_B : iso (grain B) B :=
    grain_diff_idempotent (grain R₂) Jk h_fixpoint
  -- Step 4: G[A] ∪ G[B] ≅ A ∪ B  (lift component isos)
  have h_union : iso (union (grain A) (grain B)) (union A B) :=
    union_iso (grain A) A (grain B) B h_idem_A h_idem_B
  -- Compose: G[A ∪ B] ≅ G[A] ∪ G[B] ≅ A ∪ B
  exact iso_trans _ _ _ h_dist h_union

end GrainTheory.Inference
