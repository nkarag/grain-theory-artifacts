/-
  GrainTheory.Inference.EquiJoinIdentity — Condition (iii) for equi-join grain identity

  arXiv extended version, §7, Theorem 7.2 (Grain of an Equi-Join):

    For an equi-join of R₁ and R₂ on Jk:

      G[Res] = G[R₁] ∪_typ (G[R₂] -_typ Jk)

  This file:
  1. Defines `InformationallyIndependent` (arXiv Def 6.2 / Remark on
     Informational Independence): the equi-join candidate's components carry
     no cross-dependency, so none is recoverable from the others — which is
     exactly structural irreducibility of their union.

  2. Proves GIT condition (iii): under the admissible labeling, the candidate
     F₁ = G[R₁] ∪ (G[R₂] \ Jk) is irreducible.

  **What changed with the structural repair.**

  The previous version stated condition (iii) as the *isomorphism*
  `G[F₁] ≅ F₁` and discharged it unconditionally, from grain distribution
  over union plus two idempotency facts. That was sound only because
  irreducibility was then read semantically — and, as reviewer R2 observed,
  that reading is vacuous: `G[F₁] ≅ F₁` holds for *every* F₁, since the grain
  is always isomorphic to its type. The condition had no content, which is
  why no labeling hypothesis appeared to be needed.

  Under the structural reading the condition has real content, and the
  labeling hypothesis returns — matching the paper's Theorem 7.2, which
  gates on comparing the two inputs' join-key grain portions. The reverse
  labeling, when strictly larger on the Jk side, carries a redundant Jk-field
  and is genuinely reducible.

  Reference: arXiv extended version, §7 Thm 7.2; Appendix Remark
  (Informational Independence).
-/

import GrainTheory.Inference.EquiJoinAxioms
import GrainTheory.Foundations.Idempotency
import GrainTheory.Relations.GrainInference

namespace GrainTheory.Inference

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub ssub iso grain union inter diff prod
  sub_refl sub_trans sub_antisymm ssub_refl ssub_trans ssub_antisymm ssub_sub
  iso_refl iso_symm iso_trans iso_sub
  grain_sub grain_iso grain_union
  sub_union_left sub_union_right union_sub)

/-- The **admissible labeling** condition of arXiv Theorem 7.2.

    Writing `Gᵢ^Jk = G[Rᵢ] ∩ Jk`, the labeling `(1,2)` is admissible when
    `¬ (G₂^Jk ⊏ G₁^Jk)` — the appendix's reducibility criterion, negated. Two cases satisfy
    it — the canonical labeling `G₁^Jk ⊑ G₂^Jk`, and the incomparable case —
    and these are exactly the two cases Theorem 7.2 admits.

    Failing it means the candidate carries a Jk-field the join recovers from
    the opposite input, so the candidate is reducible and is not the grain. -/
def AdmissibleLabeling (R₁ R₂ Jk : D) : Prop :=
  ¬ Foundations.properSsub (inter (grain R₂) Jk) (inter (grain R₁) Jk)

/-- The canonical labeling `G₁^Jk ⊑ G₂^Jk` is admissible. -/
theorem admissible_of_canonical {R₁ R₂ Jk : D}
    (h : ssub (inter (grain R₁) Jk) (inter (grain R₂) Jk)) :
    AdmissibleLabeling R₁ R₂ Jk :=
  fun hc => hc.2 h

/-- Incomparable join-key grain portions are admissible **in both
    labelings** — the second bullet of arXiv Theorem 7.2. -/
theorem admissible_of_incomparable {R₁ R₂ Jk : D}
    (h₁ : ¬ ssub (inter (grain R₁) Jk) (inter (grain R₂) Jk))
    (h₂ : ¬ ssub (inter (grain R₂) Jk) (inter (grain R₁) Jk)) :
    AdmissibleLabeling R₁ R₂ Jk ∧ AdmissibleLabeling R₂ R₁ Jk :=
  ⟨fun hc => h₂ hc.1, fun hc => h₁ hc.1⟩

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

/-- **Informational Independence (arXiv Def 6.2).**

    A type G is *informationally independent* when none of its components is
    recoverable from the others — equivalently, when G is structurally
    irreducible.

    In the equi-join setting, the sub-types `G[R₁]` and `G[R₂] \ Jk` making up
    the candidate are informationally independent within the result when no
    field of one is determined by the other through the combination of grain
    determination (`G[Rₘ]` determines all fields of `Rₘ`) and join equality
    (`r₁.Jk = r₂.Jk`).

    **This definition changed with the structural repair.** It previously read
    `iso (grain G) G`, which is a theorem for every `G` and so asserted
    nothing. It now unfolds to genuine irreducibility. -/
def InformationallyIndependent (G : D) : Prop :=
  Foundations.IsIrreducible G

/-- **GIT Condition (iii): the equi-join candidate is irreducible.**

    Under an admissible labeling, `F₁ = G[R₁] ∪ (G[R₂] \ Jk)` is structurally
    irreducible (arXiv Thm 7.2, irreducibility step). -/
theorem equijoin_candidate_irreducible (R₁ R₂ Jk : D)
    (h_adm : AdmissibleLabeling R₁ R₂ Jk) :
    Foundations.IsIrreducible (union (grain R₁) (diff (grain R₂) Jk)) :=
  fun S h_ssub h_iso =>
    EquiJoinStructure.equijoin_candidate_irred R₁ R₂ Jk S h_adm h_ssub h_iso

/-- The equi-join candidate `F₁ = G[R₁] ∪ (G[R₂] \ Jk)` is informationally
    independent (arXiv Def 6.2) under an admissible labeling. -/
theorem equijoin_candidate_informationally_independent (R₁ R₂ Jk : D)
    (h_adm : AdmissibleLabeling R₁ R₂ Jk) :
    InformationallyIndependent (union (grain R₁) (diff (grain R₂) Jk)) :=
  equijoin_candidate_irreducible R₁ R₂ Jk h_adm

/-- **G[F₁] ≅ F₁** — the candidate is its own grain up to isomorphism.

    Now a *consequence* of irreducibility rather than the statement of
    condition (iii): an irreducible type is a grain of itself, and any two
    grains of a type are isomorphic. -/
theorem equijoin_candidate_idempotent (R₁ R₂ Jk : D)
    (h_adm : AdmissibleLabeling R₁ R₂ Jk) :
    iso (grain (union (grain R₁) (diff (grain R₂) Jk)))
        (union (grain R₁) (diff (grain R₂) Jk)) :=
  Relations.irreducible_iso_grain (equijoin_candidate_irreducible R₁ R₂ Jk h_adm)

end GrainTheory.Inference
