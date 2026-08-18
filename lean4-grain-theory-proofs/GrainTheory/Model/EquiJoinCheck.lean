/-
  GrainTheory.Model.EquiJoinCheck — the equi-join chain, checked in the model.

  `EquiJoinStructure` extends `GrainStructure` with a determination relation and
  ten axioms, one of which — `equijoin_candidate_irred` — carries the entire
  irreducibility step of arXiv Thm 7.2. That axiom is the least-scrutinized part
  of the development: it is stated, justified in prose from the appendix
  argument, and then relied on by the centerpiece theorem.

  This file interprets `determines` concretely and checks all of it.

  **The interpretation.** `determines A B` means "A functionally determines B",
  i.e. `B ⊆ cl A`. Note this is exactly `sub B A` — the semantic subtype
  relation transposed, since `sub A B` was defined as "B determines A". So the
  determination layer adds no new primitive to the model.

  **Scope caveat.** The product `×` is interpreted as `∪typ`. For the equi-join
  that is faithful rather than a compromise: the result type
  `(R₁ −typ Jk) × (R₂ −typ Jk) × Jk` is built from three *pairwise disjoint*
  field sets, and on disjoint field sets product and union agree.
-/

import GrainTheory.Model.TheoremCheck

namespace GrainTheory.Model

/-- `A` functionally determines `B`. Equivalently `sub B A`. -/
def determines (A B : Ty) : Prop := B ⊆ cl A

instance (A B : Ty) : Decidable (determines A B) := inferInstanceAs (Decidable (_ ⊆ _))

/-! ## Part 1 — the ten `EquiJoinStructure` axioms -/

theorem d_grain_determines : ∀ R : Ty, determines (grain R) R := by decide

theorem d_determines_mono :
    ∀ G H R : Ty, determines G R → sub G H → determines H R := by decide

theorem d_determines_sub :
    ∀ G R S : Ty, determines G R → sub S R → determines G S := by decide

theorem d_determines_iso_of_sub :
    ∀ G R : Ty, determines G R → sub G R → iso G R := by decide

theorem d_determines_union :
    ∀ G A B : Ty, determines G A → determines G B → determines G (A ∪ B) := by decide

/-- `prod` is `∪typ` in this model, so this is `determines_union`. -/
theorem d_determines_prod :
    ∀ G A B : Ty, determines G A → determines G B → determines G (A ∪ B) := by decide

theorem d_determines_trans :
    ∀ G H R : Ty, determines G H → determines H R → determines G R := by decide

theorem d_determines_grain_sub :
    ∀ G R : Ty, determines G R → sub G R → sub (grain R) G := by decide

theorem d_iso_determines :
    ∀ S R : Ty, iso S R → sub S R → determines S R := by decide

/-! ## Part 2 — `equijoin_candidate_irred`

  The axiom carrying arXiv Thm 7.2's irreducibility step. Writing
  `Gᵢ^Jk = G[Rᵢ] ∩ Jk`, it asserts that the candidate
  `G[R₁] ∪ (G[R₂] − Jk)` is structurally irreducible whenever
  `¬ (G₂^Jk ⊏ G₁^Jk)`. -/

/-- The admissible-labeling gate: `¬ (G₂^Jk ⊏ G₁^Jk)`. -/
def admissible (R₁ R₂ Jk : Ty) : Prop :=
  ¬ (ssub (grain R₂ ∩ Jk) (grain R₁ ∩ Jk) ∧ ¬ ssub (grain R₁ ∩ Jk) (grain R₂ ∩ Jk))

instance (a b c : Ty) : Decidable (admissible a b c) := inferInstanceAs (Decidable (¬ _))

/-- Informational independence (arXiv Def 6.2) as a relation on the two
    candidate components: neither determines a component of the other that it
    does not already carry. -/
def indepM (A B : Ty) : Prop := cl A ∩ B ⊆ A ∧ cl B ∩ A ⊆ B
instance (A B : Ty) : Decidable (indepM A B) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The axiom as originally stated is FALSE.** The admissible labeling alone
    does not make the candidate irreducible. -/
theorem d_equijoin_candidate_irred_FAILS :
    ¬ (∀ R₁ R₂ Jk S : Ty,
        admissible R₁ R₂ Jk →
        ssub S (grain R₁ ∪ (grain R₂ \ Jk)) →
        iso S (grain R₁ ∪ (grain R₂ \ Jk)) →
        ssub (grain R₁ ∪ (grain R₂ \ Jk)) S) := by decide

/-- Nor do the physical-presence premises `Jk ⊑ Rᵢ` rescue it. -/
theorem d_physical_presence_does_not_rescue :
    ¬ (∀ R₁ R₂ Jk S : Ty,
        ssub Jk R₁ → ssub Jk R₂ → admissible R₁ R₂ Jk →
        ssub S (grain R₁ ∪ (grain R₂ \ Jk)) →
        iso S (grain R₁ ∪ (grain R₂ \ Jk)) →
        ssub (grain R₁ ∪ (grain R₂ \ Jk)) S) := by decide

/-- **With informational independence it holds.** This is the corrected axiom. -/
theorem d_equijoin_candidate_irred : ∀ R₁ R₂ Jk S : Ty,
    indepM (grain R₁) (grain R₂ \ Jk) →
    admissible R₁ R₂ Jk →
    ssub S (grain R₁ ∪ (grain R₂ \ Jk)) →
    iso S (grain R₁ ∪ (grain R₂ \ Jk)) →
    ssub (grain R₁ ∪ (grain R₂ \ Jk)) S := by decide

/-- The counterexample to the uncorrected form, spelled out.

    `R₁ = {CustomerId}`, `R₂ = {CustomerName}`, `Jk = ∅` (a cross join), with the
    declared FD `CustomerId → CustomerName`.

    Both join-key grain portions are empty, so the labeling is admissible. But
    the candidate is `{CustomerId, CustomerName}`, and `{CustomerId}` is a proper
    structural subtype of it that is still isomorphic to it — so the candidate is
    *reducible* and is not the grain.

    The appendix argues that a field of `G₂^rest` is "recovered neither from the
    rest of that grain nor, lying outside Jk, through the join". That assumes the
    only cross-input route is the join equality on `Jk`. A determination declared
    between the inputs *outside* `Jk` defeats it — the same root cause as the
    θ-join independence condition of Thm 3.8. -/
example :
    admissible {0} {1} ∅                          -- labeling is admissible
    ∧ ¬ indepM (grain ({0} : Ty)) (grain ({1} : Ty) \ ∅)   -- but not independent
    ∧ ssub ({0} : Ty) (grain ({0} : Ty) ∪ (grain ({1} : Ty) \ ∅))
    ∧ iso ({0} : Ty) (grain ({0} : Ty) ∪ (grain ({1} : Ty) \ ∅))
    ∧ ¬ ssub (grain ({0} : Ty) ∪ (grain ({1} : Ty) \ ∅)) ({0} : Ty)
    := by decide

/-- The labeling gate is not vacuous: the reverse labeling really can fail it. -/
theorem d_admissible_is_not_vacuous : ∃ R₁ R₂ Jk : Ty, ¬ admissible R₁ R₂ Jk := by decide

/-- And independence is not implied by admissibility. -/
theorem d_admissible_does_not_imply_indep :
    ∃ R₁ R₂ Jk : Ty, admissible R₁ R₂ Jk ∧ ¬ indepM (grain R₁) (grain R₂ \ Jk) := by decide

/-! ## Part 3 — the capstone

  With both side conditions in place, `equijoin_grain_identity` verifies: the
  candidate really is a grain of the result. -/

/-- `Res = (R₁ − Jk) × (R₂ − Jk) × Jk`, which on pairwise disjoint field sets is
    their union. -/
def joinRes (R₁ R₂ Jk : Ty) : Ty := (R₁ \ Jk) ∪ (R₂ \ Jk) ∪ Jk

theorem d_equijoin_grain_identity : ∀ R₁ R₂ Jk : Ty,
    ssub Jk R₁ → ssub Jk R₂ →
    indepM (grain R₁) (grain R₂ \ Jk) →
    admissible R₁ R₂ Jk →
    IsGrainOf (grain R₁ ∪ (grain R₂ \ Jk)) (joinRes R₁ R₂ Jk) := by decide

end GrainTheory.Model
