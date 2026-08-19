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

/-- **The counterexample, on a genuine equi-join.**

    Schema: `CustomerId → CustomerName, Email`.

    * `R₁ = {CustomerId, CustomerName}`, so `G[R₁] = {CustomerId}`;
    * `R₂ = {CustomerName, Email}`, so `G[R₂] = {CustomerName, Email}`;
    * `Jk = {CustomerName}` — non-empty and present in both inputs, so this is a
      real equi-join, not a cross product;
    * `G₁^Jk = ∅ ⊑ {CustomerName} = G₂^Jk`, so the labeling is **canonical**.

    The candidate is `{CustomerId} ∪ ({CustomerName, Email} − {CustomerName})`
    `= {CustomerId, Email}`. But `CustomerId` determines `Email`, so
    `{CustomerId}` is a proper structural subtype of the candidate that is still
    isomorphic to it: the candidate is **reducible**, and the grain of the result
    is `{CustomerId}`.

    The offending determination runs from `R₁`'s grain to `R₂`'s non-join part —
    across the inputs, *outside* the join key. That is precisely what the
    appendix argument assumes away when it says a non-`Jk` field is "recovered
    neither from the remaining fields of that grain nor, lying outside `Jk`,
    through the join", and it is what the canonical labeling does not exclude. -/
example :
    ({1} : Ty) ≠ ∅                                   -- the join key is non-empty
    ∧ ssub ({1} : Ty) ({0, 1} : Ty)                  -- Jk ⊑ R₁
    ∧ ssub ({1} : Ty) ({1, 2} : Ty)                  -- Jk ⊑ R₂
    ∧ grain ({0, 1} : Ty) = {0}                      -- G[R₁] = {CustomerId}
    ∧ grain ({1, 2} : Ty) = {1, 2}                   -- G[R₂] = {Name, Email}
    ∧ admissible {0, 1} {1, 2} {1}                   -- the labeling IS admissible
    ∧ (grain ({0, 1} : Ty) ∪ (grain ({1, 2} : Ty) \ {1})) = {0, 2}  -- candidate
    ∧ ssub ({0} : Ty) ({0, 2} : Ty)                  -- {CustomerId} ⊑ candidate
    ∧ iso ({0} : Ty) ({0, 2} : Ty)                   -- and isomorphic to it
    ∧ ¬ ssub ({0, 2} : Ty) ({0} : Ty)                -- properly — so REDUCIBLE
    ∧ ¬ indepM (grain ({0, 1} : Ty)) (grain ({1, 2} : Ty) \ {1})  -- indep fails
    := by decide

/-- The failure is not an artifact of degenerate join keys: it persists when
    `Jk` is non-empty and structurally present in both inputs. -/
theorem d_fails_for_genuine_equijoins :
    ¬ (∀ R₁ R₂ Jk S : Ty,
        Jk ≠ ∅ → ssub Jk R₁ → ssub Jk R₂ →
        admissible R₁ R₂ Jk →
        ssub S (grain R₁ ∪ (grain R₂ \ Jk)) →
        iso S (grain R₁ ∪ (grain R₂ \ Jk)) →
        ssub (grain R₁ ∪ (grain R₂ \ Jk)) S) := by decide

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

/-! ## Part 4 — the two axioms added for Grain Reduction

  arXiv §7 Proposition [Grain Reduction under Declared FDs] needs a
  minimization principle, and Prop 7.3 cases 1–2 need independence to be
  vacuous against an empty component. Both are checked here. -/

/-- `indep_bot`: independence against the empty type is vacuous. -/
theorem d_indep_bot : ∀ A B : Ty, (∀ T : Ty, B ⊆ T) → indepM A B := by decide

/-- `ssub_wf`, instantiated at the predicate that matters — "still isomorphic to
    `Res`". Every type isomorphic to `Res` has a `⊑`-minimal structural subtype
    that is still isomorphic to it, and that minimal element is exactly a grain.

    This is the superkey-to-candidate-key reduction, and it is what makes the
    fixpoint of the paper's deletion procedure well-defined. -/
theorem d_ssub_wf_at_iso : ∀ G Res : Ty, iso G Res →
    ∃ K : Ty, ssub K G ∧ iso K Res ∧ ∀ T : Ty, ssub T K → iso T Res → ssub K T := by
  decide

/-- **Grain Reduction, end to end.** Any superkey of `Res` reduces to a grain of
    `Res` sitting structurally inside it. -/
theorem d_grain_reduction : ∀ G Res : Ty, iso G Res →
    ∃ K : Ty, ssub K G ∧ IsGrainOf K Res := by decide

/-- And the reduction is not idle: a superkey that is *not* already a grain
    really does shrink. Witness: `{CustomerId, CustomerName}` identifies
    `Customer` but reduces to `{CustomerId}`. -/
example :
    iso ({0, 1} : Ty) {0, 1}
    ∧ ¬ IsGrainOf ({0, 1} : Ty) {0, 1}
    ∧ ssub ({0} : Ty) ({0, 1} : Ty)
    ∧ IsGrainOf ({0} : Ty) {0, 1} := by decide

end GrainTheory.Model
