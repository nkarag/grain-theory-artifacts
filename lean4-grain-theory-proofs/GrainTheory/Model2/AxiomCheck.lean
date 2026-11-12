/-
  GrainTheory.Model2.AxiomCheck — every GrainStructure axiom that
  `Model.AxiomCheck` settles, settled again in the two-dependency model.

  A second model is a second consistency witness for the axiom set, and the
  first in which two distinct determiners share a dependent. Everything is
  by `decide` over all sixteen types.
-/

import GrainTheory.Model2.Schema

namespace GrainTheory.Model2

/-! ## The axioms that hold (the same list as `Model.AxiomCheck`, Part 1) -/

theorem m_sub_refl : ∀ R : Ty, sub R R := by decide
theorem m_sub_trans : ∀ R S T : Ty, sub R S → sub S T → sub R T := by decide
/-- Antisymmetry of `⊆typ` up to isomorphism: an **axiom** of the abstract
    class, discharged here by decision procedure, as in `Model.AxiomCheck`. -/
theorem m_sub_antisymm : ∀ R S : Ty, sub R S → sub S R → iso R S := by decide

theorem m_ssub_refl : ∀ R : Ty, ssub R R := by decide
theorem m_ssub_trans : ∀ R S T : Ty, ssub R S → ssub S T → ssub R T := by decide
theorem m_ssub_antisymm : ∀ R S : Ty, ssub R S → ssub S R → iso R S := by decide
theorem m_ssub_sub : ∀ R S : Ty, ssub R S → sub R S := by decide

theorem m_iso_refl : ∀ R : Ty, iso R R := by decide
theorem m_iso_symm : ∀ R S : Ty, iso R S → iso S R := by decide
theorem m_iso_trans : ∀ R S T : Ty, iso R S → iso S T → iso R T := by decide
theorem m_iso_sub : ∀ A B C : Ty, iso A B → sub C B → sub C A := by decide

theorem m_grain_sub : ∀ R : Ty, sub (grain R) R := by decide
theorem m_grain_iso : ∀ R : Ty, iso (grain R) R := by decide
theorem m_grain_irred :
    ∀ R S : Ty, ssub S (grain R) → iso S R → ssub (grain R) S := by decide

theorem m_ssub_union_left : ∀ R S : Ty, ssub R (R ∪ S) := by decide
theorem m_ssub_union_right : ∀ R S : Ty, ssub S (R ∪ S) := by decide
theorem m_union_ssub : ∀ R S T : Ty, ssub R T → ssub S T → ssub (R ∪ S) T := by decide
theorem m_union_sub : ∀ R S T : Ty, sub R T → sub S T → sub (R ∪ S) T := by decide

theorem m_inter_ssub_left : ∀ R S : Ty, ssub (R ∩ S) R := by decide
theorem m_inter_ssub_right : ∀ R S : Ty, ssub (R ∩ S) S := by decide
theorem m_ssub_inter : ∀ R S T : Ty, ssub T R → ssub T S → ssub T (R ∩ S) := by decide

theorem m_ssub_diff : ∀ R S : Ty, ssub (R \ S) R := by decide
theorem m_ssub_union_diff : ∀ R S : Ty, ssub R (S ∪ (R \ S)) := by decide
theorem m_ssub_inter_union_diff : ∀ R S : Ty, ssub R ((R ∩ S) ∪ (R \ S)) := by decide
theorem m_diff_inter_empty : ∀ A B T : Ty, ssub ((A \ B) ∩ B) T := by decide
theorem m_diff_ssub_left : ∀ A B C : Ty, ssub A B → ssub (A \ C) (B \ C) := by decide
theorem m_inter_distrib_union :
    ∀ A B C : Ty, ssub (A ∩ (B ∪ C)) ((A ∩ B) ∪ (A ∩ C)) := by decide

theorem m_grain_union : ∀ R S : Ty, iso (grain (R ∪ S)) (grain R ∪ grain S) := by decide

-- product is interpreted as ∪typ in this model, as in `Model.AxiomCheck`
theorem m_ssub_prod_left : ∀ A B : Ty, ssub A (A ∪ B) := by decide
theorem m_ssub_prod_right : ∀ A B : Ty, ssub B (A ∪ B) := by decide
theorem m_prod_comm_iso : ∀ A B : Ty, iso (A ∪ B) (B ∪ A) := by decide

/-! ## The axioms that fail, fail here too -/

/-- `sub_inter` is false here as well: `CustomerId` is determined by
    `{OrderId}` and by `{TicketId}`, whose intersection is empty. This is the
    same fact as the lattice counterexample in `TheoremCheck`, seen from the
    axioms. -/
theorem m_sub_inter_FAILS :
    ¬ (∀ R S T : Ty, sub T R → sub T S → sub T (R ∩ S)) := by decide

example : sub {2} {0} ∧ sub {2} {1} ∧ ¬ sub {2} (({0} : Ty) ∩ {1}) := by decide

theorem m_diff_sub_left_FAILS :
    ¬ (∀ A B C : Ty, sub A B → sub (A \ C) (B \ C)) := by decide

/-! ## The closure axioms of `ClosureStructure`, in the two-dependency model

  Here the closure has content on incomparable pairs (see `TheoremCheck`), and
  the four axioms of `Relations/ClosureLattice.lean` still hold. -/

theorem m_cl_extensive : ∀ A : Ty, ssub A (cl A) := by decide
theorem m_cl_monotone : ∀ A B : Ty, ssub A B → ssub (cl A) (cl B) := by decide
theorem m_cl_idempotent : ∀ A : Ty, ssub (cl (cl A)) (cl A) := by decide
theorem m_sub_iff_ssub_cl : ∀ A B : Ty, sub A B ↔ ssub A (cl B) := fun _ _ => Iff.rfl

/-! ## Separation and non-vacuity, again -/

theorem separation : ∃ A B : Ty, sub A B ∧ ¬ ssub A B :=
  ⟨{0, 2}, {0}, by decide, by decide⟩

theorem irreducibility_bites :
    ∃ R T S : Ty, iso T R ∧ iso S R ∧ ssub S T ∧ ¬ ssub T S :=
  ⟨{0, 2}, {0, 2}, {0}, by decide, by decide, by decide, by decide⟩

end GrainTheory.Model2
