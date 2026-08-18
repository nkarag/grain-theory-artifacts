/-
  GrainTheory.Model.AxiomCheck — every GrainStructure axiom, checked against
  the concrete schema of `Model.Schema`.

  Each statement below is the corresponding axiom of `GrainStructure`, with the
  abstract symbols replaced by their concrete meanings, and settled by `decide`
  over all eight types. Nothing here is proved by hand, so nothing here can be
  wrong in the way a hand proof can.

  The file is in two halves: the axioms that HOLD, and the axioms that FAIL.
-/

import GrainTheory.Model.Schema

namespace GrainTheory.Model

/-! ## Part 1 — axioms that hold in the model -/

theorem m_sub_refl : ∀ R : Ty, sub R R := by decide
theorem m_sub_trans : ∀ R S T : Ty, sub R S → sub S T → sub R T := by decide
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

-- product is interpreted as ∪typ in this model (see the note in the report)
theorem m_ssub_prod_left : ∀ A B : Ty, ssub A (A ∪ B) := by decide
theorem m_ssub_prod_right : ∀ A B : Ty, ssub B (A ∪ B) := by decide
theorem m_prod_iso : ∀ A B C E : Ty, iso A B → iso C E → iso (A ∪ C) (B ∪ E) := by decide
theorem m_prod_comm_iso : ∀ A B : Ty, iso (A ∪ B) (B ∪ A) := by decide

/-! ## Part 2 — axioms that FAIL in the model

  Two axioms of `GrainStructure` are **false** under the intended reading of
  `⊆typ`. Both are the *semantic* twins I introduced during the notation split,
  on the reasoning that "a law with `⊆typ` hypotheses cannot be derived from its
  structural version". That reasoning was right; what I failed to ask was
  whether the semantic version is *true*. It is not.

  The failure is not subtle once stated. `⊆typ` means **determines**, and
  determination does not distribute over set operations the way containment
  does. Both counterexamples are exhibited, not merely asserted. -/

/-- **`sub_inter` is FALSE.** "If T is determined by R and by S, then T is
    determined by `R ∩typ S`." Determination does not work that way: two
    different sources can each determine T while their shared columns determine
    nothing at all. -/
theorem m_sub_inter_FAILS :
    ¬ (∀ R S T : Ty, sub T R → sub T S → sub T (R ∩ S)) := by decide

/-- The witness, spelled out: `Name` is determined by `{CustomerId}` (the FD)
    and by `{Name}` (trivially), but `{CustomerId} ∩ {Name} = ∅` determines
    nothing. -/
example : sub {1} {0} ∧ sub {1} {1} ∧ ¬ sub {1} (({0} : Ty) ∩ {1}) := by decide

/-- **`diff_sub_left` is FALSE.** "If A is determined by B, then `A −typ C` is
    determined by `B −typ C`." Removing columns from a determiner can destroy
    the determination outright. -/
theorem m_diff_sub_left_FAILS :
    ¬ (∀ A B C : Ty, sub A B → sub (A \ C) (B \ C)) := by decide

/-- The witness: `{Name}` is determined by `{CustomerId}`, but after removing
    `CustomerId` from both sides the determiner is empty and determines
    nothing. -/
example : sub {1} {0} ∧ ¬ sub (({1} : Ty) \ {0}) (({0} : Ty) \ {0}) := by decide

/-! ### Two further casualties, from lemmas that read `⊆typ` as containment -/

/-- `diff_sub_of_sub` (JoinSpecialCases) claims "if `A ⊆typ B` then `A −typ B`
    is empty". True for containment, false for determination: B can determine A
    without containing a single one of A's columns. -/
theorem m_diff_sub_of_sub_FAILS :
    ¬ (∀ A B T : Ty, sub A B → sub (A \ B) T) := by decide

/-- `inter_mono_left` (EquiJoinAxioms) claims determination is monotone under
    intersection with a fixed C. It is not. -/
theorem m_inter_mono_left_FAILS :
    ¬ (∀ A B C : Ty, sub A B → sub (A ∩ C) (B ∩ C)) := by decide

/-! ## Part 3 — what the model was built to witness

  These are the facts the abstract axiomatization cannot establish about
  itself, and they are the reason a model is not optional. -/

/-- **The two relations genuinely differ.** `⊑ ⇒ ⊆typ` but not conversely, so
    the degenerate reading `⊑ = ⊆typ` — which satisfies every axiom in
    `Basic.lean` — is refuted here.

    The witness is the Customer example, in the direction the paper states it:
    `CustomerId × CustomerName ⊆typ CustomerId` (the declared determination
    `CustomerId ↠ CustomerName` supplies the surjection) while
    `CustomerId × CustomerName ⋢ CustomerId` (`CustomerName` is not a component
    of `CustomerId`). -/
theorem separation : ∃ A B : Ty, sub A B ∧ ¬ ssub A B :=
  ⟨{0, 1}, {0}, by decide, by decide⟩

/-- **Irreducibility is not vacuous.** There is a type isomorphic to `R` that is
    *not* a grain of `R` — the padded candidate `{CustomerId, CustomerName}`,
    which has the proper structural subtype `{CustomerId}` that is still
    isomorphic to `R`.

    Under the pre-revision definition no such type could exist, for any `R`.
    That this now has a witness is exactly the content of the repair. -/
theorem irreducibility_bites :
    ∃ R T S : Ty, iso T R ∧ iso S R ∧ ssub S T ∧ ¬ ssub T S :=
  ⟨{0, 1}, {0, 1}, {0}, by decide, by decide, by decide, by decide⟩

/-- **The grain is selected, not merely constrained.** `{CustomerId}` is a grain
    of `Customer`; the padded `{CustomerId, CustomerName}` is isomorphic to it
    but is *not* a grain. Before the repair, both qualified. -/
theorem grain_selects :
    iso ({0} : Ty) {0, 1} ∧ iso ({0, 1} : Ty) {0, 1} ∧
    (∀ S : Ty, ssub S {0} → iso S {0, 1} → ssub ({0} : Ty) S) ∧
    ¬ (∀ S : Ty, ssub S {0, 1} → iso S {0, 1} → ssub ({0, 1} : Ty) S) := by
  decide

end GrainTheory.Model
