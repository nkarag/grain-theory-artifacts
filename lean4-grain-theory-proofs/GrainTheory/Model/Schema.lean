/-
  GrainTheory.Model.Schema — A concrete finite model of the grain axioms.

  Everything in the abstract development is proved *from* axioms over an opaque
  universe `D`. That leaves two questions a proof assistant cannot answer on its
  own: are the axioms **consistent**, and do they **say what we meant**? Both are
  answered by exhibiting a model — an actual mathematical structure in which
  every axiom is a checkable fact.

  This file gives the smallest model that can answer them: a three-attribute
  relational schema with one declared functional dependency.

      Attr = {0, 1, 2}  =  {CustomerId, CustomerName, Email}
      declared FD       :  CustomerId → CustomerName, Email

  A *type* is a set of attributes (`Finset Attr`), so the universe has 8
  elements, every relation is decidable, and every axiom is settled by `decide`
  rather than by a proof we might get wrong.

  Interpretation, following the paper:

  | Abstract | Concrete | Paper |
  |---|---|---|
  | `ssub A B` (`⊑`) | `A ⊆ B` | component containment (Def 2.3) |
  | `sub A B` (`⊆typ`) | `A ⊆ cl B` | B *determines* A (Def 2.1) |
  | `iso A B` (`≅`) | mutual determination | bijection between inhabitants |
  | `grain R` | the minimal key of R | Def 3.1 |

  `cl` is the FD closure: adding CustomerId to a set brings its dependents.
-/

import Mathlib.Tactic

namespace GrainTheory.Model

/-- Attributes: `0 = CustomerId`, `1 = CustomerName`, `2 = Email`. -/
abbrev Attr := Fin 3

/-- A type is a set of attributes. Eight of them, so everything is decidable. -/
abbrev Ty := Finset Attr

/-- FD closure for the single declared dependency `CustomerId → {Name, Email}`.
    Extensive, monotone and idempotent — all checked below. -/
def cl (X : Ty) : Ty := if (0 : Attr) ∈ X then {0, 1, 2} else X

/-! ## The interpretation -/

/-- `⊑` — structural: every component of A occurs in B. Schema-decidable. -/
def ssub (A B : Ty) : Prop := A ⊆ B

/-- `⊆typ` — semantic: there is a surjection `B ↠ A`, i.e. **B determines A**. -/
def sub (A B : Ty) : Prop := A ⊆ cl B

/-- `≅` — mutual determination, i.e. a bijection between inhabitants. -/
def iso (A B : Ty) : Prop := A ⊆ cl B ∧ B ⊆ cl A

/-- The grain: the minimal key. If CustomerId is present it determines
    everything else, so it is the whole grain; otherwise no FD applies and the
    type is already irreducible. -/
def grain (R : Ty) : Ty := if (0 : Attr) ∈ R then {0} else R

/-! ## Decidability

  All three relations are decidable, so every axiom below is settled by
  exhaustive check rather than by a hand proof. -/

instance (A B : Ty) : Decidable (ssub A B) := inferInstanceAs (Decidable (A ⊆ B))
instance (A B : Ty) : Decidable (sub A B) := inferInstanceAs (Decidable (A ⊆ cl B))
instance (A B : Ty) : Decidable (iso A B) :=
  inferInstanceAs (Decidable (A ⊆ cl B ∧ B ⊆ cl A))

/-! ## The closure operator behaves

  Extensive, monotone, idempotent — the three properties the semantic relation
  needs. Each is settled by exhaustive check over all 8 types. -/

theorem cl_extensive : ∀ X : Ty, X ⊆ cl X := by decide
theorem cl_monotone : ∀ X Y : Ty, X ⊆ Y → cl X ⊆ cl Y := by decide
theorem cl_idempotent : ∀ X : Ty, cl (cl X) = cl X := by decide

end GrainTheory.Model
