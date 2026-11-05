/-
  GrainTheory.Model2.Schema — a second concrete model: 4 attributes, 2 FDs

  `Model.Schema` has one declared dependency, and one dependency cannot
  express the configuration that refutes the field-set reading of the grain
  lattice: two grains that share no field, are grain-incomparable, and both
  determine a third. This model can.

      Attr = {0, 1, 2, 3}  =  {OrderId, TicketId, CustomerId, Qty}
      declared FDs        :  OrderId → CustomerId,  TicketId → CustomerId

  As in `Model.Schema`, a type is a set of attributes (`Finset Attr`), so the
  universe has 16 elements, every relation is decidable, and every statement
  below is settled by `decide`. The interpretation is the one of the paper's
  Definition "Denotation of a type under a declaration set" with types as
  attribute sets:

  | Abstract | Concrete | Paper |
  |---|---|---|
  | `ssub A B` (`⊑`) | `A ⊆ B` | structural subtype |
  | `sub A B` (`⊆typ`) | `A ⊆ cl B` | B *determines* A |
  | `iso A B` (`≅`) | mutual determination | isomorphism of denotations |
  | `grain R` | a minimal key of R | Def. grain |

  `cl` is the FD closure under the two declared dependencies.
-/

import Mathlib.Tactic

namespace GrainTheory.Model2

/-- Attributes: `0 = OrderId`, `1 = TicketId`, `2 = CustomerId`, `3 = Qty`. -/
abbrev Attr := Fin 4

/-- A type is a set of attributes. Sixteen of them. -/
abbrev Ty := Finset Attr

/-- FD closure for `OrderId → CustomerId` and `TicketId → CustomerId`:
    whenever an order or a ticket identifier is present, the customer is
    determined. Extensive, monotone and idempotent — checked below. -/
def cl (X : Ty) : Ty :=
  if (0 : Attr) ∈ X ∨ (1 : Attr) ∈ X then insert (2 : Attr) X else X

/-! ## The interpretation -/

/-- `⊑` — structural: every component of A occurs in B. -/
def ssub (A B : Ty) : Prop := A ⊆ B

/-- `⊆typ` — semantic: B determines A. -/
def sub (A B : Ty) : Prop := A ⊆ cl B

/-- `≅` — mutual determination. -/
def iso (A B : Ty) : Prop := A ⊆ cl B ∧ B ⊆ cl A

/-- The grain: a minimal key. `CustomerId` is determined whenever `OrderId`
    or `TicketId` is present, so it is dropped then; nothing else is ever
    determined, so nothing else is dropped. Where a type has several minimal
    keys this picks one, as the paper's operator may. -/
def grain (R : Ty) : Ty :=
  if (0 : Attr) ∈ R ∨ (1 : Attr) ∈ R then R.erase (2 : Attr) else R

/-! ## Decidability -/

instance (A B : Ty) : Decidable (ssub A B) := inferInstanceAs (Decidable (A ⊆ B))
instance (A B : Ty) : Decidable (sub A B) := inferInstanceAs (Decidable (A ⊆ cl B))
instance (A B : Ty) : Decidable (iso A B) :=
  inferInstanceAs (Decidable (A ⊆ cl B ∧ B ⊆ cl A))

/-! ## The closure operator behaves -/

theorem cl_extensive : ∀ X : Ty, X ⊆ cl X := by decide
theorem cl_monotone : ∀ X Y : Ty, X ⊆ Y → cl X ⊆ cl Y := by decide
theorem cl_idempotent : ∀ X : Ty, cl (cl X) = cl X := by decide

/-- The grain has the closure of its type (the last sentence of the paper's
    closure lemma), and it is a key: it determines its type. -/
theorem grain_closure : ∀ R : Ty, cl (grain R) = cl R := by decide

end GrainTheory.Model2
