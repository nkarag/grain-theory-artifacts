/-
  GrainTheory.Model2.TheoremCheck — the grain lattice in the two-dependency
  model: the field-set reading refuted, the closure reading verified.

  `Model.TheoremCheck` proves, in the one-dependency model, that on
  grain-incomparable pairs the field-set intersection is the least upper
  bound. That is a fact of that model, not of the theory: with two
  determiners sharing a dependent it is false, and this file exhibits the
  failure. It then checks the statement the paper actually makes
  (Proposition "Lattice bounds on product types"): the least upper bound is
  the intersection of the two grains' **closures**, the greatest lower bound
  is their union, the unit type is the top and the full attribute set the
  bottom, and the field-set formulas are the bounds exactly when no
  declaration relates the two grains.

  This configuration is the counterexample an ICDT 2027 reviewer gave against
  the field-set statement; it is the same fact the model's own refutation of
  `sub_inter` (19 Aug 2026) had already expressed from the side of the axioms.
-/

import GrainTheory.Model2.Schema

namespace GrainTheory.Model2

/-- `≡_g` in the model. -/
def grainEq (A B : Ty) : Prop := iso (grain A) (grain B)
/-- `≤_g` in the model: finer ≤ coarser, i.e. the finer grain determines the coarser. -/
def grainLe (A B : Ty) : Prop := sub (grain B) (grain A)

instance (A B : Ty) : Decidable (grainEq A B) := inferInstanceAs (Decidable (iso _ _))
instance (A B : Ty) : Decidable (grainLe A B) := inferInstanceAs (Decidable (sub _ _))

/-- Grain-incomparable: neither `≡_g` nor `≤_g` in either direction. -/
def incomp (R₁ R₂ : Ty) : Prop :=
  ¬ grainEq R₁ R₂ ∧ ¬ grainLe R₁ R₂ ∧ ¬ grainLe R₂ R₁
instance (a b : Ty) : Decidable (incomp a b) := inferInstanceAs (Decidable (_ ∧ _))

/-- `X` is the least upper bound of `R₁, R₂` in the `≤_g` poset. -/
def IsLub (R₁ R₂ X : Ty) : Prop :=
  grainLe R₁ X ∧ grainLe R₂ X ∧ ∀ Y : Ty, grainLe R₁ Y → grainLe R₂ Y → grainLe X Y
/-- `X` is the greatest lower bound of `R₁, R₂` in the `≤_g` poset. -/
def IsGlb (R₁ R₂ X : Ty) : Prop :=
  grainLe X R₁ ∧ grainLe X R₂ ∧ ∀ Y : Ty, grainLe Y R₁ → grainLe Y R₂ → grainLe Y X
instance (a b c : Ty) : Decidable (IsLub a b c) := inferInstanceAs (Decidable (_ ∧ _))
instance (a b c : Ty) : Decidable (IsGlb a b c) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## The field-set reading, refuted

  `Model.TheoremCheck.t_incomp_inter_is_lub` does not generalize. -/

theorem t_incomp_inter_is_lub_FAILS :
    ¬ (∀ R₁ R₂ : Ty, incomp R₁ R₂ → IsLub R₁ R₂ (R₁ ∩ R₂)) := by decide

/-- The counterexample, spelled out. `OrderId` and `TicketId` are
    grain-incomparable and share no field, so their field-set intersection is
    the empty type (the unit type, top of the order). But `CustomerId` is an
    upper bound of both, and the empty type is not below it: so the empty type
    is an upper bound and not the least one. The least upper bound is
    `CustomerId`. -/
example :
    incomp ({0} : Ty) ({1} : Ty)
    ∧ ({0} : Ty) ∩ ({1} : Ty) = ∅
    ∧ grainLe ({0} : Ty) ({2} : Ty) ∧ grainLe ({1} : Ty) ({2} : Ty)
    ∧ ¬ grainLe (∅ : Ty) ({2} : Ty)
    ∧ ¬ IsLub ({0} : Ty) ({1} : Ty) ∅
    ∧ IsLub ({0} : Ty) ({1} : Ty) ({2} : Ty) := by decide

/-- The same fact on the grains, the form `Relations/Lattice.lean` uses:
    `grainJoin` (intersection of the grains) is not the lub in general. Its
    universal property there carries **structural** hypotheses, which is the
    determination-free case below, and that is why the abstract theorem stands. -/
theorem t_grainJoin_is_lub_FAILS :
    ¬ (∀ R₁ R₂ : Ty, IsLub R₁ R₂ (grain R₁ ∩ grain R₂)) := by decide

/-! ## The closure reading, verified: Proposition "Lattice bounds on product types" -/

/-- Item (1): the product on the intersection of the two grains' closures is
    the least upper bound, for every pair. -/
theorem t_closure_inter_is_lub :
    ∀ R₁ R₂ : Ty, IsLub R₁ R₂ (cl (grain R₁) ∩ cl (grain R₂)) := by decide

/-- Item (2): the union of the two grains is the greatest lower bound, for
    every pair; so is the union of the types, which is `≡_g` to it. -/
theorem t_grain_union_is_glb :
    ∀ R₁ R₂ : Ty, IsGlb R₁ R₂ (grain R₁ ∪ grain R₂) := by decide
theorem t_union_is_glb :
    ∀ R₁ R₂ : Ty, IsGlb R₁ R₂ (R₁ ∪ R₂) := by decide
theorem t_glb_forms_agree :
    ∀ R₁ R₂ : Ty, grainEq (grain R₁ ∪ grain R₂) (R₁ ∪ R₂) := by decide

/-- Item (3): the empty type (unit) is the top, the full attribute set the bottom. -/
theorem t_top : ∀ R : Ty, grainLe R ∅ := by decide
theorem t_bottom : ∀ R : Ty, grainLe (Finset.univ : Ty) R := by decide

/-- Item (4): when closure fixes both grains and their union, the field-set
    formulas are the bounds. Fixing the union alone is **not** enough, and
    `decide` says so: with `OrderId → CustomerId`, closure fixes
    `{OrderId, CustomerId}` but not its subset `{OrderId}`, and the pair
    `{OrderId}`, `{CustomerId}` is comparable with lub `{CustomerId}`, not the
    empty intersection. The first draft of this statement carried the weaker
    hypothesis and the paper's item (4) was corrected with it. -/
theorem t_detfree_inter_is_lub :
    ∀ R₁ R₂ : Ty,
      cl (grain R₁) = grain R₁ → cl (grain R₂) = grain R₂ →
      cl (grain R₁ ∪ grain R₂) = grain R₁ ∪ grain R₂ →
      IsLub R₁ R₂ (grain R₁ ∩ grain R₂) := by decide

/-- The weaker hypothesis fails: fixing the union is not the determination-free
    case. -/
theorem t_union_fixed_not_enough_FAILS :
    ¬ (∀ R₁ R₂ : Ty, cl (grain R₁ ∪ grain R₂) = grain R₁ ∪ grain R₂ →
      IsLub R₁ R₂ (grain R₁ ∩ grain R₂)) := by decide

example :
    cl (grain ({0} : Ty) ∪ grain ({2} : Ty)) = grain ({0} : Ty) ∪ grain ({2} : Ty)
    ∧ ¬ IsLub ({0} : Ty) ({2} : Ty) (grain ({0} : Ty) ∩ grain ({2} : Ty))
    ∧ IsLub ({0} : Ty) ({2} : Ty) ({2} : Ty) := by decide

/-- Item (5): on comparable pairs the bounds are the endpoints. -/
theorem t_comparable_lub : ∀ R₁ R₂ : Ty, grainLe R₂ R₁ → IsLub R₁ R₂ R₁ := by decide
theorem t_comparable_glb : ∀ R₁ R₂ : Ty, grainLe R₂ R₁ → IsGlb R₁ R₂ R₂ := by decide

/-- The bounds are unique up to `≡_g` (antisymmetry, checked in `AxiomCheck`). -/
theorem t_lub_unique :
    ∀ R₁ R₂ X Y : Ty, IsLub R₁ R₂ X → IsLub R₁ R₂ Y → grainEq X Y := by decide

end GrainTheory.Model2
