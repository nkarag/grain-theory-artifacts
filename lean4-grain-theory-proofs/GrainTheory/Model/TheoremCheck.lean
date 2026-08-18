/-
  GrainTheory.Model.TheoremCheck — do the *theorems* survive?

  `AxiomCheck` found two axioms of `GrainStructure` false in the model. That
  raises the real question: are the theorems proved from them also false, or do
  the theorems hold while only their *proofs* route through a bad premise?

  This file states the conclusions of the affected results directly in the
  model and checks them exhaustively. A theorem that holds here is sound and
  merely needs its proof rerouted; one that fails here would have to be
  retracted.
-/

import GrainTheory.Model.Schema

namespace GrainTheory.Model

/-- `≡_g` in the model. -/
def grainEq (A B : Ty) : Prop := iso (grain A) (grain B)
/-- `≤_g` in the model. -/
def grainLe (A B : Ty) : Prop := sub (grain B) (grain A)

instance (A B : Ty) : Decidable (grainEq A B) := inferInstanceAs (Decidable (iso _ _))
instance (A B : Ty) : Decidable (grainLe A B) := inferInstanceAs (Decidable (sub _ _))

/-- `IsGrainOf` in the model. -/
def IsGrainOf (G R : Ty) : Prop :=
  iso G R ∧ ∀ S : Ty, ssub S G → iso S R → ssub G S

instance (G R : Ty) : Decidable (IsGrainOf G R) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## The results whose proofs route through the false axioms -/

/-! ### FAILS — Lattice Absorption, lub half

  `(R₁ ∩typ R₂) ≡_g R₁` whenever `R₂ ≤_g R₁`. **This is false**, and the model
  exhibits the counterexample.

  The paper's proof (appendix, Thm Lattice Absorption, step (i)) reads:

  > `G[R₁] ⊆typ R₁`; from the premise `G[R₁] ⊆typ G[R₂] ⊆typ R₂`, so
  > `G[R₁] ⊆typ R₂`. **By the universal property of intersection,**
  > `G[R₁] ⊆typ (R₁ ∩typ R₂)`.

  That last step is exactly the `sub_inter` axiom refuted in `AxiomCheck`. The
  universal property of intersection holds for *containment*, not for
  *determination*: being determined by `R₁` and by `R₂` says nothing about
  being determined by the fields they happen to share. -/

theorem t_intersection_grain_FAILS :
    ¬ (∀ R₁ R₂ : Ty, sub (grain R₁) (grain R₂) → grainEq R₁ (R₁ ∩ R₂)) := by decide

theorem t_intersection_grain_isGrainOf_FAILS :
    ¬ (∀ R₁ R₂ : Ty, sub (grain R₁) (grain R₂) → IsGrainOf (grain R₁) (R₁ ∩ R₂)) := by
  decide

/-- The counterexample, spelled out.

    `R₁ = {CustomerName}`, `R₂ = {CustomerId}`, with the declared FD
    `CustomerId → CustomerName`.

    * `G[R₁] = {CustomerName}`, `G[R₂] = {CustomerId}`;
    * the premise holds: `CustomerId` determines `CustomerName`, so
      `G[R₁] ⊆typ G[R₂]`, i.e. `R₂ ≤_g R₁`;
    * but `R₁ ∩typ R₂ = ∅`, and the empty type is not grain-equal to
      `{CustomerName}`.

    Two types whose grains are related by a *declared* determination need share
    no fields at all — and then their field-set intersection carries none of the
    information the theorem claims it retains. -/
example :
    sub (grain ({1} : Ty)) (grain ({0} : Ty))     -- premise: R₂ ≤_g R₁
    ∧ ({1} : Ty) ∩ ({0} : Ty) = ∅                 -- the intersection is empty
    ∧ ¬ grainEq ({1} : Ty) (({1} : Ty) ∩ ({0} : Ty)) := by decide

/-! ### HOLDS — Lattice Absorption, glb half

  The `∪typ` half is unaffected: its proof routes through Armstrong A5, not
  through the intersection axiom. -/

/-- Union with grain (Lattice Absorption, glb half). -/
theorem t_union_grain :
    ∀ R₁ R₂ : Ty, sub (grain R₁) (grain R₂) → grainEq R₂ (R₁ ∪ R₂) := by decide

/-- Grain Inference (Thm 5.10), the workhorse. -/
theorem t_grain_inference_isGrainOf :
    ∀ G R : Ty, sub G R → grainLe G R →
      (∀ S : Ty, ssub S G → iso S G → ssub G S) → IsGrainOf G R := by decide

/-- Grain idempotency. -/
theorem t_grain_idempotent : ∀ R : Ty, iso (grain (grain R)) (grain R) := by decide

/-- Grain uniqueness / Multiple Grains. -/
theorem t_multiple_grains :
    ∀ G₁ G₂ R : Ty, IsGrainOf G₁ R → IsGrainOf G₂ R → iso G₁ G₂ := by decide

/-- Grain Subset–Ordering Equivalence (Lemma 5.4). -/
theorem t_grain_subset : ∀ R₁ R₂ : Ty, sub (grain R₁) (grain R₂) → grainLe R₂ R₁ := by decide

/-- The grain determines every subset of its type (Cor 5.5). -/
theorem t_grain_determines_subsets :
    ∀ R R' : Ty, sub R' R → grainLe (grain R) R' := by decide

/-! ## The lattice claim — verified

  §5 states that `≤_g` forms a bounded lattice whose lub and glb are given by
  universal properties, and that on product types they coincide with the
  field-set `∩typ` and `∪typ` operations.

  Two things fix the reading, and both matter:

  * **Definition 5.3.** The surjection witnessing `≤_g` comes in one of two
    forms — a *structural* projection from shared product structure, or a
    *declared* determination such as a foreign key. Both are admissible, so
    `≤_g` is the semantic relation.
  * **Definition 5.12.** The lattice operations are what resolve
    *grain-incomparable* components. For a comparable pair the lub and glb are
    just the coarser and finer element; no formula is needed, and that is
    exactly what Lattice Absorption states.

  Checked against that reading, the claim holds. -/

/-- Def 5.12: grain-incomparable — neither `≡_g` nor `≤_g` in either direction. -/
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

/-! ### On grain-incomparable pairs, the field-set formulas ARE the lub and glb -/

theorem t_incomp_inter_is_lub :
    ∀ R₁ R₂ : Ty, incomp R₁ R₂ → IsLub R₁ R₂ (R₁ ∩ R₂) := by decide

theorem t_incomp_union_is_glb :
    ∀ R₁ R₂ : Ty, incomp R₁ R₂ → IsGlb R₁ R₂ (R₁ ∪ R₂) := by decide

/-- And on the grains — the form `Relations/Lattice.lean` uses. -/
theorem t_incomp_grainJoin_is_lub :
    ∀ R₁ R₂ : Ty, incomp R₁ R₂ → IsLub R₁ R₂ (grain R₁ ∩ grain R₂) := by decide

theorem t_incomp_grainMeet_is_glb :
    ∀ R₁ R₂ : Ty, incomp R₁ R₂ → IsGlb R₁ R₂ (grain R₁ ∪ grain R₂) := by decide

/-! ### On comparable pairs the lub and glb are the endpoints

  Which is precisely Lattice Absorption. No field-set computation is involved. -/

theorem t_comparable_lub : ∀ R₁ R₂ : Ty, grainLe R₂ R₁ → IsLub R₁ R₂ R₁ := by decide
theorem t_comparable_glb : ∀ R₁ R₂ : Ty, grainLe R₂ R₁ → IsGlb R₁ R₂ R₂ := by decide

/-! ### The one place the Lean development diverges from the paper

  `Relations/IntersectionUnion.lean` formalizes Lattice Absorption as

      sub (grain R₁) (grain R₂) → grainEq R₁ (inter R₁ R₂)

  writing the **field-set** `inter` where the paper's `∩typ` denotes the
  **lattice lub**. The premise is comparability, and on comparable pairs the two
  come apart: the lub is `R₁`, while the field-set intersection can be anything
  — including `∅`, when the comparability is witnessed by a *declared*
  determination between types that share no fields.

  So the paper's theorem is correct and the Lean statement is a
  mis-formalization of it. The counterexample below is to the Lean statement,
  not to Lattice Absorption. -/

theorem t_lean_intersection_grain_FAILS :
    ¬ (∀ R₁ R₂ : Ty, sub (grain R₁) (grain R₂) → grainEq R₁ (R₁ ∩ R₂)) := by decide

/-- `R₁ = {CustomerName}`, `R₂ = {CustomerId}`, FD `CustomerId → CustomerName`.
    The two are *comparable* (`R₂ ≤_g R₁`) via the declared determination, so
    the lub is `R₁` — but they share no field, so `R₁ ∩typ R₂ = ∅`. -/
example :
    grainLe ({0} : Ty) ({1} : Ty)
    ∧ ({1} : Ty) ∩ ({0} : Ty) = ∅
    ∧ IsLub ({1} : Ty) ({0} : Ty) ({1} : Ty)          -- the lub is R₁, as the paper says
    ∧ ¬ grainEq ({1} : Ty) (({1} : Ty) ∩ ({0} : Ty))  -- but the Lean formula is not
    := by decide

end GrainTheory.Model
