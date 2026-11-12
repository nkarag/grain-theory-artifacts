/-
  GrainTheory.Relations.ClosureLattice — the lattice bounds, with a closure
  operator in the abstract class

  arXiv v4 `prop:grain-lattice-products` (Lattice bounds on product types)
  takes its least upper bound in the closure lattice of the declared
  determinations: `L` is the type on `C(R₁)⁺ ∩ C(R₂)⁺`, the intersection of
  the two grains' closures. `GrainStructure` carries no closure operator, so
  `Relations/Lattice.lean` could prove the least upper bound only in the
  determination-free case, item (4), with structural hypotheses, and the
  general statement was checked by decision procedure in the finite models
  (`Model2/TheoremCheck.lean`, `t_closure_inter_is_lub`).

  This module adds the operator as a class extending `GrainStructure` with
  four axioms: the closure is extensive, monotone and idempotent, and `⊆typ`
  is `⊑` into the closure, `sub A B ↔ ssub A (cl B)`, which is how arXiv v4
  `lem:sat-closure` (Grain ordering on product types is attribute closure)
  reads the semantic relation on product types. From these four axioms the
  module proves items (1), (2), (4) and (5) of the proposition abstractly:
  the closure-based join is the least upper bound, the union of the grains is
  the greatest lower bound, the join collapses to the field-set intersection
  when closure fixes both grains, and on a comparable pair the join is the
  coarser type. Both finite models discharge the four axioms by `decide`
  (`Model/AxiomCheck.lean`, `Model2/AxiomCheck.lean`): their `sub` is defined
  as `A ⊆ cl B`, so the characterization holds by definition.

  Direction, as in `Lattice.lean`: `≤_g` is "finer ≤ coarser", so the least
  upper bound is the finest common coarsening.
-/

import GrainTheory.Relations.Lattice

namespace GrainTheory.Relations

open GrainStructure

/-- `GrainStructure` with the closure operator of the declared determinations.
    `cl A` is the set of components determined by `A`: on product types, the
    attribute closure of `A`'s components (arXiv v4 `lem:sat-closure`). -/
class ClosureStructure (D : Type*) extends GrainStructure D where
  /-- The closure of a type under the declared determinations. -/
  cl : D → D
  /-- Extensive: a type sits inside its closure. -/
  cl_extensive : ∀ A : D, ssub A (cl A)
  /-- Monotone: a larger type has a larger closure. -/
  cl_monotone : ∀ A B : D, ssub A B → ssub (cl A) (cl B)
  /-- Idempotent: closing twice adds nothing. With extensivity the two closures
      are structurally equal, hence isomorphic. -/
  cl_idempotent : ∀ A : D, ssub (cl (cl A)) (cl A)
  /-- `⊆typ` is `⊑` into the closure: `B` determines `A` exactly when every
      component of `A` lies in the closure of `B`'s components. -/
  sub_iff_ssub_cl : ∀ A B : D, sub A B ↔ ssub A (cl B)

variable {D : Type*} [ClosureStructure D]

open ClosureStructure

/-- The closure-based join: the type on the intersection of the two grains'
    closures, item (1) of arXiv v4 `prop:grain-lattice-products`. -/
def closureJoin (R₁ R₂ : D) : D := inter (cl (grain R₁)) (cl (grain R₂))

/-! ## The closure-based join is an upper bound -/

/-- `R₁ ≤_g closureJoin R₁ R₂`. -/
theorem closureJoin_ge_left (R₁ R₂ : D) : grainLe R₁ (closureJoin R₁ R₂) := by
  change sub (grain (closureJoin R₁ R₂)) (grain R₁)
  rw [sub_iff_ssub_cl]
  have h₁ : ssub (grain (closureJoin R₁ R₂)) (cl (closureJoin R₁ R₂)) :=
    (sub_iff_ssub_cl _ _).mp (grain_sub _)
  have h₂ : ssub (cl (closureJoin R₁ R₂)) (cl (cl (grain R₁))) :=
    cl_monotone _ _ (inter_ssub_left _ _)
  exact ssub_trans _ _ _ h₁ (ssub_trans _ _ _ h₂ (cl_idempotent _))

/-- `R₂ ≤_g closureJoin R₁ R₂`. -/
theorem closureJoin_ge_right (R₁ R₂ : D) : grainLe R₂ (closureJoin R₁ R₂) := by
  change sub (grain (closureJoin R₁ R₂)) (grain R₂)
  rw [sub_iff_ssub_cl]
  have h₁ : ssub (grain (closureJoin R₁ R₂)) (cl (closureJoin R₁ R₂)) :=
    (sub_iff_ssub_cl _ _).mp (grain_sub _)
  have h₂ : ssub (cl (closureJoin R₁ R₂)) (cl (cl (grain R₂))) :=
    cl_monotone _ _ (inter_ssub_right _ _)
  exact ssub_trans _ _ _ h₁ (ssub_trans _ _ _ h₂ (cl_idempotent _))

/-! ## The closure-based join is the least upper bound -/

/-- **Item (1).** Every common upper bound `Y` of `R₁, R₂` lies above the
    closure-based join. The hypotheses are the semantic `≤_g`, not the
    structural ones `Lattice.lean` needs: a `≤_g` witness may be a declared
    determination, and the closure is exactly what absorbs it. -/
theorem closureJoin_universal {R₁ R₂ Y : D}
    (h₁ : grainLe R₁ Y) (h₂ : grainLe R₂ Y) : grainLe (closureJoin R₁ R₂) Y := by
  -- h₁ : sub (grain Y) (grain R₁); h₂ : sub (grain Y) (grain R₂)
  -- goal: sub (grain Y) (grain (closureJoin R₁ R₂))
  have a : ssub (grain Y) (cl (grain R₁)) := (sub_iff_ssub_cl _ _).mp h₁
  have b : ssub (grain Y) (cl (grain R₂)) := (sub_iff_ssub_cl _ _).mp h₂
  have c : ssub (grain Y) (closureJoin R₁ R₂) := ssub_inter _ _ _ a b
  exact iso_sub _ _ _ (grain_iso (closureJoin R₁ R₂)) (ssub_sub _ _ c)

/-! ## The greatest lower bound

  Item (2) needs no closure: the union of the grains is the greatest lower
  bound with semantic hypotheses already in `Lattice.lean`
  (`grainMeet_le_left`, `grainMeet_le_right`, `grainMeet_universal`). It is
  restated here under the closure class so that the four bounds live together. -/

/-- **Item (2).** The union of the grains is the greatest lower bound. -/
theorem closureMeet_universal {R₁ R₂ X : D}
    (h₁ : grainLe X R₁) (h₂ : grainLe X R₂) : grainLe X (grainMeet R₁ R₂) :=
  grainMeet_universal h₁ h₂

/-! ## The two special cases of the proposition -/

/-- **Item (5), the comparable case.** If `R₂ ≤_g R₁` then the join is `R₁`,
    up to grain equivalence. Antisymmetry of the ordering, the axiom
    `sub_antisymm`, is what makes the bound unique. -/
theorem closureJoin_of_le {R₁ R₂ : D} (h : grainLe R₂ R₁) :
    grainEq (closureJoin R₁ R₂) R₁ :=
  grainLe_antisymm (closureJoin_universal (grainLe_refl R₁) h) (closureJoin_ge_left R₁ R₂)

/-- **Item (4), the determination-free case.** When closure fixes both grains,
    the closure-based join is the field-set intersection of the grains, the
    `grainJoin` of `Lattice.lean`. Fixing the union of the two component sets
    alone is not enough (`Model2/TheoremCheck.lean`,
    `t_union_fixed_not_enough_FAILS`); fixing each grain is what the join
    needs. -/
theorem closureJoin_of_fixed {R₁ R₂ : D}
    (h₁ : ssub (cl (grain R₁)) (grain R₁)) (h₂ : ssub (cl (grain R₂)) (grain R₂)) :
    iso (closureJoin R₁ R₂) (grainJoin R₁ R₂) := by
  apply ssub_antisymm
  · exact ssub_inter _ _ _
      (ssub_trans _ _ _ (inter_ssub_left _ _) h₁)
      (ssub_trans _ _ _ (inter_ssub_right _ _) h₂)
  · exact ssub_inter _ _ _
      (ssub_trans _ _ _ (inter_ssub_left _ _) (cl_extensive _))
      (ssub_trans _ _ _ (inter_ssub_right _ _) (cl_extensive _))

end GrainTheory.Relations
