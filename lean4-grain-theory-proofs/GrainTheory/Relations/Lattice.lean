/-
  GrainTheory.Relations.Lattice — Grain lattice structure

  The grain ordering forms a lattice on grain-equivalence classes of product
  types. This module mechanizes the **determination-free case** (arXiv
  Proposition "Lattice bounds on product types", item 4):
  - Meet (GLB) = union of grains (more fields = finer = lower); its universal
    property holds with semantic (`⊆_typ`) hypotheses.
  - Join (LUB) = inter of grains (fewer fields = coarser = higher); its
    universal property holds with **structural** (`⊑`) hypotheses only. In
    general the join is the intersection of the grains' closures under the
    declared determinations, which the abstract class cannot express; see
    `Model2/TheoremCheck.lean`.

  Direction: ≤_g is "finer ≤ coarser", so lower = finer = more fields.
-/

import GrainTheory.Relations.Armstrong

namespace GrainTheory.Relations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-! ## Meet and Join definitions -/

/-- Grain meet (GLB): union of grains. The meet is the finest common coarsening.
    More fields = finer = lower in the grain ordering. -/
def grainMeet (R₁ R₂ : D) : D := union (grain R₁) (grain R₂)

/-- Grain join (LUB): intersection of grains. The join is the coarsest common refinement.
    Fewer fields = coarser = higher in the grain ordering. -/
def grainJoin (R₁ R₂ : D) : D := inter (grain R₁) (grain R₂)

/-! ## Meet is greatest lower bound -/

/-- Meet is a lower bound on the left: meet(R₁,R₂) ≤_g R₁ -/
theorem grainMeet_le_left (R₁ R₂ : D) : grainLe (grainMeet R₁ R₂) R₁ :=
  -- Goal: sub (grain R₁) (grain (union (grain R₁) (grain R₂)))
  iso_sub _ _ _ (grain_iso (union (grain R₁) (grain R₂))) (sub_union_left _ _)

/-- Meet is a lower bound on the right: meet(R₁,R₂) ≤_g R₂ -/
theorem grainMeet_le_right (R₁ R₂ : D) : grainLe (grainMeet R₁ R₂) R₂ :=
  -- Goal: sub (grain R₂) (grain (union (grain R₁) (grain R₂)))
  iso_sub _ _ _ (grain_iso (union (grain R₁) (grain R₂))) (sub_union_right _ _)

/-- Meet is the greatest lower bound: if X ≤_g R₁ and X ≤_g R₂, then X ≤_g meet(R₁,R₂) -/
theorem grainMeet_universal {R₁ R₂ X : D}
    (h₁ : grainLe X R₁) (h₂ : grainLe X R₂) : grainLe X (grainMeet R₁ R₂) := by
  -- h₁ : sub (grain R₁) (grain X), h₂ : sub (grain R₂) (grain X)
  -- Goal: sub (grain (union (grain R₁) (grain R₂))) (grain X)
  have hiso := grain_iso (union (grain R₁) (grain R₂))
  exact sub_trans _ _ _ (sub_of_iso hiso) (union_sub _ _ _ h₁ h₂)

/-! ## Join is least upper bound -/

/-- Join is an upper bound on the left: R₁ ≤_g join(R₁,R₂) -/
theorem grainJoin_ge_left (R₁ R₂ : D) : grainLe R₁ (grainJoin R₁ R₂) := by
  -- Goal: sub (grain (inter (grain R₁) (grain R₂))) (grain R₁)
  exact sub_trans _ _ _ (sub_of_iso (grain_iso (inter (grain R₁) (grain R₂))))
    (inter_sub_left _ _)

/-- Join is an upper bound on the right: R₂ ≤_g join(R₁,R₂) -/
theorem grainJoin_ge_right (R₁ R₂ : D) : grainLe R₂ (grainJoin R₁ R₂) := by
  -- Goal: sub (grain (inter (grain R₁) (grain R₂))) (grain R₂)
  exact sub_trans _ _ _ (sub_of_iso (grain_iso (inter (grain R₁) (grain R₂))))
    (inter_sub_right _ _)

/-- Join is the least upper bound — **given structural upper bounds**.

    The hypotheses are `⊑`, not `⊆_typ`. This is not a technicality: with the
    semantic hypotheses the statement is **false**, refuted in
    `Model/TheoremCheck.lean` and `Model2/TheoremCheck.lean`. A `≤_g` witness
    may be a *declared* determination rather than a structural projection
    (arXiv Def. type-subset), and the field-set `∩typ` sees only the structural
    case. This theorem is therefore the determination-free case, item (4) of
    the paper's Proposition "Lattice bounds on product types"; the general
    least upper bound is the product on the intersection of the two grains'
    **closures**, which the abstract class has no closure operator to express
    and which `Model2/TheoremCheck.lean` checks by decision procedure.

    Grain-incomparability of `R₁, R₂` does **not** suffice as a hypothesis:
    two incomparable grains sharing no field can both determine a third
    (`Model2/TheoremCheck.lean`, `t_incomp_inter_is_lub_FAILS`). -/
theorem grainJoin_universal {R₁ R₂ X : D}
    (h₁ : ssub (grain X) (grain R₁)) (h₂ : ssub (grain X) (grain R₂)) :
    grainLe (grainJoin R₁ R₂) X :=
  -- Goal: sub (grain X) (grain (inter (grain R₁) (grain R₂)))
  iso_sub _ _ _ (grain_iso (inter (grain R₁) (grain R₂)))
    (ssub_sub _ _ (ssub_inter _ _ _ h₁ h₂))

end GrainTheory.Relations
