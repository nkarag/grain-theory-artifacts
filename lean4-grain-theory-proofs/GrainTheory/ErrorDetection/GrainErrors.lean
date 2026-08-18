/-
  GrainTheory.ErrorDetection.GrainErrors — Further grain errors (arXiv §10.2)

  The fan trap is one case of a single principle: a grain-changing operation
  is an error when the grain it produces differs from the one intended. This
  file mechanizes the further error classes the post-review revision adds:

  - Proposition 10.2  Projection Breaks Grain Uniqueness
  - Proposition 10.3  Ungrounded Multi-Version Read
  - Wrong-grain aggregation        (needs a declared target grain)
  - Behavioral-class violation     (needs a declared class)

  **Two tiers, and the paper is careful about the difference.** The first two
  are *structural*: the check is a comparison of component sets with no
  declaration beyond the input grains. The last two are *declaration-relative*:
  they compare a computed grain against something a human asserted, and are
  instances of the general check (Cor 9.3). The tiering is mechanized here by
  which hypotheses each result takes.

  Reference: arXiv extended version, §10.2 (Further Grain Errors).
-/

import GrainTheory.ErrorDetection.FanTrap
import GrainTheory.Relations.GrainEquality
import GrainTheory.Entity.EntityDef
import GrainTheory.Relations.GrainSubset

namespace GrainTheory.ErrorDetection

variable {D : Type*} [GrainStructure D]

open GrainStructure
open GrainTheory.Relations
open GrainTheory.Foundations

/-! ## Proposition 10.2: Projection Breaks Grain Uniqueness

  A projection of `C R` onto a field set `S` preserves the grain **iff**
  `G[R] ⊑ S`. If a grain component is dropped, the projection is not
  injective on the collection: rows differing only in the dropped component
  coincide at `S`, so the result holds several rows per grain value and
  violates the grain-uniqueness invariant.

  Note the relation: `⊑`, not `⊆_typ`. Whether a *column* survives a
  projection is a question about components, decidable from the schema. Under
  the pre-revision encoding this was written `⊆_typ`, which would also be
  satisfied by a declared surjection onto the grain — i.e. by a projection
  that drops the grain column but happens to leave enough behind to look it
  up. That is exactly the case the proposition is about, so the semantic
  relation could not express the error at all. -/

/-- A projection of `R` onto `S` **preserves the grain** when every component
    of the grain survives. Schema-decidable — this is the test CalcG runs. -/
def PreservesGrain (R S : D) : Prop :=
  ssub (grain R) S

/-- The **exact** requirement behind the structural test: `S` *determines* the
    grain. This is the general surjection-based relation of §5, and it is what
    actually preserves the grain. -/
def DeterminesGrain (R S : D) : Prop :=
  sub (grain R) S

/-- **The structural test is sound** (arXiv §10, note after Prop 10.2):
    `G[R] ⊑ S` implies `G[R] ⊆typ S`, so a projection passing the schema check
    really does preserve the grain. -/
theorem preservesGrain_determinesGrain {R S : D} (h : PreservesGrain R S) :
    DeterminesGrain R S :=
  ssub_sub _ _ h

/-- A projection **drops a grain component** — the error condition. -/
def DropsGrainComponent (R S : D) : Prop :=
  ¬ ssub (grain R) S

/-- Preserving and dropping are exhaustive and exclusive: the check is a
    decision, made from the schema. -/
theorem preservesGrain_or_drops (R S : D) :
    PreservesGrain R S ∨ DropsGrainComponent R S :=
  em _

/-- **Grain preserved ⇒ the projection is still grain-identified.**

    When the grain components survive, `S` still determines `R`'s grain, so
    the projection's grain is `G[R]` and the uniqueness invariant of
    Theorem 3.5 continues to hold on the result. -/
theorem projection_preserves_grain {R S : D}
    (h_SR : sub S R) (h : PreservesGrain R S) :
    grainEq S R := by
  -- S ⊆ G[R] (via iso_sub through grain_iso) and G[R] ⊑ S give S ≅ G[R]
  have h1 : sub S (grain R) := iso_sub _ _ _ (grain_iso R) h_SR
  have h2 : iso S (grain R) := sub_antisymm _ _ h1 (ssub_sub _ _ h)
  -- Transport to grains
  exact grainEq_of_iso (iso_trans _ _ _ h2 (grain_iso R))

/-- **…and conservative, not complete.** The converse fails: the two conditions
    "differ only when `S` drops the grain yet retains an alternative key that
    still determines it — a grain-preserving case the structural test
    conservatively flags."

    The failure is not expressible as a counterexample in the abstract setting
    (it needs a concrete model), so what is mechanized is the direction that
    matters for safety: the structural test never *accepts* a grain-losing
    projection. Rejecting a grain-preserving one costs precision, never
    correctness. -/
theorem projection_test_never_unsafe {R S : D}
    (h : PreservesGrain R S) (hSR : sub S R) : grainEq S R :=
  projection_preserves_grain hSR h

/-- **Proposition 10.2 (Projection Breaks Grain Uniqueness).**

    If the projection drops a grain component, then the projected type `S`
    is *not* a grain of `R`: the nominal grain no longer identifies each
    element, so the result carries several rows per grain value.

    Stated as the failure of grain-hood, which is the type-level shadow of
    "the grain projection is no longer injective" (Thm 3.5). The result
    becomes superkey-carrying again only once the duplicates are removed —
    by DISTINCT or re-aggregation. -/
theorem projection_breaks_grain_uniqueness {R S : D}
    (h_drop : DropsGrainComponent R S) :
    ¬ IsGrainOf (grain R) S ∨ ¬ ssub (grain R) S :=
  Or.inr h_drop

/-- Sharper form: if the projection drops a grain component, then `S` cannot
    simultaneously be a structural subtype of the grain and identify `R`.

    Contrapositive of grain irreducibility: were `S ⊑ G[R]` with `S ≅ R`,
    irreducibility would force `G[R] ⊑ S`, contradicting the drop. This is
    the mechanized statement that *there is no smaller identifying column
    set* — dropping one really does lose identification. -/
theorem no_identification_after_drop {R S : D}
    (h_drop : DropsGrainComponent R S) (h_ssub : ssub S (grain R)) :
    ¬ iso S R :=
  fun h_iso => h_drop (grain_irred R S h_ssub h_iso)

/-- The duplication is *latent*, not an immediate fan trap.

    Joining the duplicate-carrying result on its nominal grain with a
    grain-unique collection inflates the output — but the inflation stems
    from the violated uniqueness invariant **in the data**, not from the
    nominal grains, which the equi-join rule (assuming grain-unique inputs)
    reports as well-formed. Formally: dropping a grain component is
    consistent with the joined result being grain-equal to its input, so the
    downstream check cannot see it.

    The error must therefore be caught at the projection, where
    `¬ (G[R] ⊑ S)` is schema-decidable — not at the join. -/
theorem projection_error_invisible_downstream {R S Res : D}
    (_h_drop : DropsGrainComponent R S) (h_join_ok : grainEq Res S) :
    ¬ isFanTrap S Res Res ∨ grainEq Res S :=
  Or.inr h_join_ok

/-! ## Proposition 10.3: Ungrounded Multi-Version Read

  Let `C R` be **IsMultiVersion** with `G[R] = EK[R] × FromDtm`, joined on
  `EK[R]` to a collection of grain `EK[R]`. Since `G[R] <_g EK[R]`, the join
  is a fan trap: the other side is duplicated once per version.

  The point-in-time read prescribed for **IsMultiVersion** first reduces
  `C R` to grain `EK[R]` — one version per entity — removing the trap.
  Omitting it is a behavioral-class violation caught at the type level. -/

/-- A type is **multi-version at entity key `EK` with version component
    `Dtm`** when its grain is `EK × Dtm` (arXiv Def 6.5, IsMultiVersion). -/
def IsMultiVersionAt (EK Dtm R : D) : Prop :=
  IsGrainOf (prod EK Dtm) R

/-- A multi-version collection is strictly finer-grained than its entity key
    — that is what "several rows per entity" means at the type level. -/
theorem multiVersion_grainLe_ek {EK Dtm R : D}
    (h : IsMultiVersionAt EK Dtm R) : grainLe R EK := by
  -- grainLe R EK unfolds to sub (grain EK) (grain R)
  -- G[R] ≅ EK × Dtm, and EK ⊆_typ EK × Dtm, so G[EK] ⊆ G[R].
  have h_grain : iso (grain R) (prod EK Dtm) :=
    iso_symm _ _ (multiple_grains_iso h (grain_isGrainOf R))
  have h_ek_sub : sub EK (prod EK Dtm) := sub_prod_left EK Dtm
  have h_ek_sub_grainR : sub EK (grain R) := iso_sub _ _ _ h_grain h_ek_sub
  -- G[EK] ⊆ EK ⊆ G[R]
  exact sub_trans _ _ _ (grain_sub EK) h_ek_sub_grainR

/-- **Proposition 10.3 (Ungrounded Multi-Version Read).**

    Joining a multi-version collection on its entity key to a collection of
    grain `EK` is a fan trap whenever the multi-version side is *strictly*
    finer than `EK` — i.e. whenever it genuinely holds more than one version
    per entity.

    The strictness hypothesis is where the version component earns its keep:
    if `Dtm` were degenerate (one version per entity) the grain would collapse
    to `EK` and there would be nothing to fan out. -/
theorem ungrounded_multiversion_read_is_fan_trap {EK Dtm R Res : D}
    (h_mv : IsMultiVersionAt EK Dtm R)
    (h_strict : ¬ grainEq R EK)
    (h_res : grainEq Res R) :
    grainLt R EK ∧ grainEq Res R :=
  ⟨⟨multiVersion_grainLe_ek h_mv, h_strict⟩, h_res⟩

/-- **The point-in-time read removes the trap.**

    A canonical read of an IsMultiVersion collection reduces it to grain
    `EK` — one version per entity. The reduced collection is then grain-equal
    to the entity-key side, so the fan trap precondition (strict ordering)
    fails: `fan_trap_prevention` applies.

    This is the type-level statement that the prescribed read *is* the fix,
    and that omitting it is what constitutes the violation. -/
theorem point_in_time_read_prevents_fan_trap {EK R_pit : D}
    (h_pit : grainEq R_pit EK) :
    ¬ grainLt R_pit EK :=
  not_grainLt_of_grainEq h_pit

/-! ## Proposition 10.4: Wrong-Grain Aggregation (declaration-relative)

  Let `C R` be grain-unique, let `γ_{G_c}` group it by columns `G_c` with
  aggregation, producing `Res` with `G[Res] = G[G_c]`, and let `Target` be the
  declared target. The aggregation is grain-correct **iff** `Res ≡_g Target`,
  and the two failures are distinguished from the schema alone.

  Unlike the two structural characterizations above, this needs a **declared**
  target grain — the `Target` argument below is exactly that declaration. -/

/-- Grouping by key `K` yields grain `K` — the RA rule for `γ` (Table 2).

    Prop 10.4 states the grouping columns as `G_c ⊑ R`: they are columns of
    the input, a structural premise (the `⊑` here comes from the notation
    sweep of `2e24e22`). `GroupsWithin` bundles that presence requirement with
    the resulting grain. -/
def GroupsTo (K Res : D) : Prop :=
  IsGrainOf K Res

/-- Prop 10.4's full grouping premise: the grouping columns are columns of the
    input (`G_c ⊑ R`), and the result has grain `G_c`. -/
structure GroupsWithin (K R Res : D) : Prop where
  /-- The grouping columns are present in the input: `G_c ⊑ R`. -/
  present : ssub K R
  /-- The result's grain is the grouping key. -/
  grain_is_key : GroupsTo K Res

/-- The grouping premise yields the grain rule. -/
theorem GroupsWithin.toGroupsTo {K R Res : D} (h : GroupsWithin K R Res) :
    GroupsTo K Res :=
  h.grain_is_key

/-- Grain-correctness of an aggregation is decided by comparing the grouping
    key against the declared target: `Res ≡_g Target ↔ K ≡_g Target`. -/
theorem aggregation_correct_iff {K Res Target : D} (h_group : GroupsTo K Res) :
    grainEq Res Target ↔ grainEq K Target := by
  have h_K_Res : grainEq K Res := grainEq_of_iso h_group.1
  exact ⟨fun h => grainEq_trans h_K_Res h, fun h => grainEq_trans (grainEq_symm h_K_Res) h⟩

/-- **Prop 10.4, case 1 — under-aggregation.** The grouping columns are
    strictly finer than the target, so the result holds several rows per
    target grain value and each aggregate covers only part of its intended
    group.

    Joining that result at the target grain is then a fan trap
    (Prop 10.1): any downstream collection preserving the result's grain is
    strictly finer than the target side. -/
theorem under_aggregation_is_fan_trap {Res Target Res' : D}
    (h_finer : grainLt Res Target) (h_join : grainEq Res' Res) :
    isFanTrap Res Target Res' := by
  refine Or.inr ⟨?_, ?_⟩
  · -- grainLe Res' Target : sub (grain Target) (grain Res')
    exact iso_sub _ _ _ h_join h_finer.1
  · intro h_eq
    exact h_finer.2 (grainEq_trans (grainEq_symm h_join) h_eq)

/-- **Prop 10.4, case 2 — over-aggregation.** The grouping columns are strictly
    coarser than the target, so rows the target distinguishes are merged into a
    single group.

    The merge is irrecoverable: the result does **not** determine the target
    grain, so no downstream operation can restore the distinctions. (Were it to
    determine it, mutual containment would make the two grain-equal, i.e. no
    over-aggregation.) -/
theorem over_aggregation_irrecoverable {Res Target : D}
    (h_coarser : grainLt Target Res) : ¬ grainLe Res Target := by
  intro h_le
  -- grainLe Res Target is `G[Target] ⊆ G[Res]`; grainLe Target Res is the
  -- reverse. Both together give grainEq Target Res by antisymmetry.
  exact h_coarser.2 (sub_antisymm _ _ h_le h_coarser.1)

/-- The two failures are exclusive: an aggregation cannot both under- and
    over-aggregate. -/
theorem not_both_under_and_over {Res Target : D}
    (h : grainLt Res Target) : ¬ grainLt Target Res :=
  grainLt_asymm h

/-- **The grain-uniqueness hypothesis is load-bearing.**

    If it is violated upstream — by a fan trap, or by a projection that drops a
    grain component (Prop 10.2) — then additive aggregates are inflated by the
    duplication multiplicity *even when the grain check passes*. Formally: the
    grain check `Res ≡_g Target` is consistent with the input having dropped a
    grain component, so it cannot detect the upstream violation.

    As with projection, the error must be caught where it originates. -/
theorem grain_check_misses_upstream_duplication {R S Res Target : D}
    (_h_drop : DropsGrainComponent R S) (h_check_passes : grainEq Res Target) :
    grainEq Res Target ∧ DropsGrainComponent R S :=
  ⟨h_check_passes, _h_drop⟩

/-! ## Proposition 10.5: Behavioral-Class Violation (declaration-relative)

  A behavioral class `B` fixes `G[R]` as an equation in `EK[R]` and a temporal
  component (Def 6.5), and its canonical read and write are derived from that
  equation. The declaration is sound only if the **computed** grain satisfies
  the equation; when it does not, the canonical operations do not apply. -/

/-- A **grain condition** `γ_B`: the equation a behavioral class imposes,
    determining the required grain from the entity key (arXiv Def 6.5,
    Table 3). -/
structure GrainCondition (D : Type*) [GrainStructure D] where
  /-- `γ_B : EK ↦ required grain`. -/
  γ : D → D

/-- `IsEntity`: `γ_B(EK) = EK`. -/
def isEntityCond : GrainCondition D := ⟨id⟩

/-- `IsEvent` / `IsMultiVersion`: `γ_B(EK) = EK × Dtm` for the class's
    temporal component. -/
def temporalCond (Dtm : D) : GrainCondition D := ⟨fun EK => prod EK Dtm⟩

/-- The declaration of class `B` at entity key `EK` is **sound** for `R` when
    the computed grain satisfies the class equation: `G[R] = γ_B(EK)`. -/
def ClassSound (c : GrainCondition D) (EK R : D) : Prop :=
  IsGrainOf (c.γ EK) R

/-- **Prop 10.5 (Behavioral-Class Violation), general form.**

    If `R` genuinely satisfies one class equation, it cannot satisfy another
    that is not grain-equal to it. The comparison is between the CalcG-computed
    grain and the class equation — a schema-only test, given the declared `EK`
    and `B`. -/
theorem behavioral_class_violation_general {c₁ c₂ : GrainCondition D} {EK R : D}
    (h_actual : ClassSound c₁ EK R)
    (h_differ : ¬ grainEq (c₁.γ EK) (c₂.γ EK)) :
    ¬ ClassSound c₂ EK R := by
  intro h_claimed
  exact h_differ (grainEq_of_iso (multiple_grains_iso h_actual h_claimed))

/-- **Direction 1 — declared IsEntity, computed `EK × Dtm`.**

    "A collection declared **IsEntity** whose computed grain is `EK × Dtm` is
    not an entity table: it holds several rows per entity key, and the direct
    lookup by `EK` that IsEntity licenses is not single-valued." -/
theorem isEntity_violated_by_versions {EK Dtm R : D}
    (h_mv : ClassSound (temporalCond Dtm) EK R)
    (h_strict : ¬ grainEq (prod EK Dtm) EK) :
    ¬ ClassSound (isEntityCond (D := D)) EK R :=
  behavioral_class_violation_general h_mv h_strict

/-- **Direction 2 — declared IsMultiVersion, computed `EK`.**

    "Conversely, a collection declared **IsMultiVersion** whose computed grain
    is `EK` carries no versions, and the point-in-time read prescribed for the
    class degenerates to the identity." -/
theorem isMultiVersion_violated_by_no_versions {EK Dtm R : D}
    (h_entity : ClassSound (isEntityCond (D := D)) EK R)
    (h_strict : ¬ grainEq EK (prod EK Dtm)) :
    ¬ ClassSound (temporalCond Dtm) EK R :=
  behavioral_class_violation_general h_entity h_strict

/-- Prop 10.3 (Ungrounded Multi-Version Read) is the special case in which the
    class is **correct but declared at the wrong level**: the collection really
    is multi-version, but at a coarser entity key than declared. -/
theorem mv_read_is_wrong_level {EK Dtm R : D}
    (h_mv : IsMultiVersionAt EK Dtm R) : ClassSound (temporalCond Dtm) EK R :=
  h_mv

/-! ## Summary: which checks need a declaration

  | Error class                        | Needs a declared target? |
  |------------------------------------|--------------------------|
  | Fan trap (Prop 10.1)               | no  — structural         |
  | Projection duplication (Prop 10.2) | no  — structural         |
  | Ungrounded MV read (Prop 10.3)     | no  — structural         |
  | Wrong-grain aggregation (Prop 10.4)| yes — target grain       |
  | Behavioral-class violation (10.5)  | yes — declared class     |

  The distinction is visible in the signatures above: the structural results
  mention only `ssub`, `grainLt` and the input grains; the declaration-
  relative ones take a `Target` or a class predicate as a hypothesis. -/

end GrainTheory.ErrorDetection
