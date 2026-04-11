/-
  GrainTheory.Entity.EntityDef — Entity and Entity Key definitions

  PODS §5, Definitions 7–8 and Theorem (EK–Grain–Type Hierarchy).

  An *entity* of a data type R is a type E together with a surjective
  projection entity : R → E that extracts the "subject of information".
  The *entity key* is EK(R) ≡ G[E] — the grain of the entity type.
  The defining requirement is EK ⊆_typ G[R]: the entity key is always
  a type-level subset of the grain.

  In the abstract axiomatization, we model entity structure as a
  bundled record: given R, an EntityStructure packages the entity type E,
  its entity key G[E], and the structural relationships between them.
-/

import GrainTheory.Foundations.GrainDef

namespace GrainTheory.Entity

variable {D : Type*} [GrainStructure D]

open GrainStructure
open GrainTheory.Foundations

/-! ## Definition 7: Entity (PODS §5)

  Given a data type R, an *entity* of R is a type E such that there
  exists a surjective function entity : R → E extracting the subject of
  information. E is unique up to isomorphism.

  In the abstract axiomatization, we model this as: E is a data type
  that is a "coarsening" of R — specifically, G[R] ⊆_typ E ⊆_typ R
  is NOT required; instead, the entity is an independent type related
  to R through the entity key.

  Since the abstract axiomatization does not have element-level
  functions (only type-level relations), we capture entity structure
  through the type-level relationships:
  - E is a data type
  - G[E] ⊆_typ G[R] (the entity key is a subset of the grain)
  These are the structurally relevant properties for grain theory.
-/

/-- `IsEntityOf E R` holds when E serves as the entity type for R.

  In the abstract axiomatization, we require:
  1. The entity key G[E] is a type-level subset of the grain G[R].

  This captures the PODS paper's structural requirement (Definition 8):
  EK(R) = G[E] and EK(R) ⊆_typ G[R].

  The semantic aspect ("subject of information") is not expressible in
  the abstract type-level setting, but the structural consequence —
  that the entity key sits inside the grain — is the property used in
  all grain-theoretic reasoning. -/
def IsEntityOf (E R : D) : Prop :=
  sub (grain E) (grain R)

/-! ## Definition 8: Entity Key (PODS §5)

  The entity key of R is EK(R) ≡ G[E], the grain of the entity type.
  The entity key is always a type-level subset of the grain:
  EK(R) ⊆_typ G[R].

  In the abstract axiomatization, EK(R) is simply `grain E` where
  E is the entity of R.
-/

/-- `EntityKey EK E R` holds when EK is the entity key of R via entity E.

  This packages the full PODS Definition 8:
  - E is the entity of R (IsEntityOf E R)
  - EK is the grain of E (IsGrainOf EK E)
  - EK ⊆_typ G[R] (entity key sits inside the grain)

  The third condition follows from the first two plus grain_sub,
  but we state it explicitly for clarity and downstream use. -/
structure EntityKey (EK E R : D) : Prop where
  /-- E is the entity of R -/
  entity : IsEntityOf E R
  /-- EK is the grain of the entity type E -/
  ek_grain : IsGrainOf EK E
  /-- EK ⊆_typ G[R]: the entity key sits inside the grain -/
  ek_sub_grain : sub EK (grain R)

/-! ## Derived Entity Key

  When the entity E is known, the entity key is uniquely determined
  as G[E] — the canonical grain of E. -/

/-- The canonical entity key of R via entity E is G[E]. -/
def entityKeyOf (E : D) : D := grain E

/-- The canonical entity key satisfies IsGrainOf. -/
theorem entityKeyOf_isGrainOf (E : D) : IsGrainOf (entityKeyOf E) E :=
  grain_isGrainOf E

/-! ## Basic Properties -/

/-- If E is an entity of R, then G[E] ⊆_typ G[R] (definition unfolding). -/
theorem IsEntityOf.grain_sub {E R : D} (h : IsEntityOf E R) :
    sub (grain E) (grain R) :=
  h

/-- If E is an entity of R, then EK(R) = G[E] ⊆_typ G[R] ⊆_typ R.
    This is the first part of the EK–Grain–Type hierarchy. -/
theorem ek_sub_grain {E R : D} (h : IsEntityOf E R) :
    sub (grain E) (grain R) :=
  h

/-- G[R] ⊆_typ R: the grain is a subset of R (from GrainStructure axioms). -/
theorem grain_sub_type (R : D) : sub (grain R) R :=
  grain_sub R

/-- EK–Grain–Type Hierarchy (PODS Theorem):
    If E is an entity of R, then G[E] ⊆_typ G[R] ⊆_typ R.

    This combines:
    - G[E] ⊆_typ G[R] (from IsEntityOf)
    - G[R] ⊆_typ R (from grain_sub axiom)
    So by transitivity: G[E] ⊆_typ R. -/
theorem ek_grain_type_hierarchy {E R : D} (h : IsEntityOf E R) :
    sub (grain E) (grain R) ∧ sub (grain R) R :=
  ⟨h, grain_sub R⟩

/-- EK ⊆_typ R: the entity key is a subset of R (by transitivity through G[R]). -/
theorem ek_sub_type {E R : D} (h : IsEntityOf E R) :
    sub (grain E) R :=
  sub_trans _ _ _ h (grain_sub R)

/-! ## EntityKey constructor from IsEntityOf -/

/-- Given IsEntityOf E R, construct the canonical EntityKey using G[E]. -/
theorem EntityKey.canonical {E R : D} (h : IsEntityOf E R) :
    EntityKey (grain E) E R :=
  { entity := h
    ek_grain := grain_isGrainOf E
    ek_sub_grain := h }

/-! ## Grain ordering and entity -/

/-- If E is an entity of R, then R ≤_g E (R has lower/finer grain than E).
    This follows because IsEntityOf E R means G[E] ⊆_typ G[R],
    which is exactly the definition of R ≤_g E (grainLe R E). -/
theorem entity_grainLe {E R : D} (h : IsEntityOf E R) :
    sub (grain E) (grain R) :=
  h

/-! ## Entity key uniqueness (up to grain equivalence)

  If E₁ and E₂ are both entities of R, their entity keys G[E₁] and G[E₂]
  may differ — entity uniqueness up to iso is a semantic property not
  captured in the abstract axiomatization. However, we can state that
  both entity keys sit inside G[R]. -/

/-- Both entity keys of R (from possibly different entities) sit inside G[R]. -/
theorem both_ek_sub_grain {E₁ E₂ R : D}
    (h₁ : IsEntityOf E₁ R) (h₂ : IsEntityOf E₂ R) :
    sub (grain E₁) (grain R) ∧ sub (grain E₂) (grain R) :=
  ⟨h₁, h₂⟩

/-! ## Behavioral class structure

  The PODS paper defines behavioral classes based on the relationship
  between G[R] and EK(R):
  - IsEntity:       G[R] ≡_g EK(R)  (grain equals entity key)
  - IsEvent:        G[R] = EK(R) × EventDtm
  - IsMultiVersion: G[R] = EK(R) × EffectiveFrom

  These are defined here as predicates for future use (LP-20+). -/

/-- IsEntity behavioral class: G[R] ≅ G[E] — the grain equals the entity key.
    One record per entity instance. -/
def IsEntityClass (E R : D) : Prop :=
  IsEntityOf E R ∧ iso (grain R) (grain E)

/-- When R has IsEntity class, the grain IS the entity key (up to iso). -/
theorem IsEntityClass.grain_iso_ek {E R : D} (h : IsEntityClass E R) :
    iso (grain R) (grain E) :=
  h.2

/-- When R has IsEntity class, G[E] ≅ G[R] (symmetric direction). -/
theorem IsEntityClass.ek_iso_grain {E R : D} (h : IsEntityClass E R) :
    iso (grain E) (grain R) :=
  iso_symm _ _ h.2

end GrainTheory.Entity
