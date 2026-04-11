/-
  GrainTheory.Entity.EKHierarchy — EK-Grain-Type Hierarchy

  PODS §5, Theorem (EK–Grain–Type Hierarchy):
    For any data type R with entity E, EK(R) ⊆_typ G[R] ⊆_typ R.

  The core hierarchy theorem is proved in EntityDef.lean. This module
  provides the focused interface and additional hierarchy-related results,
  including the data integration remark from the PODS paper.
-/

import GrainTheory.Entity.EntityDef
import GrainTheory.Relations.GrainOrdering

namespace GrainTheory.Entity

variable {D : Type*} [GrainStructure D]

open GrainStructure
open GrainTheory.Foundations
open GrainTheory.Relations

/-! ## EK–Grain–Type Hierarchy (PODS Theorem)

  The hierarchy EK(R) ⊆_typ G[R] ⊆_typ R is proved in EntityDef.lean.
  We re-export the key results here for a focused interface.

  Main theorem: `ek_grain_type_hierarchy`
  - Left conjunct:  G[E] ⊆_typ G[R]  (entity key ⊆ grain)
  - Right conjunct: G[R] ⊆_typ R     (grain ⊆ type)

  Transitivity: `ek_sub_type`
  - G[E] ⊆_typ R  (entity key ⊆ type)
-/

-- The following are re-exported from EntityDef.lean:
-- ek_grain_type_hierarchy, ek_sub_grain, grain_sub_type, ek_sub_type

/-! ## Hierarchy as Chain of Grain Orderings

  The hierarchy can also be expressed in terms of ≤_g (grain ordering).
  If E is an entity of R, then:
  - R ≤_g E  (R has finer grain than E, since G[E] ⊆_typ G[R])
  - This means data about R can always be aggregated to the entity level.
-/

/-- If E is an entity of R, then R ≤_g E: R has finer grain than its entity.
    This is the grain-ordering reading of EK(R) ⊆_typ G[R]. -/
theorem entity_implies_grainLe {E R : D} (h : IsEntityOf E R) :
    grainLe R E :=
  h

/-! ## Data Integration at the Entity Level (PODS Remark)

  When two data types R₁ and R₂ share the same entity E, both have
  grains that sit above the entity key in the grain ordering:
    R₁ ≤_g E  and  R₂ ≤_g E.

  This means their grains converge on the shared entity key, enabling
  integration at the entity level even when the grains of R₁ and R₂
  are incomparable (the typical fan-trap scenario).
-/

/-- Data integration: if R₁ and R₂ share entity E, both R₁ ≤_g E and R₂ ≤_g E.
    Their grains converge on the shared entity key G[E].
    PODS Remark: enables integration even when G[R₁] and G[R₂] are incomparable. -/
theorem shared_entity_grainLe {E R₁ R₂ : D}
    (h₁ : IsEntityOf E R₁) (h₂ : IsEntityOf E R₂) :
    grainLe R₁ E ∧ grainLe R₂ E :=
  ⟨h₁, h₂⟩

/-- Data integration (subset form): if R₁ and R₂ share entity E, both
    entity keys sit inside both grains: G[E] ⊆_typ G[R₁] and G[E] ⊆_typ G[R₂]. -/
theorem shared_entity_ek_sub {E R₁ R₂ : D}
    (h₁ : IsEntityOf E R₁) (h₂ : IsEntityOf E R₂) :
    sub (grain E) (grain R₁) ∧ sub (grain E) (grain R₂) :=
  ⟨h₁, h₂⟩

/-! ## Hierarchy Strengthening: EntityKey Bundle

  When we have the full EntityKey bundle, the hierarchy is available
  directly without going through IsEntityOf.
-/

/-- From an EntityKey bundle, extract the full hierarchy chain. -/
theorem EntityKey.hierarchy {EK E R : D} (h : EntityKey EK E R) :
    sub EK (grain R) ∧ sub (grain R) R :=
  ⟨h.ek_sub_grain, grain_sub R⟩

/-- From an EntityKey bundle, the entity key is a subset of R. -/
theorem EntityKey.ek_sub_type {EK E R : D} (h : EntityKey EK E R) :
    sub EK R :=
  sub_trans _ _ _ h.ek_sub_grain (grain_sub R)

/-! ## Behavioral Class and the Hierarchy

  The behavioral class (IsEntity, IsEvent, IsMultiVersion) is determined
  by the *structure* of G[R] relative to EK(R) = G[E]:
  - IsEntity:  G[R] ≅ G[E]  — the grain equals the entity key
  - In this case, the hierarchy collapses: EK(R) ≅ G[R] ⊆_typ R

  The IsEntityClass predicate is defined in EntityDef.lean. We add
  the hierarchy collapse theorem here.
-/

/-- When R has IsEntity class, the hierarchy collapses: EK(R) ≅ G[R].
    The three-level chain EK ⊆ G[R] ⊆ R becomes a two-level chain
    with the first inclusion being an isomorphism. -/
theorem IsEntityClass.hierarchy_collapse {E R : D} (h : IsEntityClass E R) :
    iso (grain E) (grain R) ∧ sub (grain R) R :=
  ⟨iso_symm _ _ h.2, grain_sub R⟩

end GrainTheory.Entity
