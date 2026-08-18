/-
  GrainTheory.Entity.EntityDef — Entity and Entity Key definitions

  PODS §5, Definitions 7–8 and Theorem 5.3 (EK–Grain Hierarchy).

  An *entity* of a data type R is a type E together with a surjective
  projection entity : R → E that extracts the "subject of information".
  In the abstract axiomatization, the surjection gives E ⊆_typ R
  (Definition 2.1), which is the structural content captured here.

  The *entity key* is EK(R) ≡ G[E] — the grain of the entity type.

  Theorem 5.3 (EK–Grain Hierarchy) derives EK(R) ⊆_typ G[R] from
  the definitions — it is not assumed.  The proof constructs a surjection
  g_{ek} : G[R] ↠ G[E] = f_{g_E}⁻¹ ∘ entity ∘ f_{g_R}, mirroring the
  PODS appendix proof.
-/

import GrainTheory.Foundations.GrainDef
import GrainTheory.Relations.GrainSubset

namespace GrainTheory.Entity

variable {D : Type*} [GrainStructure D]

open GrainStructure
open GrainTheory.Foundations
open GrainTheory.Relations

/-! ## Definition 6.1: Entity (arXiv §6)

  Given a data type R, an *entity* of R is a type E such that there
  exists a surjective function entity : R ↠ E returning, for each element,
  the *subject of the information* it conveys. By Definition 2.1 (type-level
  subset), a surjection R ↠ E is exactly E ⊆_typ R.

  In the abstract axiomatization, we capture this as `sub E R`.

  **The uniqueness clause, corrected.** The pre-revision definition said
  "for a given grain G[R], the entity is unique" — which reviewer R2 correctly
  rejected, since E is *declared* by domain analysis and is not determined by
  R's structure at all, let alone by its grain. The revised definition
  withdraws that clause and states the position precisely:

  * the **entity** is unique because it is *declared* — a data type has a
    single subject of information, fixed by the declaration, with no
    alternatives;
  * the **entity key** `EK[R] = G[E]` is unique only *up to isomorphism*,
    being a grain (Theorem 3.4, Multiple Grains).

  The encoding below reflects this: `IsEntityOf` is a relation that a
  declaration witnesses, and nothing in the development derives E from R.
  Grain and entity answer different questions — *at what level of detail* is
  each element recorded, versus *who or what* it is about — and the two are
  orthogonal: a current-state customer table (grain `CustomerId`) and an SCD2
  customer dimension (grain `CustomerId × EffectiveFrom`) differ in grain yet
  share the entity `Customer`.

  See `GrainTheory.Entity.EntityPreservation` for the `=_ek` collection
  relation this orthogonality makes available.
-/

/-- Uniqueness, correctly located: what is unique *up to isomorphism* is the
    entity **key**, not the entity. Any two entity keys of the same declared
    entity are isomorphic, because both are grains of E.

    There is deliberately no companion theorem deriving E from R — that is the
    clause the revision withdraws. -/
theorem entityKey_unique_up_to_iso {E EK₁ EK₂ : D}
    (h₁ : IsGrainOf EK₁ E) (h₂ : IsGrainOf EK₂ E) : iso EK₁ EK₂ :=
  multiple_grains_iso h₁ h₂

/-- `IsEntityOf E R` holds when E serves as the entity type for R.

  Structurally: E ⊆_typ R — there exists a surjection R ↠ E
  (Definition 2.1), which is the type-level encoding of the entity
  projection entity : R → E.

  The key consequence — EK(R) = G[E] ⊆_typ G[R] — is *derived* as
  Theorem 5.3 (EK–Grain Hierarchy), not assumed. -/
def IsEntityOf (E R : D) : Prop :=
  sub E R

/-! ## Theorem 5.3: EK–Grain Hierarchy (PODS §5)

  If E is an entity of R (i.e., E ⊆_typ R), then G[E] ⊆_typ G[R].

  Proof (mirroring the PODS appendix):
  1. entity ∘ f_{g_R} : G[R] → E is a surjection
     (bijection f_g composed with surjection entity)
  2. f_{g_E}⁻¹ : E → G[E] is a bijection
  3. g_{ek} = f_{g_E}⁻¹ ∘ entity ∘ f_{g_R} : G[R] ↠ G[E] is a surjection

  In the abstract axiomatization, the surjection chain is captured by:
  - grain_determines_subsets : sub E R → sub (grain E) (grain (grain R))
  - Idempotency: iso (grain (grain R)) (grain R)
  - Transitivity through the idempotent grain
-/

/-- **PODS Theorem 5.3 (EK–Grain Hierarchy):**
    If E is an entity of R (E ⊆_typ R), then G[E] ⊆_typ G[R].

    The entity key is always a type-level subset of the grain.
    This is *derived* from the entity and grain definitions, not assumed. -/
theorem IsEntityOf.ek_sub_grain {E R : D} (h : IsEntityOf E R) :
    sub (grain E) (grain R) := by
  -- Step 1: sub E R → sub (grain E) (grain (grain R))
  --         (grain_determines_subsets: if A ⊆ B then G[A] ⊆ G[G[B]])
  have h_det : sub (grain E) (grain (grain R)) :=
    grain_determines_subsets h
  -- Step 2: iso (grain (grain R)) (grain R) → sub (grain (grain R)) (grain R)
  --         (idempotency turned into a subset via iso_sub)
  have h_idem : sub (grain (grain R)) (grain R) :=
    iso_sub _ _ _ (iso_symm _ _ (Foundations.grain_idempotent R)) (sub_refl _)
  -- Step 3: transitivity
  exact sub_trans _ _ _ h_det h_idem

/-! ## Definition 8: Entity Key (PODS §5)

  The entity key of R is EK(R) ≡ G[E], the grain of the entity type.
  The entity key is always a type-level subset of the grain:
  EK(R) ⊆_typ G[R] (Theorem 5.3).

  In the abstract axiomatization, EK(R) is simply `grain E` where
  E is the entity of R.
-/

/-- `EntityKey EK E R` holds when EK is the entity key of R via entity E.

  This packages the full PODS Definition 8:
  - E is the entity of R (IsEntityOf E R)
  - EK is the grain of the entity type E (IsGrainOf EK E)

  The hierarchy EK ⊆_typ G[R] is derivable from these two conditions
  (Theorem 5.3 + transitivity through grain E). -/
structure EntityKey (EK E R : D) : Prop where
  /-- E is the entity of R -/
  entity : IsEntityOf E R
  /-- EK is the grain of the entity type E -/
  ek_grain : IsGrainOf EK E

/-- The entity key EK ⊆_typ G[R]: derived from entity + ek_grain.

    Proof: EK ≅ E (from IsGrainOf) → sub EK (grain E) (via iso_sub) →
    sub (grain E) (grain R) (Theorem 5.3) → sub EK (grain R) (transitivity). -/
theorem EntityKey.ek_sub_grain {EK E R : D} (h : EntityKey EK E R) :
    sub EK (grain R) := by
  -- EK ≅ E from IsGrainOf
  have h_iso : iso EK E := h.ek_grain.toIso
  -- EK ⊆ E from iso (via iso_sub: iso E EK → sub EK EK → sub EK E)
  have h_ek_sub_E : sub EK E :=
    iso_sub _ _ _ (iso_symm _ _ h_iso) (sub_refl _)
  -- E ⊆ R from entity definition
  have h_E_sub_R : sub E R := h.entity
  -- EK ⊆ R by transitivity
  have h_ek_sub_R : sub EK R := sub_trans _ _ _ h_ek_sub_E h_E_sub_R
  -- G[EK] ⊆ G[G[R]] from grain_determines_subsets
  have h_det : sub (grain EK) (grain (grain R)) :=
    grain_determines_subsets h_ek_sub_R
  -- iso EK E gives iso (grain EK) (grain E) ... hmm, not directly.
  -- Instead: EK ⊆ grain R, derived from EK ⊆ E ⊆ R and grain properties.
  -- Simpler path: sub (grain E) (grain R) from Thm 5.3, then relate EK to grain E.
  have h_grainE_sub_grainR : sub (grain E) (grain R) :=
    h.entity.ek_sub_grain
  -- From iso EK E: iso EK (grain E) by transitivity through E
  have h_iso_grainE : iso EK (grain E) :=
    iso_trans _ _ _ h_iso (iso_symm _ _ (grain_iso E))
  -- From iso EK (grain E): sub EK (grain E)
  have h_ek_sub_grainE : sub EK (grain E) :=
    iso_sub _ _ _ (iso_symm _ _ h_iso_grainE) (sub_refl _)
  -- Transitivity: EK ⊆ grain E ⊆ grain R
  exact sub_trans _ _ _ h_ek_sub_grainE h_grainE_sub_grainR

/-! ## Derived Entity Key

  When the entity E is known, the entity key is uniquely determined
  as G[E] — the canonical grain of E. -/

/-- The canonical entity key of R via entity E is G[E]. -/
def entityKeyOf (E : D) : D := grain E

/-- The canonical entity key satisfies IsGrainOf. -/
theorem entityKeyOf_isGrainOf (E : D) : IsGrainOf (entityKeyOf E) E :=
  grain_isGrainOf E

/-! ## Basic Properties -/

/-- If E is an entity of R, then E ⊆_typ R (definition unfolding). -/
theorem IsEntityOf.entity_sub {E R : D} (h : IsEntityOf E R) :
    sub E R :=
  h

/-- G[R] ⊆_typ R: the grain is a subset of R (from GrainStructure axioms). -/
theorem grain_sub_type (R : D) : sub (grain R) R :=
  grain_sub R

/-- EK–Grain–Type Hierarchy (PODS Theorem 5.3):
    If E is an entity of R, then G[E] ⊆_typ G[R] ⊆_typ R.

    This combines:
    - G[E] ⊆_typ G[R] (Theorem 5.3, derived)
    - G[R] ⊆_typ R (from grain_sub axiom)
    So by transitivity: G[E] ⊆_typ R. -/
theorem ek_grain_type_hierarchy {E R : D} (h : IsEntityOf E R) :
    sub (grain E) (grain R) ∧ sub (grain R) R :=
  ⟨h.ek_sub_grain, grain_sub R⟩

/-- EK ⊆_typ R: the entity key is a subset of R (by transitivity through G[R]). -/
theorem ek_sub_type {E R : D} (h : IsEntityOf E R) :
    sub (grain E) R :=
  sub_trans _ _ _ h.ek_sub_grain (grain_sub R)

/-! ## EntityKey constructor from IsEntityOf -/

/-- Given IsEntityOf E R, construct the canonical EntityKey using G[E]. -/
theorem EntityKey.canonical {E R : D} (h : IsEntityOf E R) :
    EntityKey (grain E) E R :=
  { entity := h
    ek_grain := grain_isGrainOf E }

/-! ## Grain ordering and entity -/

/-- If E is an entity of R, then R ≤_g E (R has finer grain than E).
    This follows because G[E] ⊆_typ G[R] (Theorem 5.3),
    which is exactly the definition of R ≤_g E (grainLe R E). -/
theorem entity_grainLe {E R : D} (h : IsEntityOf E R) :
    sub (grain E) (grain R) :=
  h.ek_sub_grain

/-! ## Entity key uniqueness (up to grain equivalence)

  If E₁ and E₂ are both entities of R, their entity keys G[E₁] and G[E₂]
  may differ — entity uniqueness up to iso is a semantic property not
  captured in the abstract axiomatization. However, we can state that
  both entity keys sit inside G[R]. -/

/-- Both entity keys of R (from possibly different entities) sit inside G[R]. -/
theorem both_ek_sub_grain {E₁ E₂ R : D}
    (h₁ : IsEntityOf E₁ R) (h₂ : IsEntityOf E₂ R) :
    sub (grain E₁) (grain R) ∧ sub (grain E₂) (grain R) :=
  ⟨h₁.ek_sub_grain, h₂.ek_sub_grain⟩

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
