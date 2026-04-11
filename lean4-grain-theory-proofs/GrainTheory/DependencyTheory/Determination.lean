/-
  GrainTheory.DependencyTheory.Determination — Determination problem (LP-26)

  PODS 2027, §7, Proposition (Determination):

    For any function h : R₁ → R₂, h factors through G[R₂]:
    there exists e : R₁ → G[R₂] such that h = f_{g_{R₂}} ∘ e,
    where f_{g_{R₂}} : G[R₂] →≅ R₂.

  In our abstract axiomatization (where functions between types are not
  explicit), this is encoded as type-level factorization results:

  1. **Target-grain factorization**: sub R₁ R₂ → sub R₁ (grain R₂)
     Any type-subset relationship factors through the target's grain.

  2. **Grain-level bottleneck**: grainLe R₁ R₂ → grainLe (grain R₁) (grain R₂)
     Grain ordering factors through the grains (= grainLe_preservation).

  3. **Determination square**: If grainLe R₁ R₂, the commutative square
     holds: sub (grain R₂) (grain R₁), iso (grain R₁) R₁, iso (grain R₂) R₂.

  4. **Full factorization via iso**: iso R₁ R₂ → iso R₁ (grain R₂)
     Any isomorphism factors through the target's grain
     (= Foundations.factorization, restated).

  The grain is the universal bottleneck through which all inter-type
  relationships pass — the type-level counterpart of the PODS paper's
  determination proposition for element-level functions.
-/

import GrainTheory.Relations.GrainOrdering
import GrainTheory.Foundations.GrainDef
import GrainTheory.Foundations.Factorization
import GrainTheory.Foundations.Idempotency

namespace GrainTheory.DependencyTheory

variable {D : Type*} [GrainStructure D]

open GrainStructure
open GrainTheory.Relations (grainLe grainEq grainLe_preservation grainLe_refl)
open GrainTheory.Foundations (IsGrainOf grain_isGrainOf grain_idempotent)

/-! ## Target-Grain Factorization -/

/-- PODS Determination (type-level encoding, sub case):
    If R₁ ⊆_typ R₂, then R₁ ⊆_typ G[R₂].

    Any type-subset relationship with R₂ factors through the grain of R₂.
    This is the type-level analog of "h : R₁ → R₂ factors through G[R₂]."

    Proof: G[R₂] ≅ R₂ (grain_iso), so iso_sub gives sub R₁ G[R₂]. -/
theorem determination_sub {R₁ R₂ : D} (h : sub R₁ R₂) : sub R₁ (grain R₂) :=
  iso_sub _ _ _ (grain_iso R₂) h

/-- PODS Determination (type-level encoding, iso case):
    If R₁ ≅ R₂, then R₁ ≅ G[R₂].

    Any isomorphism with R₂ factors through the grain of R₂.
    (Restates Foundations.factorization in the DependencyTheory namespace.) -/
theorem determination_iso {R₁ R₂ : D} (h : iso R₁ R₂) : iso R₁ (grain R₂) :=
  Foundations.factorization R₁ R₂ h

/-! ## Determination Square (Commutative Diagram)

    PODS Figure 7: The determination square.

    Given R₁ ≤_g R₂ (grain ordering), the following commutative square holds:

        R₁  ←≅→  G[R₁]
        ↓          ↓
        R₂  ←≅→  G[R₂]

    where:
    - horizontal arrows are grain isomorphisms (grain_iso)
    - vertical left arrow represents the "function" h : R₁ → R₂
    - vertical right arrow represents the grain-level map G[R₁] → G[R₂]
    - the square commutes: the grain-level map determines the type-level map

    In our encoding, the square is witnessed by:
    - sub (grain R₂) (grain R₁)  (= grainLe R₁ R₂, the vertical connection)
    - iso (grain R₁) R₁           (horizontal, from grain_iso)
    - iso (grain R₂) R₂           (horizontal, from grain_iso)
-/

/-- The determination square: given grainLe R₁ R₂, we package the
    commutative diagram as a conjunction of three facts. -/
theorem determination_square {R₁ R₂ : D} (h : grainLe R₁ R₂) :
    sub (grain R₂) (grain R₁) ∧ iso (grain R₁) R₁ ∧ iso (grain R₂) R₂ :=
  ⟨h, grain_iso R₁, grain_iso R₂⟩

/-! ## Grain as Universal Bottleneck -/

/-- The grain is the universal bottleneck: for any type R, the
    canonical grain G[R] satisfies IsGrainOf G[R] R.

    This means G[R] is isomorphic to R and irreducible — no proper
    subset of G[R] is isomorphic to R. All inter-type relationships
    with R must pass through this bottleneck.

    (Restated from Foundations.grain_isGrainOf for the DependencyTheory context.) -/
theorem grain_universal_bottleneck (R : D) : IsGrainOf (grain R) R :=
  grain_isGrainOf R

/-! ## Factorization Through Both Grains -/

/-- If R₁ ≤_g R₂, the grain ordering lifts to the grain level:
    G[R₁] ≤_g G[R₂]. Combined with the grain isomorphisms, this
    shows the full determination: the inter-type relationship
    R₁ ↔ R₂ factors entirely through the grains G[R₁] and G[R₂].

    (Restated from Relations.grainLe_preservation for context.) -/
theorem determination_lifts_to_grains (R₁ R₂ : D) :
    grainLe R₁ R₂ ↔ grainLe (grain R₁) (grain R₂) :=
  grainLe_preservation R₁ R₂

/-- Grain ordering is preserved when replacing a type by its grain
    on the left: R₁ ≤_g R₂ → G[R₁] ≤_g R₂.

    Proof: G[G[R₂]] ⊆ G[R₂] ⊆ G[R₁] ≅ G[G[R₁]].
    More directly: grainLe_preservation gives grainLe (grain R₁) (grain R₂),
    but we can also show grainLe (grain R₁) R₂ from the definition. -/
theorem determination_grain_left {R₁ R₂ : D} (h : grainLe R₁ R₂) :
    grainLe (grain R₁) R₂ := by
  -- h : sub (grain R₂) (grain R₁)
  -- Goal: sub (grain R₂) (grain (grain R₁))
  -- Step 1: grain R₂ ⊆ grain R₁ (from h)
  -- Step 2: grain R₁ ≅ grain(grain R₁) (from idempotency, symm)
  -- Step 3: iso_sub gives grain R₂ ⊆ grain(grain R₁)
  exact iso_sub _ _ _ (grain_idempotent R₁) h

/-- Grain ordering is preserved when replacing a type by its grain
    on the right: R₁ ≤_g R₂ → R₁ ≤_g G[R₂].

    Proof: G[G[R₂]] ⊆ G[R₂] ⊆ G[R₁].
    The first step uses grain_sub, the second uses h. -/
theorem determination_grain_right {R₁ R₂ : D} (h : grainLe R₁ R₂) :
    grainLe R₁ (grain R₂) := by
  -- h : sub (grain R₂) (grain R₁)
  -- Goal: sub (grain (grain R₂)) (grain R₁)
  -- Step: grain(grain R₂) ⊆ grain R₂ ⊆ grain R₁
  exact sub_trans _ _ _ (grain_sub (grain R₂)) h

/-- Self-determination: every type determines itself through its grain.
    R ≤_g R, and G[R] is the bottleneck.

    This is A1 (self-determination) from the Armstrong axioms, restated
    in the determination context. -/
theorem self_determination (R : D) : grainLe R R :=
  grainLe_refl R

end GrainTheory.DependencyTheory
