/-
  GrainTheory.DependencyTheory.Factorization — Grain Projection as a Homomorphism

  PODS 2027, §7 "Grain Projection as a Homomorphism":
  - Definition 7.1 (Grain Lift): φ(h) = grain_{R₂} ∘ h ∘ f_{g_{R₁}}
  - Proposition 7.2 (Grain Factorization): h factors through G[R₂]
  - Theorem (Grain Homomorphism): grain_{R₂} ∘ h = φ(h) ∘ grain_{R₁}
  - Corollary (Grain Compositionality): φ(h₂ ∘ h₁) = φ(h₂) ∘ φ(h₁)

  These are element-level (function-level) statements requiring a semantic
  layer — SemanticGrainStructure — that adds a denotation function
  den : D → Type and a witness isoEquiv turning abstract iso into Equiv.

  New axioms: 2 (den, isoEquiv). Total with GrainStructure: 38.

  Key results:
  - grainLift:                φ(h) = grain_{R₂} ∘ h ∘ f_{g_{R₁}}  [Def 7.1]
  - grain_factorization:      h = f_{g_{R₂}} ∘ e                   [Prop 7.2]
  - grain_factorization_full: h = f_{g_{R₂}} ∘ φ(h) ∘ grain_{R₁}  [derived]
  - grain_homomorphism:       grain_{R₂} ∘ h = φ(h) ∘ grain_{R₁}  [Theorem]
  - grain_compositionality:   φ(h₂ ∘ h₁) = φ(h₂) ∘ φ(h₁)         [Corollary]
  - grain_lift_surj_iff:      h surj ⟺ φ(h) surj                  [Remark]
-/

import GrainTheory.Basic

universe u v

/-- Extension of GrainStructure with a semantic (denotation) layer.

    Adds 2 axioms:
    - `den : D → Type` — maps abstract type names to actual Lean types
    - `isoEquiv` — witnesses that abstract `iso` produces actual `Equiv`

    PODS justification: `iso` was always intended as "bijection exists";
    `isoEquiv` makes this computational content explicit. -/
class SemanticGrainStructure (D : Type u) extends GrainStructure D where
  /-- Denotation: maps an abstract type name to an actual Lean type -/
  den : D → Type v
  /-- Witness: abstract iso produces an actual equivalence -/
  isoEquiv : ∀ (R₁ R₂ : D), iso R₁ R₂ → den R₁ ≃ den R₂

namespace SemanticGrainStructure

variable {D : Type u} [SemanticGrainStructure.{u, v} D]

open GrainStructure (grain grain_iso)

/-! ## Core Definitions -/

/-- The grain function: G[R] ≃ R. PODS: f_{g_R} (Definition 3.1). -/
noncomputable def grainEquiv (R : D) : den (grain R) ≃ den R :=
  isoEquiv (grain R) R (grain_iso R)

/-- The grain projection: R → G[R]. PODS: grain_R = f_{g_R}⁻¹. -/
noncomputable def grainProj (R : D) : den R → den (grain R) :=
  (grainEquiv R).symm

/-! ## PODS §7, Definition 7.1: Grain Lift -/

/-- **PODS Definition 7.1 (Grain Lift):**
    φ(h) = grain_{R₂} ∘ h ∘ f_{g_{R₁}} : G[R₁] → G[R₂].
    The grain lift of h captures the essential grain-to-grain content,
    discarding all payload attributes and implementation details. -/
noncomputable def grainLift (R₁ R₂ : D) (h : den R₁ → den R₂) :
    den (grain R₁) → den (grain R₂) :=
  grainProj R₂ ∘ h ∘ (grainEquiv R₁)

/-- The factoring map: R₁ → G[R₂]. PODS: e = grain_{R₂} ∘ h. -/
noncomputable def factorE (R₁ R₂ : D) (h : den R₁ → den R₂) :
    den R₁ → den (grain R₂) :=
  grainProj R₂ ∘ h

/-! ## PODS §7, Proposition 7.2: Grain Factorization -/

/-- **PODS Proposition 7.2 (Grain Factorization):**
    For any h : R₁ → R₂, h factors through G[R₂]:
    h = f_{g_{R₂}} ∘ e where e = grain_{R₂} ∘ h.
    Follows directly from f_{g_{R₂}} being an isomorphism (Def 3.1),
    independently of the grain lift φ. -/
theorem grain_factorization (R₁ R₂ : D) (h : den R₁ → den R₂) :
    h = (grainEquiv R₂) ∘ (factorE R₁ R₂ h) := by
  funext x
  simp only [Function.comp_apply, factorE, grainProj,
    Equiv.apply_symm_apply]

/-- The factoring map decomposes via the grain lift:
    e = φ(h) ∘ grain_{R₁}. Noted after Proposition 7.2. -/
theorem grain_factorization_decomposition
    (R₁ R₂ : D) (h : den R₁ → den R₂) :
    factorE R₁ R₂ h = (grainLift R₁ R₂ h) ∘ (grainProj R₁) := by
  funext x
  simp only [Function.comp_apply, factorE, grainLift, grainProj,
    Equiv.apply_symm_apply]

/-- Full decomposition: h = f_{g_{R₂}} ∘ φ(h) ∘ grain_{R₁}.
    Derived from Proposition 7.2 and the decomposition of e. -/
theorem grain_factorization_full (R₁ R₂ : D) (h : den R₁ → den R₂) :
    h = (grainEquiv R₂) ∘ (grainLift R₁ R₂ h) ∘ (grainProj R₁) := by
  funext x
  simp only [Function.comp_apply, grainLift, grainProj,
    Equiv.apply_symm_apply]

/-! ## PODS §7, Theorem: Grain Homomorphism -/

/-- **PODS Theorem (Grain Homomorphism):**
    grain_{R₂} ∘ h = φ(h) ∘ grain_{R₁}.
    Grain projection commutes with transformation: transforming and then
    projecting to grain yields the same result as projecting to grain
    and then applying the grain lift. This is the **homomorphism
    condition** — it does not matter whether one works at the level of
    full types or at the grain level. -/
theorem grain_homomorphism (R₁ R₂ : D) (h : den R₁ → den R₂) :
    grainProj R₂ ∘ h = (grainLift R₁ R₂ h) ∘ (grainProj R₁) := by
  funext x
  simp only [Function.comp_apply, grainLift, grainProj,
    Equiv.apply_symm_apply]

/-! ## PODS §7, Remark: Surjectivity Characterization -/

/-- **PODS Remark (Connection to Grain Ordering):**
    h surjective ⟺ φ(h) surjective (grain projection and grain function
    are bijections). R₁ ≤_g R₂ precisely when the grain lift is a
    surjection. -/
theorem grain_lift_surj_iff (R₁ R₂ : D) (h : den R₁ → den R₂) :
    Function.Surjective h ↔
      Function.Surjective (grainLift R₁ R₂ h) := by
  constructor
  · intro hs y
    obtain ⟨z, hz⟩ := hs ((grainEquiv R₂) y)
    exact ⟨(grainEquiv R₁).symm z, by
      simp only [grainLift, grainProj, Function.comp_apply,
        Equiv.apply_symm_apply, hz, Equiv.symm_apply_apply]⟩
  · intro hs y
    obtain ⟨w, hw⟩ := hs ((grainEquiv R₂).symm y)
    refine ⟨(grainEquiv R₁) w, ?_⟩
    have : (grainEquiv R₂).symm (h ((grainEquiv R₁) w)) =
           (grainEquiv R₂).symm y := by
      simpa only [grainLift, grainProj, Function.comp_apply]
        using hw
    exact (grainEquiv R₂).symm.injective this

/-! ## PODS §7, Corollary: Grain Compositionality -/

/-- **PODS Corollary (Grain Compositionality):**
    φ(h₂ ∘ h₁) = φ(h₂) ∘ φ(h₁).
    The grain lift of a composed transformation equals the composition
    of the individual grain lifts. This is the algebraic homomorphism
    condition. Follows from the grain homomorphism: the intermediate
    type R₂ cancels via f_{g_{R₂}} ∘ grain_{R₂} = id. -/
theorem grain_compositionality (R₁ R₂ R₃ : D)
    (h₁ : den R₁ → den R₂) (h₂ : den R₂ → den R₃) :
    grainLift R₁ R₃ (h₂ ∘ h₁) =
      (grainLift R₂ R₃ h₂) ∘ (grainLift R₁ R₂ h₁) := by
  funext x
  simp only [Function.comp_apply, grainLift, grainProj,
    Equiv.apply_symm_apply]

end SemanticGrainStructure
