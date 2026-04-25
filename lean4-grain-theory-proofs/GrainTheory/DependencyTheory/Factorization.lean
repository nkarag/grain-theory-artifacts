/-
  GrainTheory.DependencyTheory.Factorization — Grain Homomorphism

  PODS 2027, §7 "Grain Projection as a Homomorphism":
  - Theorem 7.1 (Grain Homomorphism):
      (i)  Factorization — h factors through G[R₂]
      (ii) Commutativity — the grain factorization square commutes,
           establishing grain projection as a homomorphism
  - Corollary 7.2 (Grain Compositionality):
      Grain-level factors compose; follows from commutativity via
      id cancellation of the intermediate type.

  These are element-level (function-level) statements requiring a semantic
  layer — SemanticGrainStructure — that adds a denotation function
  den : D → Type and a witness isoEquiv turning abstract iso into Equiv.

  New axioms: 2 (den, isoEquiv). Total with GrainStructure: 38.

  Key results:
  - grain_homomorphism_i: h = f_{g_{R₂}} ∘ e            [Thm 7.1(i)]
  - grain_factorization_square: e = f_{G₁G₂} ∘ grain_{R₁} [lemma]
  - grain_homomorphism_ii: h = f_{g_{R₂}} ∘ f_{G₁G₂} ∘ grain_{R₁} [Thm 7.1(ii)]
  - grain_compositionality: f_{G₁G₃} = f_{G₂G₃} ∘ f_{G₁G₂}       [Cor 7.2]
  - grain_factor_surj_iff: h surjective ⟺ f_{G₁G₂} surjective    [Remark]
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

/-! ## Core Definitions (PODS §7 notation) -/

/-- The grain isomorphism: G[R] ≃ R. PODS: f_{g_R}. -/
noncomputable def grainEquiv (R : D) : den (grain R) ≃ den R :=
  isoEquiv (grain R) R (grain_iso R)

/-- The grain projection: R → G[R]. PODS: grain_R = f_{g_R}⁻¹. -/
noncomputable def grainProj (R : D) : den R → den (grain R) :=
  (grainEquiv R).symm

/-- The grain-level factor: G[R₁] → G[R₂].
    PODS: f_{G₁G₂} = grain_{R₂} ∘ h ∘ f_{g_{R₁}}. -/
noncomputable def grainFactor (R₁ R₂ : D) (h : den R₁ → den R₂) :
    den (grain R₁) → den (grain R₂) :=
  grainProj R₂ ∘ h ∘ (grainEquiv R₁)

/-- The factoring map: R₁ → G[R₂]. PODS: e = grain_{R₂} ∘ h. -/
noncomputable def factorE (R₁ R₂ : D) (h : den R₁ → den R₂) :
    den R₁ → den (grain R₂) :=
  grainProj R₂ ∘ h

/-! ## PODS §7, Theorem 7.1: Grain Homomorphism -/

/-- **PODS Theorem 7.1(i) — Factorization:**
    h = f_{g_{R₂}} ∘ e where e = grain_{R₂} ∘ h.
    Any h : R₁ → R₂ factors through G[R₂]. -/
theorem grain_homomorphism_i (R₁ R₂ : D) (h : den R₁ → den R₂) :
    h = (grainEquiv R₂) ∘ (factorE R₁ R₂ h) := by
  funext x
  simp only [Function.comp_apply, factorE, grainProj,
    Equiv.apply_symm_apply]

/-- **Lemma (Grain Factorization Square):**
    e = f_{G₁G₂} ∘ grain_{R₁}. The factoring map decomposes through
    the source grain. Used to derive Thm 7.1(ii) from 7.1(i). -/
theorem grain_factorization_square (R₁ R₂ : D) (h : den R₁ → den R₂) :
    factorE R₁ R₂ h = (grainFactor R₁ R₂ h) ∘ (grainProj R₁) := by
  funext x
  simp only [Function.comp_apply, factorE, grainFactor, grainProj,
    Equiv.apply_symm_apply]

/-- **PODS Theorem 7.1(ii) — Commutativity:**
    h = f_{g_{R₂}} ∘ f_{G₁G₂} ∘ grain_{R₁}.
    The grain factorization square commutes: every transformation
    decomposes into extract source grain, map between grains, expand
    via co-domain grain isomorphism. This establishes grain projection
    as a **homomorphism**. -/
theorem grain_homomorphism_ii (R₁ R₂ : D) (h : den R₁ → den R₂) :
    h = (grainEquiv R₂) ∘ (grainFactor R₁ R₂ h) ∘ (grainProj R₁) := by
  funext x
  simp only [Function.comp_apply, grainFactor, grainProj,
    Equiv.apply_symm_apply]

/-! ## PODS §7, Corollary 7.2: Grain Compositionality -/

/-- **PODS Corollary 7.2 (Grain Compositionality):**
    f_{G₁G₃} = f_{G₂G₃} ∘ f_{G₁G₂}.
    The grain-level factor of a composed transformation equals the
    composition of the individual grain-level factors. Follows from
    commutativity (Thm 7.1(ii)): the intermediate type R₂ cancels
    via f_{g_{R₂}} ∘ grain_{R₂} = id. -/
theorem grain_compositionality (R₁ R₂ R₃ : D)
    (h₁ : den R₁ → den R₂) (h₂ : den R₂ → den R₃) :
    grainFactor R₁ R₃ (h₂ ∘ h₁) =
      (grainFactor R₂ R₃ h₂) ∘ (grainFactor R₁ R₂ h₁) := by
  funext x
  simp only [Function.comp_apply, grainFactor, grainProj,
    Equiv.apply_symm_apply]

/-! ## PODS §7 Remark: Surjectivity Characterization -/

/-- **PODS Remark (Connection to Grain Ordering):**
    h surjective ⟺ f_{G₁G₂} surjective (grain iso and its inverse are
    bijections). R₁ ≤_g R₂ precisely when the grain-level factor is
    a surjection. -/
theorem grain_factor_surj_iff (R₁ R₂ : D) (h : den R₁ → den R₂) :
    Function.Surjective h ↔
      Function.Surjective (grainFactor R₁ R₂ h) := by
  constructor
  · intro hs y
    obtain ⟨z, hz⟩ := hs ((grainEquiv R₂) y)
    exact ⟨(grainEquiv R₁).symm z, by
      simp only [grainFactor, grainProj, Function.comp_apply,
        Equiv.apply_symm_apply, hz, Equiv.symm_apply_apply]⟩
  · intro hs y
    obtain ⟨w, hw⟩ := hs ((grainEquiv R₂).symm y)
    refine ⟨(grainEquiv R₁) w, ?_⟩
    have : (grainEquiv R₂).symm (h ((grainEquiv R₁) w)) =
           (grainEquiv R₂).symm y := by
      simpa only [grainFactor, grainProj, Function.comp_apply]
        using hw
    exact (grainEquiv R₂).symm.injective this

end SemanticGrainStructure
