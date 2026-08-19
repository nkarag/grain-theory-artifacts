/-
  GrainTheory.Inference.GrainReduction — Grain Reduction under Declared FDs

  arXiv extended version, §7, Proposition [Grain Reduction under Declared FDs].

  Theorem 7.2 computes the grain of an equi-join from the **grains** of its
  inputs — determinations whose left side is a whole grain. A schema may also
  declare a functional dependency whose left side is an *arbitrary* attribute
  set, possibly spanning both inputs and matching no grain. Such a dependency is
  invisible to the grain-level rule, yet it can shrink the grain further.

  The paper's example: joining `RegionId × StoreId` with
  `RegionId × Season × Discount` on `RegionId` gives
  `RegionId × StoreId × Season × Discount` by Thm 7.2 — correct at the grain
  level, since no whole grain determines a field of the other. But a declared
  `{StoreId, Season} → Discount` is neither input's grain, so no grain-level
  rule sees it, and `Discount` is in fact redundant. The true grain is
  `RegionId × StoreId × Season`.

  This module mechanizes the two-layer structure:

  1. what Thm 7.2 returns is a **superkey** of the result;
  2. minimizing that superkey — deleting determined attributes to a fixpoint —
     yields a **grain**, unique up to isomorphism.

  Step 2 is classical superkey-to-candidate-key reduction. Abstractly it is
  minimization over structural subtypes, which is `ssub_wf` — the same principle
  the paper's own Lemma 3.2 uses to establish grain existence.

  The polynomial-time claim is a meta-property of the algorithm, not a Lean
  theorem; `Model/` carries the computational content.
-/

import GrainTheory.Inference.EquiJoin
import GrainTheory.Foundations.MultipleGrains

namespace GrainTheory.Inference

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub ssub ssub_sub ssub_refl ssub_trans ssub_wf iso grain
  union diff inter prod iso_refl iso_symm iso_trans)
open GrainTheory.Foundations (IsGrainOf IsIrreducible multiple_grains_iso)

/-! ## Step 1 — what Theorem 7.2 returns is a superkey -/

/-- A grain of `Res` **determines** `Res`: the grain projection restricted to it
    identifies every element. This is the paper's first step — "so `G[Res]` is a
    superkey of `Res`". -/
theorem superkey_of_isGrainOf {G Res : D}
    (h_grain : IsGrainOf G Res) (h_sub : sub G Res) :
    EquiJoinStructure.determines G Res :=
  EquiJoinStructure.iso_determines G Res h_grain.1 h_sub

/-- **It stays a superkey under any further declared dependencies.**

    "Declaring dependencies only adds constraints, it never removes the
    identification." At the type level this is immediate: the determination is
    already established, and `determines` is a property of the pair, not of the
    dependency set. Recorded because the paper's proof turns on it. -/
theorem superkey_stable {G Res : D}
    (h : EquiJoinStructure.determines G Res) : EquiJoinStructure.determines G Res :=
  h

/-! ## Step 2 — minimizing a superkey yields a grain

  The classical superkey-to-candidate-key reduction. An attribute is
  *extraneous* when the rest still determines it; dropping extraneous attributes
  to a fixpoint leaves a minimal identifying set.

  Abstractly, "drop a component and keep identifying `Res`" is exactly
  minimization over structural subtypes under the predicate `· ≅ Res`, so the
  fixpoint is a `⊑`-minimal type isomorphic to `Res` — which is Definition 3.1. -/

/-- **Proposition [Grain Reduction under Declared FDs].**

    Any type isomorphic to `Res` — in particular the superkey Theorem 7.2
    returns — reduces to a **grain** of `Res` sitting structurally inside it.

    The reduction is the paper's: delete a component that the rest still
    determines, iterate to a fixpoint. At the fixpoint no proper structural
    subtype is still isomorphic to `Res`, which is precisely irreducibility. -/
theorem grain_reduction (G Res : D) (h_iso : iso G Res) :
    ∃ K : D, ssub K G ∧ IsGrainOf K Res := by
  obtain ⟨K, h_ssub, h_K_iso, h_min⟩ := ssub_wf G (fun T => iso T Res) h_iso
  exact ⟨K, h_ssub, ⟨h_K_iso, fun S h_S_ssub h_S_iso => h_min S h_S_ssub h_S_iso⟩⟩

/-- The reduction is **well-defined up to isomorphism, regardless of deletion
    order**: any two results are isomorphic.

    "Any two candidate keys are grains of `Res` and therefore isomorphic
    (Theorem 3.4), so the fixpoint is well-defined up to isomorphism regardless
    of deletion order." -/
theorem grain_reduction_unique {K₁ K₂ Res : D}
    (h₁ : IsGrainOf K₁ Res) (h₂ : IsGrainOf K₂ Res) : iso K₁ K₂ :=
  multiple_grains_iso h₁ h₂

/-- Grain existence is the same argument with `G = Res`: `Res ≅ Res`, so the
    reduction applies and returns a grain. This is arXiv Lemma 3.2, now derived
    from the minimization principle rather than supplied by the operator. -/
theorem grain_exists_by_reduction (Res : D) : ∃ K : D, ssub K Res ∧ IsGrainOf K Res :=
  grain_reduction Res Res (iso_refl Res)

/-! ## The two layers, composed

  The equi-join instance: Theorem 7.2's candidate is a superkey of the result,
  and reducing it under the declared dependencies gives the grain. -/

/-- **The equi-join candidate reduces to the grain.**

    Thm 7.2 returns `F₁ = G[R₁] ∪typ (G[R₂] -typ Jk)` under its grain-level
    hypotheses. That candidate is a superkey of `Res`; Grain Reduction then
    removes any component determined by the rest through a declared FD whose
    left side is no grain — the composite cross-input case the grain-level rule
    cannot see — and what remains is a grain of `Res`, structurally inside `F₁`.

    The grain-level rule is correct as far as *grains* determine; the
    attribute-level FD refines it. -/
theorem equijoin_grain_reduction
    (R₁ R₂ Jk Res : D)
    (h_jk_r1 : ssub Jk R₁) (h_jk_r2 : ssub Jk R₂)
    (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
    (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
    (h_indep : InformationallyIndependent (grain R₁) (diff (grain R₂) Jk))
    (h_adm : AdmissibleLabeling R₁ R₂ Jk) :
    ∃ K : D, ssub K (union (grain R₁) (diff (grain R₂) Jk)) ∧ IsGrainOf K Res :=
  grain_reduction _ Res
    (equijoin_grain_identity R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup
      h_indep h_adm).1

/-- When no declared dependency reduces it, the candidate **is** the grain —
    the reduction is the identity, and Thm 7.2's answer stands unrefined. -/
theorem equijoin_reduction_trivial_of_irreducible
    {R₁ R₂ Jk Res : D}
    (h_grain : IsGrainOf (union (grain R₁) (diff (grain R₂) Jk)) Res)
    {K : D} (h_K : IsGrainOf K Res) :
    iso K (union (grain R₁) (diff (grain R₂) Jk)) :=
  multiple_grains_iso h_K h_grain

end GrainTheory.Inference
