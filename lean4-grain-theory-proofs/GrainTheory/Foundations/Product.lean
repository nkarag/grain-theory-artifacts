/-
  GrainTheory.Foundations.Product — Grain of product types

  arXiv Theorem 3.8: **If no determination is declared among the components**,
  G[R₁ × R₂] ≅ G[R₁] × G[R₂].

  The product of grains is itself a grain of the product type.

  **The independence hypothesis.** Reviewer R2 identified this as a missing
  side condition, and the post-review revision adds it. Where a determination
  *does* hold across components the product is reducible and the conclusion
  fails: with `CustomerId` determining `CustomerName`,
  `G[CustomerId × CustomerName] = CustomerId`, not
  `G[CustomerId] × G[CustomerName]`. In that case the grain is computed by
  Grain Inference (Thm 5.10) instead.

  Both theorems below therefore take `indep R₁ R₂` as an explicit hypothesis.
  The isomorphism step does not need it; only irreducibility does.

  Axioms used (Basic.lean):
  - sub_prod: product preserves type subset
  - prod_iso: product preserves isomorphism
  - prod_irred: products of independent irreducible types are irreducible

  Reference: arXiv extended version, §3, Theorem 3.8 (Grain of Product Types).
-/

import GrainTheory.Foundations.GrainDef
import GrainTheory.Foundations.MultipleGrains

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-- The product of grains satisfies `IsGrainOf` for the product type,
    **given that the components are independent**.

    - Isomorphism: `grain Rᵢ ≅ Rᵢ`, and product preserves iso (`prod_iso`).
    - Irreducibility: each `grain Rᵢ` is structurally irreducible, and the
      product of independent irreducible types is irreducible (`prod_irred`).

    arXiv Theorem 3.8 (Grain of Product Types). -/
theorem prod_grain_isGrainOf (R₁ R₂ : D) (h_indep : indep R₁ R₂) :
    IsGrainOf (prod (grain R₁) (grain R₂)) (prod R₁ R₂) :=
  ⟨prod_iso _ _ _ _ (grain_iso R₁) (grain_iso R₂),
   fun S h_ssub h_iso =>
     prod_irred _ _ _ _ S h_indep
       (fun T => grain_irred R₁ T) (fun T => grain_irred R₂ T)
       h_ssub h_iso⟩

/-- arXiv Theorem 3.8: Grain of product types.
    If no determination is declared among the components,
    G[R₁ × R₂] ≅ G[R₁] × G[R₂].

    Proof: `prod (grain R₁) (grain R₂)` is a grain of `prod R₁ R₂`
    (`prod_grain_isGrainOf`), and so is the canonical `grain (prod R₁ R₂)`.
    Two grains of the same type are isomorphic (`multiple_grains_iso`).

    Note how much shorter this is than the earlier version: the structural
    repair means we no longer establish the two inclusions separately and
    close by antisymmetry — grain-hood factors, so Multiple Grains applies
    directly. -/
theorem grain_product (R₁ R₂ : D) (h_indep : indep R₁ R₂) :
    iso (grain (prod R₁ R₂)) (prod (grain R₁) (grain R₂)) :=
  multiple_grains_iso (grain_isGrainOf (prod R₁ R₂)) (prod_grain_isGrainOf R₁ R₂ h_indep)

end GrainTheory.Foundations
