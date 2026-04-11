/-
  GrainTheory.Foundations.Product — Grain of product types

  PODS Theorem 3.8: G[R₁ × R₂] ≅ G[R₁] × G[R₂].

  The product of grains is itself a grain of the product type.
  The proof establishes that prod (grain R₁) (grain R₂) satisfies the
  three grain axioms for prod R₁ R₂, then uses antisymmetry to conclude
  iso with the canonical grain.

  New axioms used (added to Basic.lean):
  - sub_prod: product preserves type subset
  - prod_iso: product preserves isomorphism
  - prod_irred: products of irreducible types are irreducible

  Reference: PODS 2027 paper, §3, Theorem grain-product.
-/

import GrainTheory.Foundations.GrainDef

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-- PODS Theorem 3.8: Grain of product types.
    G[R₁ × R₂] ≅ G[R₁] × G[R₂].

    Proof outline:
    1. Show prod (grain R₁) (grain R₂) is a grain of prod R₁ R₂:
       - Subset: grain Rᵢ ⊆_typ Rᵢ, so prod preserves this (sub_prod)
       - Isomorphism: grain Rᵢ ≅ Rᵢ, so prod preserves this (prod_iso)
       - Irreducibility: grains are irreducible, so prod of irred is irred (prod_irred)
    2. Since both grain (prod R₁ R₂) and prod (grain R₁) (grain R₂) are grains
       of prod R₁ R₂, they are isomorphic:
       - iso_sub + grain_sub gives grain (prod R₁ R₂) ⊆_typ prod (grain R₁) (grain R₂)
       - prod_irred + grain_iso gives the reverse inclusion
       - sub_antisymm concludes -/
theorem grain_product (R₁ R₂ : D) :
    iso (grain (prod R₁ R₂)) (prod (grain R₁) (grain R₂)) := by
  -- Step 1: prod (grain R₁) (grain R₂) satisfies the three grain axioms for prod R₁ R₂
  -- (a) Subset: prod (grain R₁) (grain R₂) ⊆_typ prod R₁ R₂
  have h_sub : sub (prod (grain R₁) (grain R₂)) (prod R₁ R₂) :=
    sub_prod _ _ _ _ (grain_sub R₁) (grain_sub R₂)
  -- (b) Isomorphism: prod (grain R₁) (grain R₂) ≅ prod R₁ R₂
  have h_iso : iso (prod (grain R₁) (grain R₂)) (prod R₁ R₂) :=
    prod_iso _ _ _ _ (grain_iso R₁) (grain_iso R₂)
  -- (c) Irreducibility: product of irreducible types is irreducible
  have h_irred : ∀ S : D, sub S (prod (grain R₁) (grain R₂)) →
      iso S (prod R₁ R₂) → sub (prod (grain R₁) (grain R₂)) S :=
    fun S h_s h_i => prod_irred _ _ _ _ S
      (fun T => grain_irred R₁ T) (fun T => grain_irred R₂ T) h_s h_i
  -- Step 2: Both grain (prod R₁ R₂) and prod (grain R₁) (grain R₂) are grains,
  -- so they must be isomorphic.
  -- (d) grain (prod R₁ R₂) ⊆_typ prod (grain R₁) (grain R₂)
  --     By iso_sub: h_iso : prod(grain..) ≅ prod R₁ R₂, and
  --     grain_sub : grain(prod R₁ R₂) ⊆_typ prod R₁ R₂,
  --     so grain(prod R₁ R₂) ⊆_typ prod(grain R₁)(grain R₂)
  have h1 : sub (grain (prod R₁ R₂)) (prod (grain R₁) (grain R₂)) :=
    iso_sub _ _ _ h_iso (grain_sub (prod R₁ R₂))
  -- (e) prod (grain R₁) (grain R₂) ⊆_typ grain (prod R₁ R₂)
  --     From h1 and grain_iso, by h_irred
  have h2 : sub (prod (grain R₁) (grain R₂)) (grain (prod R₁ R₂)) :=
    h_irred _ h1 (grain_iso (prod R₁ R₂))
  -- (f) Antisymmetry: both directions give isomorphism
  exact sub_antisymm _ _ h1 h2

/-- The product of grains satisfies `IsGrainOf` for the product type.
    This packages the three grain properties for downstream use. -/
theorem prod_grain_isGrainOf (R₁ R₂ : D) :
    IsGrainOf (prod (grain R₁) (grain R₂)) (prod R₁ R₂) :=
  ⟨prod_iso _ _ _ _ (grain_iso R₁) (grain_iso R₂),
   fun S h_sub h_iso =>
     prod_irred _ _ _ _ S
       (fun T => grain_irred R₁ T) (fun T => grain_irred R₂ T)
       h_sub h_iso⟩

end GrainTheory.Foundations
