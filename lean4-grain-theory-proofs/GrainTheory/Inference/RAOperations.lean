/-
  GrainTheory.Inference.RAOperations — Grain inference for RA operations

  PODS §6, Table 1: Grain inference rules for all standard relational
  algebra operations. Proofs match PODS appendix (lines 536–593).

  Operations covered:
  - Selection σ: G[Res] = G[R] (type unchanged)
  - Projection π_S: G[Res] = G[R] when G[R] ⊆ S (grain preserved)
  - Extension ε: G[Res] = G[R] (D functionally determined)
  - Rename ρ: G[Res] ≡_g G[R] (structural type difference)
  - Grouping γ: G[Res] = G_c (one row per group)
  - Set ops ∪∩−: G[Res] = G[R] (type unchanged)
  - Theta join ⋈_θ: G[Res] = G[R₁] × G[R₂] (grain product)
  - Semi-join ⋉: G[Res] = G[R₁] (filter only)
  - Anti-join ▷: G[Res] = G[R₁] (filter only)
-/

import GrainTheory.Relations.GrainEquality
import GrainTheory.Foundations.Product
import GrainTheory.Foundations.MultipleGrains

namespace GrainTheory.Inference

variable {D : Type*} [GrainStructure D]

open GrainStructure (iso grain sub prod iso_symm iso_trans
  grain_iso iso_sub sub_antisymm)
open GrainTheory.Relations (grainEq grainEq_of_iso)
open GrainTheory.Foundations (grain_product IsGrainOf grain_isGrainOf
  multiple_grains_iso)

/-! ## General Lemma: Type-Unchanged Operations -/

/-- If the result type is isomorphic to the input type, the grain is preserved.
    Base lemma for selection, set ops, semi-join, and anti-join.

    PODS justification: grain is a type-level property; iso types have
    isomorphic grains (Theorem 4.2). -/
theorem grain_type_unchanged (R Res : D) (h : iso Res R) :
    iso (grain Res) (grain R) :=
  grainEq_of_iso h

/-! ## Tier 1: Type-Unchanged Operations (Res = R) -/

/-- PODS Table 1: Selection σ_θ.
    Selection filters rows without changing the type: Res = R.
    G[Res] = G[R]. (Appendix proof, line 536) -/
theorem grain_selection (R Res : D) (h : iso Res R) :
    iso (grain Res) (grain R) :=
  grain_type_unchanged R Res h

/-- PODS Table 1: Set operations ∪, ∩, −.
    Union-compatible types (R₁ = R₂ = R), so Res = R.
    G[Res] = G[R]. (Appendix proof, line 575) -/
theorem grain_set_ops (R Res : D) (h : iso Res R) :
    iso (grain Res) (grain R) :=
  grain_type_unchanged R Res h

/-- PODS Table 1: Semi-join ⋉.
    Returns rows from R₁ only: Res = R₁.
    G[Res] = G[R₁]. (Appendix proof, line 588) -/
theorem grain_semijoin (R₁ Res : D) (h : iso Res R₁) :
    iso (grain Res) (grain R₁) :=
  grain_type_unchanged R₁ Res h

/-- PODS Table 1: Anti-join ▷.
    Returns rows from R₁ only: Res = R₁.
    G[Res] = G[R₁]. (Appendix proof, line 588) -/
theorem grain_antijoin (R₁ Res : D) (h : iso Res R₁) :
    iso (grain Res) (grain R₁) :=
  grain_type_unchanged R₁ Res h

/-! ## Tier 2: Theta Join (via grain product) -/

/-- PODS Table 1: Theta join ⋈_θ.
    Res = R₁ × R₂ (full product; θ filters but creates no equality
    constraints). G[Res] = G[R₁] × G[R₂] by Theorem grain-product.
    (Appendix proof, line 581) -/
theorem grain_theta_join (R₁ R₂ : D) :
    iso (grain (prod R₁ R₂)) (prod (grain R₁) (grain R₂)) :=
  grain_product R₁ R₂

/-! ## Tier 3: Projection (conditional) -/

/-- PODS Table 1: Projection π_S.
    Res = S where S ⊆_typ R. If G[R] ⊆_typ S (grain fields survive),
    then G[S] = G[R].

    Proof:
    1. iso_sub: G[R] ≅ R and S ⊆ R → S ⊆ G[R]
    2. sub_antisymm: S ⊆ G[R] and G[R] ⊆ S → S ≅ G[R]
    3. Transitivity: S ≅ G[R] ≅ R → S ≅ R
    4. Theorem 4.2: S ≅ R → G[S] ≅ G[R]
    (Appendix proof, line 543) -/
theorem grain_projection (R S : D) (hSR : sub S R) (hGS : sub (grain R) S) :
    iso (grain S) (grain R) :=
  -- S ⊆ G[R] (from iso_sub: G[R] ≅ R and S ⊆ R)
  have h1 : sub S (grain R) := iso_sub _ _ _ (grain_iso R) hSR
  -- S ≅ G[R] (antisymmetry: S ⊆ G[R] and G[R] ⊆ S)
  have h2 : iso S (grain R) := sub_antisymm _ _ h1 hGS
  -- S ≅ R (transitivity: S ≅ G[R] ≅ R)
  have h3 : iso S R := iso_trans _ _ _ h2 (grain_iso R)
  -- G[S] ≅ G[R] (Theorem 4.2)
  grainEq_of_iso h3

/-! ## Tier 4: Rename (grain equality ≡_g) -/

/-- PODS Table 1: Rename ρ_{a→b}.
    Renaming changes attribute names but preserves structure: Res ≅ R.
    G[Res] ≡_g G[R] (PODS uses ≡_g because types have different field
    names but are isomorphic).

    In our axiomatization, ≡_g is `grainEq`, i.e., G[Res] ≅ G[R].
    (Appendix proof, line 560) -/
theorem grain_rename (R Res : D) (h : iso Res R) : grainEq Res R :=
  grainEq_of_iso h

/-! ## Tier 5: Extension (functionally determined column) -/

/-- PODS Table 1: Extension by D = f(R).
    Res = R × D where D is functionally determined by R.

    Encoding: functional determination means R × D ≅ R (adding a
    determined column preserves information content). Then
    Res ≅ R × D ≅ R, so G[Res] = G[R].
    (Appendix proof, line 551) -/
theorem grain_extension (R D_ext Res : D)
    (h_res : iso Res (prod R D_ext)) (h_det : iso (prod R D_ext) R) :
    iso (grain Res) (grain R) :=
  grainEq_of_iso (iso_trans _ _ _ h_res h_det)

/-! ## Tier 6: Grouping (G_c is a grain by construction) -/

/-- PODS Table 1: Grouping γ_{G_c, agg}.
    Res = G_c × Agg. Grouping produces one row per unique G_c-value,
    so G_c is by construction a grain of Res.

    Encoding: the hypothesis `IsGrainOf G_c Res` captures grouping
    semantics directly. Then G[Res] ≅ G_c by grain uniqueness.
    (Appendix proof, line 568) -/
theorem grain_grouping (G_c Res : D) (h : IsGrainOf G_c Res) :
    iso (grain Res) G_c :=
  iso_symm _ _ (multiple_grains_iso h (grain_isGrainOf Res))

end GrainTheory.Inference
