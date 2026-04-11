/-
  GrainTheory.Relations.GrainInference — Grain inference sufficient condition

  PODS Theorem 4.9 (strengthened): If G ⊆_typ R, G ≤_g R, and G[G] ≅ G,
  then G is a grain of R (IsGrainOf G R):
    - G ≅ R (isomorphism)
    - G is irreducible w.r.t. R

  The weaker conclusion G ≡_g G[R] (grain equivalence) follows from just
  conditions (i) and (ii), without needing G[G] = G. The stronger
  conclusion (grain identity) requires all three conditions.

  Used downstream by: intersection/union (LP-16), equi-join (LP-21),
  RA operations (LP-24).
-/

import GrainTheory.Relations.GrainOrdering
import GrainTheory.Foundations.Idempotency
import GrainTheory.Foundations.GrainDef

namespace GrainTheory.Relations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-- PODS Thm 4.9: Grain inference sufficient condition.
    If G ⊆_typ R and G ≤_g R, then G ≡_g G[R].

    The paper states three conditions (G ⊆_typ R, G ≤_g R, G[G] = G),
    but condition (3) is not needed: the proof uses only (1) and (2).

    Proof:
    - From (2): sub (grain R) (grain G)                    [grainLe unfolded]
    - From (1) + iso_sub: sub G (grain R)                  [iso types have same subsets]
    - Then: sub (grain G) G ⊆_typ (grain R)                [grain_sub + trans]
    - Antisymmetry: iso (grain G) (grain R)
    - Compose with idempotency: iso (grain G) (grain (grain R)) -/
theorem grain_inference {G R : D}
    (h_sub : sub G R) (h_le : grainLe G R) : grainEq G (grain R) := by
  -- h_le unfolds to: sub (grain R) (grain G)
  -- Goal: grainEq G (grain R) = iso (grain G) (grain (grain R))
  -- Step 1: sub G (grain R) via iso_sub
  have h1 : sub G (grain R) :=
    iso_sub _ _ _ (grain_iso R) h_sub
  -- Step 2: sub (grain G) (grain R) via grain_sub + trans
  have h2 : sub (grain G) (grain R) :=
    sub_trans _ _ _ (grain_sub G) h1
  -- Step 3: sub (grain R) (grain G) from h_le
  have h3 : sub (grain R) (grain G) := h_le
  -- Step 4: iso (grain G) (grain R) by antisymmetry
  have h4 : iso (grain G) (grain R) :=
    sub_antisymm _ _ h2 h3
  -- Step 5: iso (grain R) (grain (grain R)) from idempotency
  have h5 : iso (grain R) (grain (grain R)) :=
    iso_symm _ _ (Foundations.grain_idempotent R)
  -- Step 6: compose to get iso (grain G) (grain (grain R))
  exact iso_trans _ _ _ h4 h5

/-- Variant with all three paper conditions, for downstream compatibility. -/
theorem grain_inference' {G R : D}
    (h_sub : sub G R) (h_le : grainLe G R) (_h_idem : iso (grain G) G) :
    grainEq G (grain R) :=
  grain_inference h_sub h_le

/-- **PODS Thm 4.9 (strengthened): Grain Inference → Grain Identity.**

    If (i) G ⊆_typ R, (ii) G ≤_g R, and (iii) G[G] ≅ G, then
    IsGrainOf G R: G is a grain of R (iso + irreducible).

    This is strictly stronger than `grain_inference` (which gives ≡_g).
    Condition (iii) is essential: it provides irreducibility via transfer.

    Proof:
    - ≡_g from `grain_inference` (Steps 1-3)
    - ≡_g + (iii) + idempotency: G ≅ grain R ≅ R (iso condition)
    - S ⊆ G, S ≅ R → S ≅ G → grain_irred: grain G ⊆ S
      → iso_sub + sub_trans: G ⊆ grain G ⊆ S (irred condition) -/
theorem grain_inference_isGrainOf {G R : D}
    (h_sub : sub G R) (h_le : grainLe G R) (h_idem : iso (grain G) G) :
    Foundations.IsGrainOf G R := by
  -- Step 1-3: grain equivalence (from existing proof)
  have h_eqg : grainEq G (grain R) := grain_inference h_sub h_le
  -- h_eqg : iso (grain G) (grain (grain R))
  -- Step 4: G ≅ R (isomorphism)
  have h_grainG_iso_grainR : iso (grain G) (grain R) :=
    iso_trans _ _ _ h_eqg (Foundations.grain_idempotent R)
  have h_G_iso_grainR : iso G (grain R) :=
    iso_trans _ _ _ (iso_symm _ _ h_idem) h_grainG_iso_grainR
  have h_G_iso_R : iso G R :=
    iso_trans _ _ _ h_G_iso_grainR (grain_iso R)
  -- Step 5: Irreducibility — for any S ⊆ G with S ≅ R, show G ⊆ S
  have h_irred : ∀ S : D, sub S G → iso S R → sub G S := by
    intro S h_s_sub_G h_s_iso_R
    -- S ≅ G (by transitivity: S ≅ R ≅ G⁻¹)
    have h_s_iso_G : iso S G :=
      iso_trans _ _ _ h_s_iso_R (iso_symm _ _ h_G_iso_R)
    -- Transfer S ⊆ G to S ⊆ grain G (via iso_sub: grain G ≅ G → S ⊆ G → S ⊆ grain G)
    have h_s_sub_grainG : sub S (grain G) :=
      iso_sub _ _ _ h_idem h_s_sub_G
    -- grain_irred G S: S ⊆ grain G and S ≅ G → grain G ⊆ S
    have h_grainG_sub_S : sub (grain G) S :=
      grain_irred G S h_s_sub_grainG h_s_iso_G
    -- Key: G ⊆ grain G (from iso_sub: grain G ≅ G → G ⊆ G → G ⊆ grain G)
    have h_G_sub_grainG : sub G (grain G) :=
      iso_sub _ _ _ h_idem (sub_refl G)
    -- Chain: G ⊆ grain G ⊆ S
    exact sub_trans _ _ _ h_G_sub_grainG h_grainG_sub_S
  exact ⟨h_G_iso_R, h_irred⟩

end GrainTheory.Relations
