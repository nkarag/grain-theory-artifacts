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

/-- **arXiv Thm 5.10 (strengthened): Grain Inference → Grain Identity.**

    If (i) `G ⊆_typ R`, (ii) `G ≤_g R`, and (iii) `G` is irreducible
    (`G[G] = G` in the paper's notation), then `IsGrainOf G R`.

    Conditions (i) and (ii) run in **opposite** directions and neither
    implies the other: (i) is a surjection `R ↠ G` (G is *recoverable* from
    R); (ii) is a surjection `G ↠ R` (G *determines* R). Adding (iii) pins
    `G[R]` to exactly `G`.

    **Condition (iii) after the structural repair.** It used to read
    `iso (grain G) G` — G is isomorphic to its own grain — and the proof
    transported irreducibility from `grain G` to `G` across that
    isomorphism. That transport is *unsound* under the structural reading:
    structural irreducibility is not an isomorphism-invariant property (that
    is exactly the reviewer's point — `CustomerId` and
    `CustomerId × CustomerName` are isomorphic, yet only the first is
    irreducible). Condition (iii) is therefore now `IsIrreducible G`
    directly, which is what the paper's `G[G] = G` asserts: G *is a grain
    of itself*, not merely isomorphic to one.

    The new hypothesis is strictly stronger — `IsIrreducible G` implies
    `iso (grain G) G` (`irreducible_iso_grain` below) but not conversely —
    so every downstream caller now has a real obligation to discharge. That
    is the intended consequence of the repair: results that *conclude*
    grain-hood must actually establish irreducibility.

    Proof:
    - ≡_g from `grain_inference` (conditions (i) and (ii))
    - the isomorphism clause follows as before
    - irreducibility is condition (iii), transported to R through
      `isGrainOf_iff_iso_and_irreducible` -/
theorem grain_inference_isGrainOf {G R : D}
    (h_sub : sub G R) (h_le : grainLe G R) (h_irred : Foundations.IsIrreducible G) :
    Foundations.IsGrainOf G R := by
  -- Condition (iii) gives G ≅ G[G], which is what the isomorphism step needs.
  have h_idem : iso (grain G) G :=
    Foundations.multiple_grains_iso (Foundations.grain_isGrainOf G) h_irred.self_grain
  -- Conditions (i)+(ii): grain equivalence
  have h_eqg : grainEq G (grain R) := grain_inference h_sub h_le
  -- G ≅ R (isomorphism clause)
  have h_grainG_iso_grainR : iso (grain G) (grain R) :=
    iso_trans _ _ _ h_eqg (Foundations.grain_idempotent R)
  have h_G_iso_grainR : iso G (grain R) :=
    iso_trans _ _ _ (iso_symm _ _ h_idem) h_grainG_iso_grainR
  have h_G_iso_R : iso G R :=
    iso_trans _ _ _ h_G_iso_grainR (grain_iso R)
  -- Grain-hood factors: isomorphism + irreducibility
  exact Foundations.IsGrainOf.mk' h_G_iso_R h_irred

/-- Irreducibility implies the old condition (iii), `G[G] ≅ G`, but not
    conversely — the converse would require transporting a structural
    property across an isomorphism. -/
theorem irreducible_iso_grain {G : D} (h : Foundations.IsIrreducible G) :
    iso (grain G) G :=
  Foundations.multiple_grains_iso (Foundations.grain_isGrainOf G) h.self_grain

end GrainTheory.Relations
