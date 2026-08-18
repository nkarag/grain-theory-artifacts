/-
  GrainTheory.Inference.EquiJoinAxioms — Axioms for equi-join grain inference

  Extends GrainStructure with functional dependency (`determines`) and
  related axioms needed for LP-21 (equi-join grain inference theorem).

  Reference: PODS 2027 paper, §6 (Grain Inference for Equi-Join);
  BULLETPROOF_EQUIJOIN_PLAN.md §2.3 (axiomatization extensions).
-/

import GrainTheory.Basic
import GrainTheory.Foundations.GrainDef
import GrainTheory.Foundations.Product

universe u

/-- Extension of GrainStructure with functional-dependency semantics.

    `determines G R` encodes the type-level functional dependency G → R:
    knowing the G-projection of any instance uniquely identifies the
    R-projection.  This bridges structural grain reasoning (⊆_typ, ≅)
    with semantic determination, which is essential for the bootstrapping
    argument in the equi-join proof.
-/
class EquiJoinStructure (D : Type u) extends GrainStructure D where
  /-- Functional dependency: `determines G R` means G → R at the type level.
      PODS justification: the projection π_G is injective on instances of R. -/
  determines : D → D → Prop

  /-- The grain always determines its type: G[R] → R.
      PODS justification: G[R] is a superkey of R by definition
      (grain axiom 2: G[R] ≅ R, meaning the projection is bijective). -/
  grain_determines : ∀ (R : D), determines (grain R) R

  /-- Monotonicity: enlarging the determiner preserves determination.
      If G → R and G ⊆_typ H, then H → R.
      PODS justification: a superset of a superkey is still a superkey. -/
  determines_mono : ∀ (G H R : D), determines G R → sub G H → determines H R

  /-- Projection: determination restricts to sub-types.
      If G → R and S ⊆_typ R, then G → S.
      PODS justification: if G determines all columns of R, it certainly
      determines any subset of those columns. -/
  determines_sub : ∀ (G R S : D), determines G R → sub S R → determines G S

  /-- Determination + subset implies isomorphism.
      If G → R and G ⊆_typ R, then G ≅ R.
      PODS justification: the projection π_G is injective (from determines)
      and surjective (from G ⊆ R, every G-value appears), hence bijective. -/
  determines_iso_of_sub : ∀ (G R : D),
    determines G R → sub G R → iso G R

  /-- Union: if G determines A and G determines B, then G determines A ∪ B.
      PODS justification: knowing G-values gives both A-values and B-values,
      hence all (A ∪ B)-values. -/
  determines_union : ∀ (G A B : D),
    determines G A → determines G B → determines G (union A B)

  /-- Product: if G determines A and G determines B, then G determines A × B.
      PODS justification: knowing G-values gives both A-values and B-values,
      hence the combined (A × B)-values. Product analogue of determines_union. -/
  determines_prod : ∀ (G A B : D),
    determines G A → determines G B → determines G (prod A B)

  /-- Transitivity: determination composes.
      If G → H and H → R, then G → R.
      PODS justification: composition of injective projections. -/
  determines_trans : ∀ (G H R : D),
    determines G H → determines H R → determines G R

  /-- Superkeys contain the grain: if G → R and G ⊆_typ R, then G[R] ⊆_typ G.
      PODS justification: G is a superkey (determines + sub ⇒ injective projection),
      and the grain is the minimal superkey. Any superkey must contain all grain
      columns, otherwise the grain would have a proper subset that determines R,
      contradicting irreducibility.
      This is the sound fragment of iso_sub needed for equi-join grain containment:
      it applies only to sub-types that determine R, not to arbitrary sub-types
      of isomorphic types. -/
  determines_grain_sub : ∀ (G R : D),
    determines G R → sub G R → sub (grain R) G

  -- ================================================================
  -- Axioms for grain-definition irreducibility (Phase 3)
  -- ================================================================

  /-- Isomorphic sub-types determine their parent: if S ≅ R and S ⊆_typ R, then S → R.
      PODS justification: S ≅ R means there is a bijection between S-instances and
      R-instances. S ⊆_typ R means every S-field is an R-field, so the projection
      π_S : R → S exists. The bijection implies π_S is injective, which is
      determination. Converse of `determines_iso_of_sub` for the determines part. -/
  iso_determines : ∀ (S R : D), iso S R → sub S R → determines S R

  -- ================================================================
  -- Structural irreducibility of the equi-join candidate (arXiv Thm 7.2)
  -- ================================================================

  /-- **Equi-join candidate irreducibility (arXiv Thm 7.2, irreducibility
      step).**

      Writing `Gᵢ^Jk = G[Rᵢ] ∩ Jk` for each input's join-key grain portion,
      the candidate `G[R₁] ∪ (G[R₂] \ Jk)` is structurally irreducible
      exactly when `G₂^Jk` is *not* a proper structural subtype of `G₁^Jk`.

      arXiv justification (Thm 7.2 proof, "A field of G₁^rest or G₂^rest is
      never redundant…"): the candidate's fields are those of `G[R₁]` — split
      into `G₁^rest` and `G₁^Jk` — together with `G₂^rest = G[R₂] \ Jk`. A
      field of `G₁^rest` or `G₂^rest` is never redundant: it is a non-Jk field
      of an irreducible grain, recovered neither from the rest of that grain
      nor, lying outside Jk, through the join. A field `f ∈ G₁^Jk` can be
      recovered only via the opposite grain `G[R₂]` through the join, which
      requires the candidate minus `f` to still contain all of
      `G[R₂] = G₂^rest ∪ G₂^Jk`. Since the candidate's Jk-fields are exactly
      `G₁^Jk`, such an `f` exists iff `G₂^Jk ⊏ G₁^Jk`. Hence the candidate is
      reducible iff `G₂^Jk ⊏ G₁^Jk`, which is the hypothesis negated here.

      This covers both admissible cases of Thm 7.2: the *canonical* labeling
      (`G₁^Jk ⊑ G₂^Jk`) and the *incomparable* case both satisfy
      `¬ (G₂^Jk ⊏ G₁^Jk)`; only the strict reverse labeling fails it, and
      there the candidate genuinely is reducible.

      **Relation routing.** Both the gate and the reducibility criterion are
      structural: `⊑` for the canonical labeling, `⊏` for the strict
      comparison. The paper agrees as of the §7/appendix notation sweep
      (`6963ec1`, `4ae23dd`), which converted the six `⊊` sites to `⊏` and the
      labeling comparisons to `⊑`. -/
  equijoin_candidate_irred : ∀ (R₁ R₂ Jk S : D),
    ¬ GrainTheory.Foundations.properSsub
        (inter (grain R₂) Jk) (inter (grain R₁) Jk) →
    ssub S (union (grain R₁) (diff (grain R₂) Jk)) →
    iso S (union (grain R₁) (diff (grain R₂) Jk)) →
    ssub (union (grain R₁) (diff (grain R₂) Jk)) S

namespace EquiJoinStructure

variable {D : Type u} [EquiJoinStructure D]

-- Re-open GrainStructure names for readability
open GrainStructure (sub iso grain union inter diff prod
  sub_refl sub_trans sub_antisymm
  iso_refl iso_symm iso_trans iso_sub
  grain_sub grain_iso grain_irred ssub ssub_sub ssub_refl ssub_trans ssub_antisymm indep
  sub_union_left sub_union_right union_sub
  inter_sub_left inter_sub_right sub_inter
  sub_diff sub_union_diff
  diff_inter_empty diff_sub_left inter_distrib_union
  sub_prod_left sub_prod_right)

-- ================================================================
-- Derived lemmas (sanity checks exercising the new axioms)
-- ================================================================

/-- Every type determines itself. -/
theorem determines_self (R : D) : determines R R := by
  have h_det := grain_determines R   -- G[R] → R
  have h_sub := grain_sub R          -- G[R] ⊆_typ R
  exact determines_mono (grain R) R R h_det h_sub

/-- A type determines any of its sub-types.
    Used in bootstrapping: F₁ contains G₂_rest ⊆_typ F₁, so F₁ → G₂_rest. -/
theorem determines_of_sub (G B : D) (h : sub B G) : determines G B :=
  determines_sub G G B (determines_self G) h

/-- A **proper structural** subtype of the grain cannot determine the type.

    Dropping a component from G[R] — `S ⊏ G[R]` — leaves something that no
    longer determines R. This is the schema-decidable form of irreducibility:
    it says the grain has no redundant component.

    Restated over `⊑` as part of the notation split. Under the old
    `⊆_typ` reading the hypothesis `¬ (G[R] ⊆_typ S)` was unsatisfiable
    whenever `S ≅ R`, so the lemma had no instances — the vacuity the
    reviewer identified, visible here as a lemma that could never fire. -/
theorem grain_irred_determines (R S : D)
    (h_ssub : ssub S (grain R)) (h_proper : ¬ ssub (grain R) S) :
    ¬ determines S R := by
  intro h_det
  -- S ⊑ G[R] ⊆_typ R, so S ⊆_typ R
  have h_sub_R : sub S R :=
    sub_trans S (grain R) R (ssub_sub S (grain R) h_ssub) (grain_sub R)
  -- S → R and S ⊆_typ R imply S ≅ R
  have h_iso : iso S R := determines_iso_of_sub S R h_det h_sub_R
  -- S ⊑ G[R] and S ≅ R, by structural grain irreducibility: G[R] ⊑ S
  have h_contra : ssub (grain R) S := grain_irred R S h_ssub h_iso
  exact h_proper h_contra

-- ================================================================
-- Derived lemmas from Phase 3 axioms
-- ================================================================

/-- Any sub-type isomorphic to R contains the grain.
    If S ≅ R and S ⊆_typ R, then G[R] ⊆_typ S.

    Combines `iso_determines` with `determines_grain_sub`: isomorphism gives
    determination, and any determiner that is a sub-type contains the grain. -/
theorem iso_sub_grain (S R : D) (h_iso : iso S R) (h_sub : sub S R) :
    sub (grain R) S := by
  have h_det : determines S R := iso_determines S R h_iso h_sub
  exact determines_grain_sub S R h_det h_sub

/-- Intersection is monotone in the first argument:
    A ⊆_typ B → (A ∩ C) ⊆_typ (B ∩ C). -/
theorem inter_mono_left (A B C : D) (h : sub A B) :
    sub (inter A C) (inter B C) := by
  have h1 : sub (inter A C) B := sub_trans _ _ _ (inter_sub_left A C) h
  have h2 : sub (inter A C) C := inter_sub_right A C
  exact sub_inter B C (inter A C) h1 h2

/-- Intersection is monotone in the second argument:
    A ⊆_typ B → (C ∩ A) ⊆_typ (C ∩ B). -/
theorem inter_mono_right (A B C : D) (h : sub A B) :
    sub (inter C A) (inter C B) := by
  have h1 : sub (inter C A) C := inter_sub_left C A
  have h2 : sub (inter C A) B := sub_trans _ _ _ (inter_sub_right C A) h
  exact sub_inter C B (inter C A) h1 h2

/-- diff of the grain is sub-type of diff of the type:
    G[R] ⊆_typ R → (G[R] \ S) ⊆_typ (R \ S). -/
theorem diff_grain_sub_diff (R S : D) :
    sub (diff (grain R) S) (diff R S) :=
  diff_sub_left (grain R) R S (grain_sub R)

end EquiJoinStructure
