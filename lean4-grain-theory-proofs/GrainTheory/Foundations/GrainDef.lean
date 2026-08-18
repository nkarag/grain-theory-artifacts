/-
  GrainTheory.Foundations.GrainDef — PODS Definitions 1-3

  Formalizes type subset, proper type subset, and grain as derived
  concepts from the GrainStructure axioms.

  Reference: PODS 2027 paper, §3, Definitions 1-3.
-/

import GrainTheory.Basic

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-! ## Definition 1: Type Subset (⊆_typ)

  Given types A and B, A ⊆_typ B if every field of A is also a field of B.
  This is captured directly by `GrainStructure.sub`.
-/

/-! ## Definition 2: Proper Type Subset (⊂_typ)

  A ⊂_typ B iff A ⊆_typ B and ¬(B ⊆_typ A).
-/

/-- Proper type subset: A ⊂_typ B ≡ A ⊆_typ B ∧ ¬(B ⊆_typ A) (arXiv Def 2.2) -/
def properSub (A B : D) : Prop :=
  sub A B ∧ ¬ sub B A

scoped infixl:50 " ⊂_typ " => properSub

/-! ## Definition 2.3: Proper Structural Subtype (⊏)

  A ⊏ B iff A ⊑ B and ¬(B ⊑ A) — i.e. B has a component not in A.
  This is the relation grain irreducibility quantifies over.
-/

/-- Proper structural subtype: A ⊏ B ≡ A ⊑ B ∧ ¬(B ⊑ A) (arXiv Def 2.3).
    Unfolding component containment, `¬(B ⊑ A)` says exactly that B has a
    component not occurring in A. -/
def properSsub (A B : D) : Prop :=
  ssub A B ∧ ¬ ssub B A

scoped infixl:50 " ⊏_typ " => properSsub

/-- A proper structural subtype is a structural subtype. -/
theorem properSsub_ssub {A B : D} (h : properSsub A B) : ssub A B :=
  h.1

/-- Proper structural subtyping is irreflexive. -/
theorem properSsub_irrefl (A : D) : ¬ properSsub A A :=
  fun ⟨h, hn⟩ => hn h

/-- Proper structural subtyping is asymmetric. -/
theorem properSsub_asymm {A B : D} (h : properSsub A B) : ¬ properSsub B A :=
  fun ⟨hba, _⟩ => h.2 hba

/-- ⊏ refines ⊂_typ only in its first component: `A ⊏ B` gives `A ⊆_typ B`,
    but *not* `¬(B ⊆_typ A)` — a declared surjection may still run backwards.
    This one-way refinement is exactly why the structural reading of
    irreducibility is strictly stronger than the semantic one. -/
theorem properSsub_sub {A B : D} (h : properSsub A B) : sub A B :=
  ssub_sub _ _ h.1

/-- Proper subset implies subset -/
theorem properSub_sub {A B : D} (h : properSub A B) : sub A B :=
  h.1

/-- Proper subset is irreflexive -/
theorem properSub_irrefl (A : D) : ¬ properSub A A :=
  fun ⟨h, hn⟩ => hn h

/-- Proper subset is asymmetric -/
theorem properSub_asymm {A B : D} (h : properSub A B) : ¬ properSub B A :=
  fun ⟨hba, _⟩ => h.2 hba

/-! ## Definition 3.1: Grain

  Given a data type R, a type G is a grain of R when:
  1. G ≅ R (isomorphism)
  2. No proper **structural** subtype of G is isomorphic to R
     (structural irreducibility)

  Clause (2) is the post-review repair. Under the earlier reading, where the
  quantifier ranged over `⊂_typ` (semantic proper subsets), the clause was
  *vacuously true*: if `G' ⊆_typ G` and `G' ≅ R ≅ G`, then the bijection
  `G' → G` is itself a surjection, so `G ⊆_typ G'` and `G'` was never a
  *proper* subset. Every type isomorphic to R then qualified as a grain and
  "the simplest type isomorphic to R" was never selected. Quantifying over
  `⊏` (component containment) instead makes the clause bite:
  `CustomerId ⊏ CustomerId × CustomerName` holds even though the two types
  are isomorphic, so the padded candidate is correctly rejected.

  Note: the definition does NOT require G ⊆_typ R. The grain may be external
  to R (e.g. `BalanceDate` for `Coll MonthlyBalance`). The canonical grain
  operator has `grain_sub` as an axiom in `GrainStructure`, but that is a
  property of the operator, not part of the grain definition — and it is
  stated with `sub`, never `ssub`, precisely so external grains survive.
-/

/-- **Structural irreducibility** (arXiv Def 3.1, clause 2, self-applied).
    `IsIrreducible G` holds when no proper structural subtype of G is
    isomorphic to G itself. Contrapositive form: `S ⊑ G` and `S ≅ G` force
    `G ⊑ S`.

    This is the paper's condition "`G[G] = G`" — G is a grain of itself —
    and it is what Grain Inference (Thm 5.10) takes as condition (iii). -/
def IsIrreducible (G : D) : Prop :=
  ∀ S : D, ssub S G → iso S G → ssub G S

/-- `IsGrainOf G R` holds when G satisfies the grain definition w.r.t. R
    (arXiv Def 3.1): isomorphism + *structural* irreducibility.
    No subset requirement — the grain may be external. -/
def IsGrainOf (G R : D) : Prop :=
  iso G R ∧
  (∀ S : D, ssub S G → iso S R → ssub G S)

/-- The canonical grain `G[R]` satisfies `IsGrainOf` — immediate from the axioms.

    This is also the mechanized form of the **Grain Existence Lemma**
    (arXiv Lemma 3.2, "every data type has a grain"): the operator `grain`
    supplies the witness, and this theorem discharges both clauses. -/
theorem grain_isGrainOf (R : D) : IsGrainOf (grain R) R :=
  ⟨grain_iso R, fun S => grain_irred R S⟩

/-- **Grain existence** (arXiv Lemma 3.2). Every data type has a grain. -/
theorem grain_exists (R : D) : ∃ G : D, IsGrainOf G R :=
  ⟨grain R, grain_isGrainOf R⟩

/-- If G is a grain of R, then G ≅ R -/
theorem IsGrainOf.toIso {G R : D} (h : IsGrainOf G R) : iso G R :=
  h.1

/-- If G is a grain of R, then no proper structural subtype of G is
    isomorphic to R -/
theorem IsGrainOf.toIrred {G R : D} (h : IsGrainOf G R) :
    ∀ S : D, ssub S G → iso S R → ssub G S :=
  h.2

/-! ### The grain definition factors as "isomorphic + irreducible"

  A consequence of the structural repair that the earlier encoding could not
  state: because clause (2) mentions R only through `iso S R`, and clause (1)
  gives `G ≅ R`, the two clauses are independent — irreducibility is a
  property of G *alone*.

  This is what the paper means by writing condition (iii) of Grain Inference
  as `G[G] = G` ("G is irreducible"), and it is what makes the definition
  non-circular. -/

/-- **Grain-hood factors:** `IsGrainOf G R ↔ G ≅ R ∧ IsIrreducible G`.

    Irreducibility is a property of G alone; the relation to R is carried
    entirely by the isomorphism clause. -/
theorem isGrainOf_iff_iso_and_irreducible {G R : D} :
    IsGrainOf G R ↔ (iso G R ∧ IsIrreducible G) := by
  constructor
  · rintro ⟨h_iso, h_irred⟩
    refine ⟨h_iso, fun S h_ssub h_iso_G => ?_⟩
    exact h_irred S h_ssub (iso_trans _ _ _ h_iso_G h_iso)
  · rintro ⟨h_iso, h_irred⟩
    refine ⟨h_iso, fun S h_ssub h_iso_R => ?_⟩
    exact h_irred S h_ssub (iso_trans _ _ _ h_iso_R (iso_symm _ _ h_iso))

/-- A grain of R is irreducible. -/
theorem IsGrainOf.toIrreducible {G R : D} (h : IsGrainOf G R) : IsIrreducible G :=
  (isGrainOf_iff_iso_and_irreducible.mp h).2

/-- Isomorphism plus irreducibility gives grain-hood. -/
theorem IsGrainOf.mk' {G R : D} (h_iso : iso G R) (h_irred : IsIrreducible G) :
    IsGrainOf G R :=
  isGrainOf_iff_iso_and_irreducible.mpr ⟨h_iso, h_irred⟩

/-- The canonical grain is irreducible. -/
theorem grain_irreducible (R : D) : IsIrreducible (grain R) :=
  (grain_isGrainOf R).toIrreducible

/-- **Grain-hood transfers along structural equality.**

    If `A` is a grain of `R` and `B` has exactly the same components as `A`
    (mutual `⊑`), then `B` is a grain of `R` too.

    Note what this replaces: grain-hood used to be transferred along a bare
    *isomorphism*. That is unsound once irreducibility is structural — two
    isomorphic types can differ in irreducibility, which is the whole content
    of the repair. Only structural equality transfers it. -/
theorem IsGrainOf.of_ssub_antisymm {A B R : D}
    (h : IsGrainOf A R) (h₁ : ssub A B) (h₂ : ssub B A) : IsGrainOf B R := by
  refine ⟨iso_trans _ _ _ (ssub_antisymm _ _ h₂ h₁) h.1, fun S h_ssub h_iso => ?_⟩
  exact ssub_trans _ _ _ h₂ (h.2 S (ssub_trans _ _ _ h_ssub h₂) h_iso)

/-- Every irreducible type is a grain of itself (arXiv: `G[G] = G`). -/
theorem IsIrreducible.self_grain {G : D} (h : IsIrreducible G) : IsGrainOf G G :=
  IsGrainOf.mk' (iso_refl G) h

end GrainTheory.Foundations
