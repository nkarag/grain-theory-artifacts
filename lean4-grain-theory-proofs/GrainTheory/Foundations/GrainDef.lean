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

/-- Proper type subset: A ⊂_typ B ≡ A ⊆_typ B ∧ ¬(B ⊆_typ A) (PODS Def 2) -/
def properSub (A B : D) : Prop :=
  sub A B ∧ ¬ sub B A

scoped infixl:50 " ⊂_typ " => properSub

/-- Proper subset implies subset -/
theorem properSub_sub {A B : D} (h : properSub A B) : sub A B :=
  h.1

/-- Proper subset is irreflexive -/
theorem properSub_irrefl (A : D) : ¬ properSub A A :=
  fun ⟨h, hn⟩ => hn h

/-- Proper subset is asymmetric -/
theorem properSub_asymm {A B : D} (h : properSub A B) : ¬ properSub B A :=
  fun ⟨hba, _⟩ => h.2 hba

/-! ## Definition 3: Grain

  Given a data type R, the grain of R (denoted G[R]) is a type satisfying:
  1. G[R] ≅ R (isomorphism)
  2. No proper subset of G[R] is isomorphic to R (irreducibility)

  Note: the PODS paper definition does NOT require G[R] ⊆_typ R. The grain
  may be external to R (e.g., BalanceDate for MonthlyBalance). The canonical
  grain operator has `grain_sub` as an axiom in GrainStructure, but that is
  a property of the operator, not part of the grain definition.

  The `IsGrainOf` predicate packages these two properties, so that
  downstream proofs (e.g., uniqueness) can reason about arbitrary grains.
-/

/-- `IsGrainOf G R` holds when G satisfies the grain definition w.r.t. R (PODS Def 3):
    isomorphism + irreducibility. No subset requirement — the grain may be external. -/
def IsGrainOf (G R : D) : Prop :=
  iso G R ∧
  (∀ S : D, sub S G → iso S R → sub G S)

/-- The canonical grain `G[R]` satisfies `IsGrainOf` — immediate from the axioms. -/
theorem grain_isGrainOf (R : D) : IsGrainOf (grain R) R :=
  ⟨grain_iso R, fun S => grain_irred R S⟩

/-- If G is a grain of R, then G ≅ R -/
theorem IsGrainOf.toIso {G R : D} (h : IsGrainOf G R) : iso G R :=
  h.1

/-- If G is a grain of R, then no proper subset of G is isomorphic to R -/
theorem IsGrainOf.toIrred {G R : D} (h : IsGrainOf G R) :
    ∀ S : D, sub S G → iso S R → sub G S :=
  h.2

end GrainTheory.Foundations
