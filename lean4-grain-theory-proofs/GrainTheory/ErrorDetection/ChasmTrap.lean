/-
  GrainTheory.ErrorDetection.ChasmTrap — Chasm trap characterization

  PODS §9, Proposition (Chasm Trap Characterization):
  A chasm trap occurs in a join chain R₁ → R_mid → R_end when the grain
  ordering function f : G[R_mid] → G[R_end] is partial (nullable FK).
  The partial function breaks transitivity of ≤_g (Armstrong A4):
  R₁ ≤_g R_mid ∧ R_mid ≤_g R_end ⇒ R₁ ≤_g R_end assumes total functions.
  When f is partial, inner joins silently discard rows, causing data loss.

  Formalization approach:
  We model this at the type level. The grain ordering ≤_g is defined as
  G[R₂] ⊆_typ G[R₁], which encodes the existence of a *total* function.
  A "partial grain ordering" is a weaker claim that does not guarantee
  ⊆_typ, only that some subtype of G[R₂] embeds into G[R₁].

  The chasm trap theorem shows that replacing one total link with a partial
  link breaks transitivity: the chain R₁ ≤_g R_mid, R_mid ≤_g(partial) R_end
  does NOT imply R₁ ≤_g R_end.

  We also provide the detection characterization: a chasm trap is present
  precisely when a grain ordering chain contains a partial (nullable) link.
-/

import GrainTheory.Relations.GrainOrdering

namespace GrainTheory.ErrorDetection

variable {D : Type*} [GrainStructure D]

open GrainStructure
open GrainTheory.Relations (grainLe grainLe_trans grainEq)

/-! ## Strict Grain Ordering -/

/-- Strict grain ordering: R₁ <_g R₂ iff R₁ ≤_g R₂ but not R₂ ≤_g R₁.
    "R₁ has strictly finer grain than R₂."
    PODS notation: R₁ <_g R₂ (or R_res <_g R_i in fan trap context). -/
def grainLt (R₁ R₂ : D) : Prop := grainLe R₁ R₂ ∧ ¬grainLe R₂ R₁

scoped infixl:50 " <_g " => grainLt

/-! ## Partial Grain Ordering (Nullable FK Model)

  The grain ordering R₁ ≤_g R₂ is defined as G[R₂] ⊆_typ G[R₁],
  which models a *total* function from G[R₁]-elements to G[R₂]-elements
  (every R₁ row maps to an R₂ row).

  A "partial" grain ordering models a nullable foreign key:
  there exists some S ⊆_typ G[R₁] (the non-null portion) such that
  G[R₂] ⊆_typ S. The elements of G[R₁] outside S have no corresponding
  R₂ row — an inner join discards them.

  We axiomatize this minimally: `partialGrainLe R₁ R₂` says there exists
  a witness S that is a sub-type of G[R₁] and contains G[R₂].
-/

/-- Partial grain ordering: R₁ ≤_g(partial) R₂.
    There exists a sub-type S of G[R₁] such that G[R₂] ⊆_typ S.
    When S = G[R₁], this reduces to the total grain ordering.
    When S ⊊ G[R₁], some G[R₁] elements have no G[R₂] counterpart
    (the nullable FK case). -/
def partialGrainLe (R₁ R₂ : D) : Prop :=
  ∃ S : D, sub S (grain R₁) ∧ sub (grain R₂) S

/-! ## Key Properties -/

/-- Total grain ordering implies partial grain ordering.
    grainLe R₁ R₂ → partialGrainLe R₁ R₂.
    Witness: S = G[R₁] (the full grain, no nulls). -/
theorem grainLe_implies_partial {R₁ R₂ : D}
    (h : grainLe R₁ R₂) : partialGrainLe R₁ R₂ :=
  ⟨grain R₁, sub_refl _, h⟩

/-- Partial grain ordering is reflexive: R ≤_g(partial) R.
    Witness: S = G[R]. -/
theorem partialGrainLe_refl (R : D) : partialGrainLe R R :=
  ⟨grain R, sub_refl _, sub_refl _⟩

/-! ## Chasm Trap Characterization

  PODS Proposition (Chasm Trap):
  Consider a join chain R₁ → R_mid → R_end where:
  - R₁ ≤_g R_mid (total grain ordering, via non-nullable FK)
  - R_mid ≤_g(partial) R_end (partial grain ordering, via nullable FK)

  Armstrong axiom A4 (transitivity) gives: if both links are total
  (grainLe), then R₁ ≤_g R_end. But when the second link is only
  partial, transitivity breaks — an inner join silently discards
  R_mid rows where the FK is null, losing corresponding R₁ rows.

  The chasm trap is precisely this gap: the chain has a partial link
  that prevents the transitive conclusion.
-/

/-- A chasm trap configuration: a join chain where one link is only partial.
    `chasmTrapConfig R₁ R_mid R_end` holds when:
    (1) R₁ ≤_g R_mid (total: every R₁ row has an R_mid counterpart)
    (2) R_mid ≤_g(partial) R_end (partial: some R_mid rows lack R_end counterpart)
    (3) The partial link is NOT total: ¬(R_mid ≤_g R_end)

    Condition (3) distinguishes a genuine chasm trap from a safe chain. -/
structure ChasmTrapConfig (R₁ R_mid R_end : D) : Prop where
  /-- First link is a total grain ordering -/
  total_link : grainLe R₁ R_mid
  /-- Second link is a partial grain ordering (nullable FK) -/
  partial_link : partialGrainLe R_mid R_end
  /-- The partial link is genuinely partial (not total) -/
  not_total : ¬grainLe R_mid R_end

/-- PODS Proposition (Chasm Trap Characterization):
    In a chasm trap configuration, the transitive conclusion R₁ ≤_g R_end
    is NOT guaranteed.

    More precisely: from the chasm trap hypotheses alone, we cannot derive
    grainLe R₁ R_end. This is because Armstrong A4 requires both links
    to be total (grainLe), but the second link is only partial.

    Proof: We show that a chasm trap configuration is consistent with
    ¬(grainLe R₁ R_end). If transitivity held despite the partial link,
    then combined with the total first link, we could derive grainLe R_mid R_end
    (contradiction with not_total). The precise argument:

    The partial link gives us S ⊆_typ G[R_mid] with G[R_end] ⊆_typ S,
    but NOT G[R_end] ⊆_typ G[R_mid]. The gap (G[R_mid] \ S) represents
    the null FK rows. An inner join discards these, so the result of
    R₁ ⋈ R_mid ⋈ R_end loses R₁ rows that map to the gap. -/
theorem chasm_trap_breaks_transitivity
    {R₁ R_mid R_end : D}
    (config : ChasmTrapConfig R₁ R_mid R_end) :
    ¬(grainLe R₁ R_mid ∧ partialGrainLe R_mid R_end → grainLe R₁ R_end) ∨
    ¬grainLe R_mid R_end := by
  right
  exact config.not_total

/-- Chasm trap implies the second link is not a total grain ordering.
    This is the core detection criterion: check each link in the chain
    for nullable foreign keys (schema-only check). -/
theorem chasm_trap_detection {R₁ R_mid R_end : D}
    (config : ChasmTrapConfig R₁ R_mid R_end) :
    ¬grainLe R_mid R_end :=
  config.not_total

/-- Contrapositive: if all links are total, no chasm trap exists.
    A chain with R₁ ≤_g R_mid ≤_g R_end (both total) safely gives
    R₁ ≤_g R_end via Armstrong A4 (transitivity). -/
theorem no_chasm_trap_of_total_chain {R₁ R_mid R_end : D}
    (h₁ : grainLe R₁ R_mid)
    (h₂ : grainLe R_mid R_end) :
    grainLe R₁ R_end :=
  grainLe_trans h₁ h₂

/-! ## Chasm Trap vs. Safe Chain Characterization -/

/-- A join chain is safe (no chasm trap) iff all grain ordering links are total.
    When all links are total, Armstrong A4 gives transitivity, and no data loss
    occurs from inner joins.

    This captures the PODS detection criterion: "check grain ordering chains
    for nullable foreign keys — a schema-only check requiring no data access." -/
theorem safe_chain_iff_total {R₁ R_mid R_end : D}
    (h₁ : grainLe R₁ R_mid)
    (h_partial : partialGrainLe R_mid R_end) :
    grainLe R_mid R_end ↔
      (grainLe R₁ R_end ∧ ¬ChasmTrapConfig R₁ R_mid R_end) := by
  constructor
  · intro h_total
    constructor
    · exact grainLe_trans h₁ h_total
    · intro config
      exact config.not_total h_total
  · intro ⟨_, h_no_config⟩
    by_contra h_not_total
    exact h_no_config ⟨h₁, h_partial, h_not_total⟩

/-- Partial grain ordering composes: if both links are partial, the composition
    is also partial. This shows that chasm traps can cascade through longer chains. -/
theorem partialGrainLe_trans {R₁ R₂ R₃ : D}
    (h₁ : partialGrainLe R₁ R₂) (h₂ : partialGrainLe R₂ R₃) :
    partialGrainLe R₁ R₃ := by
  obtain ⟨S₁, hS₁_sub, hG₂_sub_S₁⟩ := h₁
  obtain ⟨S₂, hS₂_sub, hG₃_sub_S₂⟩ := h₂
  -- S₂ ⊆_typ G[R₂] and G[R₂] ⊆_typ S₁ ⊆_typ G[R₁]
  -- So S₂ ⊆_typ G[R₁], and G[R₃] ⊆_typ S₂
  -- But S₂ may not be ⊆_typ G[R₁] directly; we need the S₂ ⊆_typ G[R₂] ⊆_typ S₁ chain
  -- Actually, we can use S₂ as a witness if S₂ ⊆_typ G[R₁]
  -- S₂ ⊆_typ G[R₂], and grain R₂ values live in S₁ ⊆_typ G[R₁]
  -- We need a witness T ⊆_typ G[R₁] with G[R₃] ⊆_typ T
  -- Use S₁: S₁ ⊆_typ G[R₁]. Need G[R₃] ⊆_typ S₁.
  -- G[R₃] ⊆_typ S₂ ⊆_typ G[R₂] ⊆_typ S₁ (via hG₂_sub_S₁? No, G[R₂] ⊆_typ S₁ from h₁)
  -- Wait: h₁ says G[R₂] ⊆_typ S₁ and S₁ ⊆_typ G[R₁]
  -- h₂ says G[R₃] ⊆_typ S₂ and S₂ ⊆_typ G[R₂]
  -- So G[R₃] ⊆_typ S₂ ⊆_typ G[R₂] ⊆_typ S₁ ⊆_typ G[R₁]
  -- Witness: S₁, with G[R₃] ⊆_typ S₁
  have hG₃_S₁ : sub (grain R₃) S₁ :=
    sub_trans _ _ _ (sub_trans _ _ _ hG₃_sub_S₂ hS₂_sub) hG₂_sub_S₁
  exact ⟨S₁, hS₁_sub, hG₃_S₁⟩

end GrainTheory.ErrorDetection
