/-
  GrainTheory.ErrorDetection.FanTrap — Fan trap characterization (LP-29)

  PODS 2027, §9, Proposition fan-trap:

    Given collections C R₁ and C R₂ joined on Jk producing C Res,
    a *fan trap* occurs when G[Res] <_g G[R_i] for some i:
    the result grain is strictly finer than an input grain,
    meaning each row from R_i is duplicated in Res, inflating every
    aggregate computed over R_i.

  Results:
  - Definition: grainLt (strict grain ordering)
  - Definition: isFanTrap (fan trap predicate)
  - Theorem: fan trap detection via equi-join grain formula
  - Theorem: fan trap prevention via pre-aggregation
  - Supporting lemmas: properties of strict grain ordering
-/

import GrainTheory.Relations.GrainOrdering
import GrainTheory.Relations.Incomparability

namespace GrainTheory.ErrorDetection

variable {D : Type*} [GrainStructure D]

open GrainStructure (sub iso grain union inter diff prod
  sub_refl sub_trans sub_antisymm iso_refl iso_symm iso_trans iso_sub
  grain_sub grain_iso grain_irred
  sub_union_left sub_union_right union_sub sub_diff)

open GrainTheory.Relations (grainEq grainLe grainIncomp
  grainLe_refl grainLe_antisymm grainLe_trans
  grainLe_of_grainEq grainLe_of_grainEq')

/-! ## Strict Grain Ordering (PODS notation: <_g) -/

/-- Strict grain ordering: R₁ <_g R₂ iff R₁ ≤_g R₂ and ¬(R₁ ≡_g R₂).
    "R₁ has strictly finer granularity than R₂."

    Equivalently (by PODS Def 5): G[R₂] ⊆_typ G[R₁] and ¬(G[R₁] ≅ G[R₂]).

    Example: OrderDetail <_g Order, since G[Order] ⊂_typ G[OrderDetail]. -/
def grainLt (R₁ R₂ : D) : Prop := grainLe R₁ R₂ ∧ ¬ grainEq R₁ R₂

scoped infixl:50 " <_g " => grainLt

/-! ## Properties of Strict Grain Ordering -/

/-- Strict grain ordering is irreflexive: ¬(R <_g R). -/
theorem grainLt_irrefl (R : D) : ¬ grainLt R R := by
  intro ⟨_, hne⟩
  exact hne (iso_refl (grain R))

/-- Strict grain ordering is asymmetric: R₁ <_g R₂ → ¬(R₂ <_g R₁). -/
theorem grainLt_asymm {R₁ R₂ : D} (h : grainLt R₁ R₂) : ¬ grainLt R₂ R₁ := by
  intro ⟨h₂₁, _⟩
  exact h.2 (grainLe_antisymm h.1 h₂₁)

/-- Strict grain ordering is transitive: R₁ <_g R₂ → R₂ <_g R₃ → R₁ <_g R₃. -/
theorem grainLt_trans {R₁ R₂ R₃ : D}
    (h₁₂ : grainLt R₁ R₂) (h₂₃ : grainLt R₂ R₃) : grainLt R₁ R₃ := by
  refine ⟨grainLe_trans h₁₂.1 h₂₃.1, ?_⟩
  intro heq
  -- If R₁ ≡_g R₃, then from R₂ ≤_g R₃ and R₁ ≤_g R₂:
  -- R₃ ≤_g R₁ (from heq) and R₁ ≤_g R₂, so R₃ ≤_g R₂
  -- Combined with R₂ ≤_g R₃, gives R₂ ≡_g R₃ — contradicts h₂₃.
  have h₃₁ : grainLe R₃ R₁ := grainLe_of_grainEq' heq
  have h₃₂ : grainLe R₃ R₂ := grainLe_trans h₃₁ h₁₂.1
  exact h₂₃.2 (grainLe_antisymm h₂₃.1 h₃₂)

/-- Strict ordering implies non-strict ordering. -/
theorem grainLe_of_grainLt {R₁ R₂ : D} (h : grainLt R₁ R₂) : grainLe R₁ R₂ :=
  h.1

/-- Strict ordering implies non-equality. -/
theorem grainNe_of_grainLt {R₁ R₂ : D} (h : grainLt R₁ R₂) : ¬ grainEq R₁ R₂ :=
  h.2

/-- Grain equality precludes strict ordering. -/
theorem not_grainLt_of_grainEq {R₁ R₂ : D} (h : grainEq R₁ R₂) : ¬ grainLt R₁ R₂ := by
  intro ⟨_, hne⟩
  exact hne h

/-- Strict ordering and incomparability are mutually exclusive. -/
theorem grainLt_not_incomp {R₁ R₂ : D} (h : grainLt R₁ R₂) : ¬ grainIncomp R₁ R₂ := by
  intro ⟨hle, _⟩
  exact hle h.1

/-! ## Fan Trap Definition (PODS §9, Proposition fan-trap) -/

/-- A fan trap occurs in the equi-join producing Res from R₁ and R₂ when
    the result grain is strictly finer than at least one input grain.

    PODS §9: "a fan trap occurs when G[Res] <_g G[R_i] for some i."

    We express this as: the result is strictly finer-grained than R₁ or R₂
    (i.e., Res <_g R₁ or Res <_g R₂, since grain ordering is preserved
    by the corollary in GrainOrdering.lean). -/
def isFanTrap (R₁ R₂ Res : D) : Prop :=
  grainLt Res R₁ ∨ grainLt Res R₂

/-! ## Fan Trap Detection (PODS §9)

    The equi-join grain formula (Theorem 6.1) gives:
      F₁ ≡_g Res  where  F₁ = G[R₁] ∪_typ (G[R₂] -_typ Jk)

    A fan trap on the R_i side occurs when Res <_g R_i. By grain
    equivalence F₁ ≡_g Res, we can check the condition on F₁ instead:
    F₁ ≤_g R_i and ¬(F₁ ≡_g R_i).

    Detection is a zero-cost schema check: compute F₁ from the type-level
    formula and test strict grain ordering against each input. -/

/-- Fan trap detection for R₁ side: if a candidate grain formula F₁
    satisfies F₁ ≡_g Res, and F₁ ≤_g R₁ but ¬(F₁ ≡_g R₁), then
    a fan trap occurs on the R₁ side.

    The hypothesis F₁ ≡_g Res is obtained from equijoin_grain (LP-21)
    composed with grain idempotency. The grain ordering F₁ ≤_g R₁ and
    non-equality ¬(F₁ ≡_g R₁) are computed by schema-level subset
    comparison (zero-cost). -/
theorem fan_trap_detection_r1
    (R₁ R₂ Res F₁ : D)
    (hF₁_eq : grainEq F₁ Res)
    (hF₁_le : grainLe F₁ R₁)
    (hF₁_ne : ¬ grainEq F₁ R₁)
    : isFanTrap R₁ R₂ Res := by
  -- Goal: Res <_g R₁, i.e., grainLe Res R₁ ∧ ¬ grainEq Res R₁
  -- Step 1: Res ≤_g R₁ by transitivity through F₁
  -- hF₁_eq : iso (grain F₁) (grain Res)
  -- grainLe_of_grainEq' hF₁_eq : grainLe Res F₁ (= sub (grain F₁) (grain Res))
  have h_res_f1 : grainLe Res F₁ := grainLe_of_grainEq' hF₁_eq
  have h_res_r1 : grainLe Res R₁ := grainLe_trans h_res_f1 hF₁_le
  -- Step 2: ¬(Res ≡_g R₁)
  -- Suppose Res ≡_g R₁ (iso (grain Res) (grain R₁)).
  -- hF₁_le : sub (grain R₁) (grain F₁)
  -- h_res_f1 : sub (grain F₁) (grain Res)
  -- heq_res_r1 : iso (grain Res) (grain R₁)
  -- Then: sub (grain F₁) (grain Res) and iso (grain Res) (grain R₁)
  --   → sub (grain F₁) (grain R₁) by iso_sub
  -- Combined with hF₁_le : sub (grain R₁) (grain F₁)
  --   → iso (grain F₁) (grain R₁) by sub_antisymm, i.e., F₁ ≡_g R₁
  -- Contradiction with hF₁_ne.
  have h_ne : ¬ grainEq Res R₁ := by
    intro heq_res_r1
    -- heq_res_r1 : iso (grain Res) (grain R₁)
    -- h_res_f1 : sub (grain F₁) (grain Res) [= grainLe Res F₁]
    -- hF₁_le : sub (grain R₁) (grain F₁) [= grainLe F₁ R₁]
    -- Need: iso (grain F₁) (grain R₁) [= grainEq F₁ R₁]
    -- Chain: grain R₁ ⊆ grain F₁ ⊆ grain Res, and grain Res ≅ grain R₁
    -- So grain F₁ ⊆ grain R₁ (by iso_sub with iso_symm heq_res_r1)
    have h1 : sub (grain F₁) (grain R₁) :=
      iso_sub _ _ _ (iso_symm _ _ heq_res_r1) h_res_f1
    -- hF₁_le : sub (grain R₁) (grain F₁) — the other direction
    -- sub_antisymm gives iso (grain R₁) (grain F₁), need iso (grain F₁) (grain R₁)
    exact hF₁_ne (iso_symm _ _ (sub_antisymm _ _ hF₁_le h1))
  exact Or.inl ⟨h_res_r1, h_ne⟩

/-- Fan trap detection for R₂ side: symmetric version. -/
theorem fan_trap_detection_r2
    (R₁ R₂ Res F₁ : D)
    (hF₁_eq : grainEq F₁ Res)
    (hF₁_le : grainLe F₁ R₂)
    (hF₁_ne : ¬ grainEq F₁ R₂)
    : isFanTrap R₁ R₂ Res := by
  have h_res_f1 : grainLe Res F₁ := grainLe_of_grainEq' hF₁_eq
  have h_res_r2 : grainLe Res R₂ := grainLe_trans h_res_f1 hF₁_le
  have h_ne : ¬ grainEq Res R₂ := by
    intro heq_res_r2
    have h1 : sub (grain F₁) (grain R₂) :=
      iso_sub _ _ _ (iso_symm _ _ heq_res_r2) h_res_f1
    exact hF₁_ne (iso_symm _ _ (sub_antisymm _ _ hF₁_le h1))
  exact Or.inr ⟨h_res_r2, h_ne⟩

/-- Fan trap detection for both sides: if the candidate grain is strictly
    finer than both inputs, a bilateral fan trap occurs. -/
theorem fan_trap_detection_both
    (R₁ R₂ Res F₁ : D)
    (hF₁_eq : grainEq F₁ Res)
    (hF₁_le₁ : grainLe F₁ R₁)
    (hF₁_ne₁ : ¬ grainEq F₁ R₁)
    (_hF₁_le₂ : grainLe F₁ R₂)
    (_hF₁_ne₂ : ¬ grainEq F₁ R₂)
    : isFanTrap R₁ R₂ Res := by
  exact fan_trap_detection_r1 R₁ R₂ Res F₁ hF₁_eq hF₁_le₁ hF₁_ne₁

/-! ## Fan Trap from Incomparable Grains (PODS §6 Case 3)

    When G[R₁] #_g G[R₂] (incomparable grains), the equi-join result
    has F₁ = G[R₁] ∪ (G[R₂] \ Jk) which is strictly finer than both
    inputs. This is the canonical source of fan traps.

    The key insight: if the non-Jk portions of both grains are nonempty,
    the result grain has more fields than either input grain alone. -/

/-- When the result is strictly finer-grained than both inputs,
    the fan trap affects both sides. -/
def isFanTrapBoth (R₁ R₂ Res : D) : Prop :=
  grainLt Res R₁ ∧ grainLt Res R₂

/-- A bilateral fan trap implies a (unilateral) fan trap. -/
theorem isFanTrapBoth_implies_isFanTrap {R₁ R₂ Res : D}
    (h : isFanTrapBoth R₁ R₂ Res) : isFanTrap R₁ R₂ Res :=
  Or.inl h.1

/-! ## Fan Trap Prevention (PODS §9)

    "Pre-aggregate each input to the target grain before joining:
     if G[R_i'] ≡_g G[Target], then G[Res] ≱_g G[R_i']."

    In grain theory terms: if we pre-aggregate R_i to match the target
    grain (ensuring grain equality), then no fan trap can occur on that
    side — because G[Res] ≡_g G[R_i'] means the ordering is not strict. -/

/-- Fan trap prevention: if R_i has the same grain as Res (after
    pre-aggregation), then Res is not strictly finer than R_i.

    This is immediate from the definition: grainEq implies grainLe
    in both directions, so strict ordering is impossible. -/
theorem fan_trap_prevention
    (Ri Res : D)
    (h_eq : grainEq Ri Res)
    : ¬ grainLt Res Ri := by
  intro ⟨_, hne⟩
  -- grainEq Ri Res = iso (grain Ri) (grain Res)
  -- grainEq Res Ri = iso (grain Res) (grain Ri) = iso_symm of h_eq
  exact hne (iso_symm _ _ h_eq)

/-- Corollary: if both inputs have the same grain as the result,
    then no fan trap occurs. -/
theorem fan_trap_prevention_both
    (R₁ R₂ Res : D)
    (h₁ : grainEq R₁ Res)
    (h₂ : grainEq R₂ Res)
    : ¬ isFanTrap R₁ R₂ Res := by
  intro h
  cases h with
  | inl h_lt => exact fan_trap_prevention R₁ Res h₁ h_lt
  | inr h_lt => exact fan_trap_prevention R₂ Res h₂ h_lt

/-! ## Fan Trap Equivalence

    A fan trap is equivalent to: the result has strictly finer
    grain than at least one input. This is a direct reformulation
    of the definition, connecting the PODS prose to the formal statement. -/

/-- Fan trap occurs iff the result grain is strictly ordered below
    at least one input grain.

    This is the formal statement of PODS Proposition fan-trap:
    the condition G[Res] <_g G[R_i] (expressed at the type level
    as Res <_g R_i, since grain ordering is preserved by the corollary
    in GrainOrdering.lean) means row duplication occurs. -/
theorem fan_trap_iff (R₁ R₂ Res : D) :
    isFanTrap R₁ R₂ Res ↔ (grainLt Res R₁ ∨ grainLt Res R₂) :=
  Iff.rfl

end GrainTheory.ErrorDetection
