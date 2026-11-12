/-
  GrainTheory.Relations.GrainOrdering — Grain ordering (partial order)

  arXiv v4 `def:grain-ord` (Grain Ordering): R₁ ≤_g R₂ iff ∃ surjective f : G[R₁] ↠ G[R₂].

  Grain ordering arises in two ways, both yielding surjective functions:
  (1) Subset-based: G[R₂] ⊆_typ G[R₁] yields a surjective projection.
  (2) FD-based: a surjective functional dependency from G[R₁] to G[R₂]
      without field overlap (e.g., EmployeeId ↠ DepartmentId).

  In this abstract axiomatization, we encode grain ordering via (1):
  `grainLe R₁ R₂ := sub (grain R₂) (grain R₁)`. The subset case
  implies surjectivity (the projection is surjective), and all proof
  machinery (Armstrong axioms, GIT, equi-join) operates through this
  path. The FD-based case (2) cannot be expressed abstractly since
  DataType `D` carries no internal function types.

  arXiv v4 `thm:grain-partial-order` (Grain Ordering is a Partial Order):
  ≤_g is a partial order up to grain equivalence:
  reflexive, antisymmetric (up to ≅), and transitive.
-/

import GrainTheory.Basic
import GrainTheory.Foundations.Idempotency

namespace GrainTheory.Relations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-! ## Grain Equality (arXiv v4 `def:grain-eq` (Grain Equality), minimal) -/

/-- Grain equality: R₁ ≡_g R₂ iff G[R₁] ≅ G[R₂].
    Full development in LP-10; defined here for antisymmetry. -/
def grainEq (R₁ R₂ : D) : Prop := iso (grain R₁) (grain R₂)

scoped infixl:50 " ≡_g " => grainEq

/-! ## Grain Ordering (arXiv v4 `def:grain-ord` (Grain Ordering)) -/

/-- arXiv v4 `def:grain-ord` (Grain Ordering): Grain ordering. R₁ ≤_g R₂ iff ∃ surjective f : G[R₁]
    ↠ G[R₂].
    Encoded via the subset case: G[R₂] ⊆_typ G[R₁] (the projection is
    surjective because every field of G[R₂] exists in G[R₁]).
    "R₁ has lower grain (finer granularity) than R₂."
    Example: OrderDetail ≤_g Order, since G[Order] ⊆_typ G[OrderDetail]. -/
def grainLe (R₁ R₂ : D) : Prop := sub (grain R₂) (grain R₁)

scoped infixl:50 " ≤_g " => grainLe

/-! ## Partial Order Properties -/

/-- Grain ordering is reflexive: R ≤_g R -/
theorem grainLe_refl (R : D) : grainLe R R :=
  sub_refl (grain R)

/-- Grain ordering is antisymmetric up to grain equivalence:
    R₁ ≤_g R₂ → R₂ ≤_g R₁ → R₁ ≡_g R₂ -/
theorem grainLe_antisymm {R₁ R₂ : D}
    (h₁ : grainLe R₁ R₂) (h₂ : grainLe R₂ R₁) : grainEq R₁ R₂ :=
  sub_antisymm _ _ h₂ h₁

/-- Grain ordering is transitive: R₁ ≤_g R₂ → R₂ ≤_g R₃ → R₁ ≤_g R₃ -/
theorem grainLe_trans {R₁ R₂ R₃ : D}
    (h₁ : grainLe R₁ R₂) (h₂ : grainLe R₂ R₃) : grainLe R₁ R₃ :=
  sub_trans _ _ _ h₂ h₁

/-! ## arXiv v4 `thm:grain-partial-order` (Grain Ordering is a Partial Order)

  ≤_g is a partial order (up to isomorphism):
  - Reflexivity: R ≤_g R (identity is surjective).
  - Antisymmetry: R₁ ≤_g R₂ ∧ R₂ ≤_g R₁ → R₁ ≡_g R₂.
    Proof: surjective f : G[R₁] ↠ G[R₂] implies |G[R₁]| ≥ |G[R₂]|;
    surjective g : G[R₂] ↠ G[R₁] implies the reverse. Equal cardinality
    makes f a bijection, hence G[R₁] ≅ G[R₂].
    In the subset encoding: sub_antisymm gives iso directly.
  - Transitivity: R₁ ≤_g R₂ ∧ R₂ ≤_g R₃ → R₁ ≤_g R₃
    (composition of surjections is surjective).
-/

/-- arXiv v4 `thm:grain-partial-order` (Grain Ordering is a Partial Order): Grain ordering is a
    partial order
    (up to isomorphism). Bundles reflexivity, antisymmetry, and transitivity. -/
theorem grain_partial_order :
    (∀ (R : D), grainLe R R) ∧
    (∀ (R₁ R₂ : D), grainLe R₁ R₂ → grainLe R₂ R₁ → grainEq R₁ R₂) ∧
    (∀ (R₁ R₂ R₃ : D), grainLe R₁ R₂ → grainLe R₂ R₃ → grainLe R₁ R₃) :=
  ⟨grainLe_refl, fun _ _ h₁ h₂ => grainLe_antisymm h₁ h₂, fun _ _ _ h₁ h₂ => grainLe_trans h₁ h₂⟩

/-! ## Useful lemmas -/

/-- Grain ordering unfolds to sub on grains -/
theorem grainLe_iff (R₁ R₂ : D) : grainLe R₁ R₂ ↔ sub (grain R₂) (grain R₁) :=
  Iff.rfl

/-- Grain equality from ordering in both directions -/
theorem grainEq_of_le_le {R₁ R₂ : D}
    (h₁ : grainLe R₁ R₂) (h₂ : grainLe R₂ R₁) : grainEq R₁ R₂ :=
  grainLe_antisymm h₁ h₂

/-! ## Corollary: Grain Ordering Preservation -/

/-- Grain Ordering Preservation (corollary of arXiv v4 `thm:grain-idempotent` (Grain of a Grain,
    Idempotency)):
    R₁ ≤_g R₂ ⟺ G[R₁] ≤_g G[R₂].

    Both directions follow from idempotency G[G[R]] ≅ G[R],
    using iso_sub to transport the sub relation across the
    grain_idempotent isomorphism.

    (⟹) grainLe R₁ R₂ = sub (grain R₂) (grain R₁).
    Chain: grain(grain R₂) ⊆ grain R₂ ⊆ grain R₁ ≅ grain(grain R₁),
    so sub (grain(grain R₂)) (grain(grain R₁)) = grainLe (grain R₁) (grain R₂).

    (⟸) Same argument in reverse, using iso_symm of grain_idempotent. -/
theorem grainLe_preservation (R₁ R₂ : D) :
    grainLe R₁ R₂ ↔ grainLe (grain R₁) (grain R₂) := by
  constructor
  · intro h
    -- h : sub (grain R₂) (grain R₁)
    -- Goal: sub (grain (grain R₂)) (grain (grain R₁))
    -- Step 1: grain(grain R₂) ⊆ grain R₂ (grain_sub)
    -- Step 2: sub_trans gives grain(grain R₂) ⊆ grain R₁
    -- Step 3: iso_sub with grain_idempotent R₁ gives grain(grain R₂) ⊆ grain(grain R₁)
    exact iso_sub _ _ _
      (Foundations.grain_idempotent R₁)
      (sub_trans _ _ _ (grain_sub (grain R₂)) h)
  · intro h
    -- h : sub (grain (grain R₂)) (grain (grain R₁))
    -- Goal: sub (grain R₂) (grain R₁)
    -- Step 1: grain R₂ ⊆ grain(grain R₂)
    --   (from iso_sub: grain(grain R₂) ≅ grain R₂ → sub (grain R₂) (grain(grain R₂)))
    have h_embed : sub (grain R₂) (grain (grain R₂)) :=
      iso_sub _ _ _ (Foundations.grain_idempotent R₂) (sub_refl (grain R₂))
    -- Step 2: sub_trans gives grain R₂ ⊆ grain(grain R₁)
    have h_mid : sub (grain R₂) (grain (grain R₁)) :=
      sub_trans _ _ _ h_embed h
    -- Step 3: iso_sub with iso_symm(grain_idempotent R₁) gives grain R₂ ⊆ grain R₁
    exact iso_sub _ _ _
      (iso_symm _ _ (Foundations.grain_idempotent R₁))
      h_mid

end GrainTheory.Relations
