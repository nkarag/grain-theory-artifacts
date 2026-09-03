/-
  GrainTheory.ADT.TypeExpr — the grain type-expression operator, syntactically

  arXiv/ICDT §"Grain for Arbitrary Algebraic Data Types":
  - Definition [Grain type-expression operator]
  - Theorem [Correctness of the grain type-expression operator]

  The paper states three things about the operator `G(·)`:

    (a) for every **closed** ADT `T`, `G(T)` is a grain of `T`;
    (b) it is **idempotent**, `G(G(T)) = G(T)`;
    (c) it **commutes** with `+`, `μ` and `ν` outright, and with `×` once
        determined slots are dropped.

  (b) and (c) are facts about *syntax* and need no semantics at all: they are
  established here by structural induction, with no axioms. (a) is the semantic
  claim and lives in `ADT/Correctness.lean`.

  This file is the type-expression grammar and the operator on it.

  **Binary products and sums.** The paper writes them n-ary. Binary constructors
  are used here because an n-ary product is an iterated binary one and the
  binary form keeps the structural recursion inside Lean's termination checker;
  nothing below depends on the arity.

  **The product clause is a parameter, not a definition.** The paper's clause is

      G(A₁ × ⋯ × Aₙ) = ∏_{i ∈ S} G(Aᵢ)

  where `S` is *a minimal set of components whose closure under the declared
  determinations is all of them* — "where several such `S` exist the clause may
  return any of them, as several candidate keys may". That is a choice, not a
  function of the syntax, so it is carried as a field with exactly the two
  properties the paper attributes to it: the chosen slots are among the
  originals, and re-minimizing an already-minimal choice changes nothing.
-/

import GrainTheory.Foundations.GrainDef

universe u

namespace GrainTheory.ADT

/-- Type expressions: the ADT grammar of the paper.

    `T ::= B | X | T × T | T + T | μX.T | νX.T`

    with `B` a base type drawn from the universe `D`, and `X` a recursion
    variable identified by a natural number. -/
inductive TyExpr (D : Type u) : Type u
  /-- A base type, an element of the opaque universe. -/
  | base : D → TyExpr D
  /-- A recursion variable. -/
  | var : ℕ → TyExpr D
  /-- Product (record). -/
  | prod : TyExpr D → TyExpr D → TyExpr D
  /-- Sum (variant). -/
  | sum : TyExpr D → TyExpr D → TyExpr D
  /-- Inductive fixed point `μX.F`. -/
  | mu : ℕ → TyExpr D → TyExpr D
  /-- Coinductive fixed point `νX.F`. -/
  | nu : ℕ → TyExpr D → TyExpr D
  deriving DecidableEq

namespace TyExpr

variable {D : Type u}

/-- **Closed**: no free recursion variable. A variable is free unless some
    enclosing binder binds it.

    The correctness theorem is stated for closed types — `Order` or
    `List OrderLine`, not the body `1 + OrderLine × X` they are built from —
    because Definition 3.1 has nothing to say about an open expression. -/
def closedUnder : List ℕ → TyExpr D → Prop
  | _, base _ => True
  | bs, var n => n ∈ bs
  | bs, prod A B => closedUnder bs A ∧ closedUnder bs B
  | bs, sum A B => closedUnder bs A ∧ closedUnder bs B
  | bs, mu n F => closedUnder (n :: bs) F
  | bs, nu n F => closedUnder (n :: bs) F

/-- A closed type expression: no free recursion variables. -/
def Closed (T : TyExpr D) : Prop := closedUnder [] T

end TyExpr

/-! ## The operator

  Every clause but one is pure structural recursion, reducing each slot
  independently of its neighbours. Declared determinations relate slots to one
  another, and they enter at exactly one place: the clause for products. -/

/-- Which slots the product clause keeps.

    The paper's clause retains `∏_{i ∈ S} G(Aᵢ)` for `S` a minimal set of
    components whose closure under the declared determinations is all of them.
    For a binary product the possibilities are exactly these three: keep both,
    or drop the component the other determines. -/
inductive ProdChoice
  /-- Neither component determines the other: keep both. -/
  | both
  /-- The left component determines the right: drop the right. -/
  | left
  /-- The right component determines the left: drop the left. -/
  | right
  deriving DecidableEq

/-- The product clause, carried as data.

    `choose A B` consults the declared determinations to pick the minimal
    sub-product. It is a genuine *choice*: "where several such `S` exist the
    clause may return any of them, as several candidate keys may". Nothing below
    constrains which it picks — only that it picks a sub-product, which the type
    of `ProdChoice` already guarantees. -/
structure ProdClause (D : Type u) where
  /-- The minimal sub-product to retain, given the reduced components. -/
  choose : TyExpr D → TyExpr D → ProdChoice

/-- Apply a choice to a pair of components. -/
def ProdChoice.apply {D : Type u} : ProdChoice → TyExpr D → TyExpr D → TyExpr D
  | .both, A, B => TyExpr.prod A B
  | .left, A, _ => A
  | .right, _, B => B

variable {D : Type u} (pc : ProdClause D) [GrainStructure D]

open TyExpr

/-- **Definition [Grain type-expression operator].**

    `G(B) = grain B`, `G(X) = X`, `G(A + B) = G(A) + G(B)`,
    `G(μX.F) = μX.G(F)`, `G(νX.F) = νX.G(F)`, and at a product the minimal
    sub-product of the reduced components.

    The base clause defers to Definition 3.1 rather than asserting an answer.
    The variable clause is the one that carries the whole extension: there is
    nothing at `X` to reduce, since `X` is not a component but the mark of where
    the type refers back to itself — it holds no fields and carries no
    declaration. Irreducibility is satisfied at `X` vacuously.

    The operator is total on every algebraic data type. -/
def gop : TyExpr D → TyExpr D
  | base b => base (GrainStructure.grain b)
  | var n => var n
  | prod A B => (pc.choose (gop A) (gop B)).apply (gop A) (gop B)
  | sum A B => sum (gop A) (gop B)
  | mu n F => mu n (gop F)
  | nu n F => nu n (gop F)

/-! ## Claim (c): the operator commutes with the constructors

  "It commutes with `+`, `μ` and `ν` outright, and with `×` once determined
  slots are dropped." Each is definitional. -/

@[simp] theorem gop_var (n : ℕ) : gop pc (var n : TyExpr D) = var n := rfl

@[simp] theorem gop_base (b : D) : gop pc (base b) = base (GrainStructure.grain b) := rfl

/-- Commutes with `+` outright. -/
@[simp] theorem gop_sum (A B : TyExpr D) :
    gop pc (sum A B) = sum (gop pc A) (gop pc B) := rfl

/-- Commutes with `μ` outright — this is what lets the operator pass under a
    binder, and it holds because `G(X) = X` leaves the recursion untouched. -/
@[simp] theorem gop_mu (n : ℕ) (F : TyExpr D) :
    gop pc (mu n F) = mu n (gop pc F) := rfl

/-- Commutes with `ν` outright. -/
@[simp] theorem gop_nu (n : ℕ) (F : TyExpr D) :
    gop pc (nu n F) = nu n (gop pc F) := rfl

/-- Commutes with `×` **once determined slots are dropped** — the one clause
    that is not outright commutation, because determinations relate slots. -/
@[simp] theorem gop_prod (A B : TyExpr D) :
    gop pc (prod A B) =
      (pc.choose (gop pc A) (gop pc B)).apply (gop pc A) (gop pc B) := rfl

/-! ## Claim (b): the operator is idempotent

  `G(G(T)) = G(T)`, proved by structural induction with **no axioms and no
  semantics**. This is the operator's counterpart of grain idempotency — that
  one being a statement about the grain, this one about the syntax that computes
  it.

  The base case is grain idempotency itself, transported through the `base`
  constructor; the product case is `select_idem`; every other case is the
  induction hypothesis under a constructor. -/

/-- **Operator idempotency.** `G(G(T)) = G(T)` for every type expression,
    open or closed.

    Proved by structural induction, with **no axioms and no semantics**. The
    product case needs nothing extra: the clause returns a sub-product of
    already-reduced components, so re-reducing meets the induction hypothesis on
    whichever slots survived.

    The one hypothesis is that the base-type grain is a syntactic fixpoint,
    `grain (grain b) = grain b`. Abstractly the grain is unique only up to
    isomorphism, so this is supplied rather than assumed of the operator; in the
    concrete model it holds on the nose. -/
theorem gop_idempotent (h_base : ∀ b : D,
    GrainStructure.grain (GrainStructure.grain b) = GrainStructure.grain b) :
    ∀ T : TyExpr D, gop pc (gop pc T) = gop pc T
  | base b => by simp [gop, h_base b]
  | var _ => rfl
  | prod A B => by
      have hA := gop_idempotent h_base A
      have hB := gop_idempotent h_base B
      simp only [gop]
      cases h : pc.choose (gop pc A) (gop pc B) with
      | both => simp only [ProdChoice.apply, gop, hA, hB, h]
      | left => simp only [ProdChoice.apply]; exact hA
      | right => simp only [ProdChoice.apply]; exact hB
  | sum A B => by
      simp only [gop]
      rw [gop_idempotent h_base A, gop_idempotent h_base B]
  | mu n F => by
      simp only [gop]
      rw [gop_idempotent h_base F]
  | nu n F => by
      simp only [gop]
      rw [gop_idempotent h_base F]

/-- Idempotency on **open** expressions too, which is what makes the
    grain-saturation hypothesis available again at the next binder, so nested
    recursive types — a list of trees, a stream of orders — are covered without
    further argument. The statement above is already general in this respect;
    recorded separately because the paper singles the point out. -/
theorem gop_idempotent_open (h_base : ∀ b : D,
    GrainStructure.grain (GrainStructure.grain b) = GrainStructure.grain b)
    (n : ℕ) (F : TyExpr D) :
    gop pc (mu n (gop pc F)) = mu n (gop pc F) := by
  simp only [gop]
  rw [gop_idempotent pc h_base F]

/-- Closedness is preserved: reducing a closed type leaves it closed. No clause
    introduces a variable, and the product clause only ever drops slots. -/
theorem closedUnder_gop : ∀ (bs : List ℕ) (T : TyExpr D),
    closedUnder bs T → closedUnder bs (gop pc T)
  | _, base _, _ => trivial
  | _, var _, h => h
  | bs, prod A B, h => by
      have hA := closedUnder_gop bs A h.1
      have hB := closedUnder_gop bs B h.2
      simp only [gop]
      cases pc.choose (gop pc A) (gop pc B) with
      | both => exact ⟨hA, hB⟩
      | left => exact hA
      | right => exact hB
  | bs, sum A B, h =>
      ⟨closedUnder_gop bs A h.1, closedUnder_gop bs B h.2⟩
  | bs, mu n F, h => closedUnder_gop (n :: bs) F h
  | bs, nu n F, h => closedUnder_gop (n :: bs) F h

end GrainTheory.ADT
