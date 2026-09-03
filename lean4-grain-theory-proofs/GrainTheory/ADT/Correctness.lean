/-
  GrainTheory.ADT.Correctness — the operator computes the grain

  arXiv/ICDT §"Grain for Arbitrary Algebraic Data Types",
  Theorem [Correctness of the grain type-expression operator]:

  > For every closed algebraic data type `T`, `G(T)` is a grain of `T` in the
  > sense of Definition 3.1: it is isomorphic to `T` and irreducible.

  The paper proves this by structural induction, "and the induction passes under
  binders, where the body is an open expression and Definition 3.1 has nothing
  to say". This file mechanizes that induction.

  ## What the induction rests on

  Three inputs are isolated rather than proved here, each for a stated reason.

  1. **`mu_congr` / `nu_congr`** — the fixed-point congruence. The paper's `μ`
     case assembles the induction hypotheses into a natural isomorphism of
     polynomial functors and then cites: *"Naturally isomorphic polynomial
     functors have isomorphic initial algebras"* (Bird & de Moor). This is that
     citation, and it is the one genuinely external mathematical input.

     **Honest caveat.** `D` is an opaque universe with no morphisms, so
     *naturality* cannot be stated here. The axiom is therefore phrased
     pointwise — isomorphic bodies give isomorphic fixed points — which is
     **stronger** than the categorical result it stands for. Closing that gap
     needs a development of polynomial functors that this abstraction cannot
     express.

  2. **`mu_irred` / `nu_irred`** — that `μ` and `ν` carry the *irreducibility*
     clause through, not only the isomorphism clause. The paper asserts both
     ("the constructors `μ` and `ν` carry both clauses of Definition 3.1 through
     unchanged") on the same grounds.

  3. **`choose_sound`** — that the product clause returns a grain of the
     product. The paper discharges this by citing Theorem [Grain of products
     and sums] and, where a determination holds, the Grain Inference theorem:
     *"That clause is Theorem [Grain of products and sums] placed where the
     recursion can reach it."* Both are mechanized elsewhere in this
     development, so this is a hypothesis of the clause rather than a new
     assumption about the world.

  Everything else — the recursion, the passage under binders, the interaction of
  the clauses — is machine-checked below.
-/

import GrainTheory.ADT.TypeExpr
import GrainTheory.Foundations.MultipleGrains

universe u

namespace GrainTheory.ADT

open TyExpr GrainStructure GrainTheory.Foundations

/-- An environment sending recursion variables to types. -/
abbrev Env (D : Type u) := ℕ → D

/-- Rebind one variable. -/
def Env.update {D : Type u} (ρ : Env D) (n : ℕ) (Y : D) : Env D :=
  fun m => if m = n then Y else ρ m

/-- `GrainStructure` extended with the two fixed-point constructors and the
    principles the paper's `μ`/`ν` cases cite. -/
class ADTStructure (D : Type u) extends GrainStructure D where
  /-- Inductive fixed point: the initial algebra of the body. -/
  muD : (D → D) → D
  /-- Coinductive fixed point: the final coalgebra of the body. -/
  nuD : (D → D) → D
  /-- **Bird & de Moor.** Isomorphic bodies have isomorphic initial algebras.
      See the caveat in this file's header: stated pointwise because `D` has no
      morphisms with which to say *naturally*. -/
  mu_congr : ∀ F G : D → D, (∀ Y, iso (F Y) (G Y)) → iso (muD F) (muD G)
  /-- Dually, for final coalgebras. -/
  nu_congr : ∀ F G : D → D, (∀ Y, iso (F Y) (G Y)) → iso (nuD F) (nuD G)
  /-- `μ` carries the irreducibility clause through.

      Note the hypothesis: the body must be irreducible whenever the recursion
      variable is instantiated by an **irreducible** type — not at every
      instantiation whatever. That restriction is forced, and it is the paper's
      own observation: *"The hypothesis on `σ` is never an obligation in
      practice, because it discharges itself at the binder: there `X` is
      instantiated by `μX.G(F)`, which is its own grain by the idempotence half
      of the lemma."* Quantifying over arbitrary `Y` would be false — an
      arbitrary type is not its own grain — and the mechanization refuses it. -/
  mu_irred : ∀ F : D → D,
    (∀ Y, Foundations.IsIrreducible Y → Foundations.IsIrreducible (F Y)) →
      Foundations.IsIrreducible (muD F)
  /-- Dually, for `ν`. -/
  nu_irred : ∀ F : D → D,
    (∀ Y, Foundations.IsIrreducible Y → Foundations.IsIrreducible (F Y)) →
      Foundations.IsIrreducible (nuD F)

variable {D : Type u} [ADTStructure D]

open ADTStructure

/-- Interpretation of a type expression in an environment. -/
def interp (pc : ProdClause D) : TyExpr D → Env D → D
  | base b, _ => b
  | var n, ρ => ρ n
  | TyExpr.prod A B, ρ => GrainStructure.prod (interp pc A ρ) (interp pc B ρ)
  | TyExpr.sum A B, ρ => GrainStructure.sum (interp pc A ρ) (interp pc B ρ)
  | TyExpr.mu n F, ρ => muD (fun Y => interp pc F (ρ.update n Y))
  | TyExpr.nu n F, ρ => nuD (fun Y => interp pc F (ρ.update n Y))

/-- The product clause is **sound**: what it keeps is a grain of what it was
    given. Discharged in the paper by Theorem [Grain of products and sums] and,
    where a determination holds, by Grain Inference. -/
def ProdClause.Sound (pc : ProdClause D) : Prop :=
  ∀ (A B : TyExpr D) (ρ : Env D),
    IsGrainOf (interp pc ((pc.choose A B).apply A B) ρ)
              (interp pc (TyExpr.prod A B) ρ)

/-! ## The isomorphism clause

  `G(T) ≅ T`, for **every** expression and **every** environment — open
  expressions included, and with no hypothesis on the environment.

  That generality is what makes the `μ` case work: `mu_congr` needs the
  isomorphism at *every* instantiation `Y` of the recursion variable, not only
  at grain-saturated ones. It is available because the variable clause
  `G(X) = X` returns the environment's value untouched, so both sides agree
  there by reflexivity whatever the environment holds. -/

theorem interp_gop_iso (pc : ProdClause D) (h_sound : pc.Sound) :
    ∀ (T : TyExpr D) (ρ : Env D), iso (interp pc (gop pc T) ρ) (interp pc T ρ)
  | base b, _ => grain_iso b
  | var n, _ => iso_refl _
  | TyExpr.prod A B, ρ => by
      -- the clause returns a grain of the reduced product, which is isomorphic
      -- to the reduced product, which is isomorphic to the original
      have hA := interp_gop_iso pc h_sound A ρ
      have hB := interp_gop_iso pc h_sound B ρ
      have h1 : iso (interp pc (gop pc (TyExpr.prod A B)) ρ)
          (interp pc (TyExpr.prod (gop pc A) (gop pc B)) ρ) :=
        (h_sound (gop pc A) (gop pc B) ρ).1
      exact iso_trans _ _ _ h1 (prod_iso _ _ _ _ hA hB)
  | TyExpr.sum A B, ρ => by
      exact sum_iso _ _ _ _ (interp_gop_iso pc h_sound A ρ)
        (interp_gop_iso pc h_sound B ρ)
  | TyExpr.mu n F, ρ => by
      exact mu_congr _ _ (fun Y => interp_gop_iso pc h_sound F (ρ.update n Y))
  | TyExpr.nu n F, ρ => by
      exact nu_congr _ _ (fun Y => interp_gop_iso pc h_sound F (ρ.update n Y))

/-! ## The irreducibility clause

  Here the environment matters. At a variable the operator returns `ρ n`
  untouched, so the result is irreducible only if the environment holds
  irreducible types. That is the paper's *grain-saturation* hypothesis, and it
  "discharges itself at the binder", where the variable is instantiated by the
  fixed point of an already-reduced body. -/

/-- An environment is **grain-saturated** when every type it holds is its own
    grain. -/
def Saturated (ρ : Env D) : Prop := ∀ n, Foundations.IsIrreducible (ρ n)

theorem interp_gop_irred (pc : ProdClause D) (h_sound : pc.Sound) :
    ∀ (T : TyExpr D) (ρ : Env D), Saturated ρ →
      Foundations.IsIrreducible (interp pc (gop pc T) ρ)
  | base b, _, _ => grain_irreducible b
  | var n, _, hρ => hρ n
  | TyExpr.prod A B, ρ, _ =>
      (h_sound (gop pc A) (gop pc B) ρ).toIrreducible
  | TyExpr.sum A B, ρ, hρ => by
      -- the sum of irreducible summands is irreducible; no condition is needed,
      -- the summands being disjoint alternatives
      have hA := interp_gop_irred pc h_sound A ρ hρ
      have hB := interp_gop_irred pc h_sound B ρ hρ
      intro S h_ssub h_iso
      exact sum_irred _ _ _ _ S (fun T => hA T) (fun T => hB T) h_ssub h_iso
  | TyExpr.mu n F, ρ, hρ => by
      refine mu_irred _ (fun Y hY => ?_)
      -- saturation is *restored* at the binder rather than assumed: the
      -- recursion variable is instantiated by an already-reduced type.
      exact interp_gop_irred pc h_sound F (ρ.update n Y) (by
        intro m
        by_cases h : m = n
        · simpa only [Env.update, if_pos h] using hY
        · simpa only [Env.update, if_neg h] using hρ m)
  | TyExpr.nu n F, ρ, hρ => by
      refine nu_irred _ (fun Y hY => ?_)
      exact interp_gop_irred pc h_sound F (ρ.update n Y) (by
        intro m
        by_cases h : m = n
        · simpa only [Env.update, if_pos h] using hY
        · simpa only [Env.update, if_neg h] using hρ m)

/-! ## The theorem -/

/-- **Theorem [Correctness of the grain type-expression operator].**

    For every algebraic data type `T`, `G(T)` is a grain of `T` in the sense of
    Definition 3.1: isomorphic to `T`, and irreducible.

    The operator therefore *computes* what Definition 3.1 only specifies: from
    the type expression and the declared determinations it produces a grain of
    `T`, and by Multiple Grains it does not matter which one. -/
theorem gop_isGrainOf (pc : ProdClause D) (h_sound : pc.Sound)
    (T : TyExpr D) (ρ : Env D) (hρ : Saturated ρ) :
    IsGrainOf (interp pc (gop pc T) ρ) (interp pc T ρ) :=
  IsGrainOf.mk' (interp_gop_iso pc h_sound T ρ) (interp_gop_irred pc h_sound T ρ hρ)

/-- …and by Multiple Grains, it does not matter which grain the clause picked:
    any two runs of the operator agree up to isomorphism. -/
theorem gop_unique (pc₁ pc₂ : ProdClause D) (h₁ : pc₁.Sound) (h₂ : pc₂.Sound)
    (T : TyExpr D) (ρ : Env D) (hρ : Saturated ρ)
    (h_same : interp pc₁ T ρ = interp pc₂ T ρ) :
    iso (interp pc₁ (gop pc₁ T) ρ) (interp pc₂ (gop pc₂ T) ρ) :=
  multiple_grains_iso (gop_isGrainOf pc₁ h₁ T ρ hρ)
    (h_same ▸ gop_isGrainOf pc₂ h₂ T ρ hρ)

end GrainTheory.ADT
