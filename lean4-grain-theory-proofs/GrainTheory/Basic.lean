/-
  GrainTheory.Basic — Core axioms for grain theory

  Abstract axiomatization of data types and the grain operator.
  Reference: PODS 2027 paper, §3 (Foundations).

  `D` is an opaque universe of data types. We axiomatize:
  - Type subset relation (⊆_typ) — *semantic*: a surjection exists
  - Structural subtype relation (⊑) — *structural*: component containment
  - Type isomorphism (≅_typ)
  - Grain operator G[·]
  - Type-level operations (product, sum, intersection, union, difference)

  **The notation split (arXiv Definitions 2.1 and 2.3).**
  `sub` (⊆_typ) holds when *some* surjection `B ↠ A` exists — the witness
  may be a *declared* determination (a foreign key, a functional
  dependency). `ssub` (⊑) holds only when every component of `A` occurs
  among the components of `B`, the witness being the canonical projection
  that forgets the extra components; it is decidable from the schema alone.

  `ssub` *refines* `sub` (`ssub_sub`) but not conversely, and the gap is
  load-bearing: `CustomerId ⊏ CustomerId × CustomerName` is proper even
  though the two types are isomorphic under the declared determination
  `CustomerId ↠ CustomerName`. Routing the two relations correctly is what
  makes grain irreducibility non-vacuous:

  - **irreducibility** (`grain_irred`, `prod_irred`, `sum_irred`) and the
    CalcG algorithm quantify over `ssub`;
  - the **isomorphism** clause, the grain **ordering** `≤_g`, the EK–grain
    hierarchy, and **external grains** stay on `sub`.

  Under the old encoding, where irreducibility quantified over `sub`, the
  clause was vacuous: every type isomorphic to `R` qualified as a grain,
  because a bijection is a surjection in both directions.
-/

import Mathlib.Tactic

universe u

/-- The core axiomatization of grain theory over an abstract universe of data types `D`.

  `sub R S` means R is a type-level subset of S (PODS Def 1: every field of R is a field of S).
  `iso R S` means R and S are isomorphic (there exists a two-sided inverse between them).
  `grain R` is the grain of R — the irreducible core that is isomorphic to R.

  The three grain axioms (arXiv Def 3.1):
  1. `grain_sub`: G[R] ⊆_typ R
  2. `grain_iso`: G[R] ≅ R
  3. `grain_irred`: if S ⊑ G[R] and S ≅ R, then G[R] ⊑ S (*structural*
     irreducibility)
-/
class GrainStructure (D : Type u) where
  /-- Type-level subset: `sub A B` means A ⊆_typ B (arXiv Def 2.1).
      Semantic: *some* surjection `B ↠ A` exists, possibly a declared one. -/
  sub : D → D → Prop
  /-- Structural subtype: `ssub A B` means A ⊑ B (arXiv Def 2.3).
      Every component of A occurs among the components of B; the witness is
      the canonical projection. Decidable from the schema alone. -/
  ssub : D → D → Prop
  /-- Declared independence: `indep A B` means no determination is declared
      between A and B — neither functionally determines the other
      (arXiv Thm 3.8 hypothesis, Remark 4.3).

      In arXiv Thm 7.2 this is read at the **grain level**: the determinant is
      a whole grain. A declared FD whose left side is no grain — a composite
      key spanning both inputs, say — is not seen here, and is applied
      afterwards by Grain Reduction (`Inference/GrainReduction.lean`). -/
  indep : D → D → Prop
  /-- Type isomorphism: `iso A B` means A ≅ B (two-sided inverse exists) -/
  iso : D → D → Prop
  /-- Grain operator: `grain R` is G[R], the grain of R (PODS Def 3) -/
  grain : D → D
  /-- Type-level product -/
  prod : D → D → D
  /-- Type-level sum (coproduct) -/
  sum : D → D → D
  /-- Type-level intersection -/
  inter : D → D → D
  /-- Type-level union -/
  union : D → D → D
  /-- Type-level difference -/
  diff : D → D → D
  -- Structural axioms for sub (preorder + antisymmetry up to iso)
  /-- ⊆_typ is reflexive -/
  sub_refl : ∀ (R : D), sub R R
  /-- ⊆_typ is transitive -/
  sub_trans : ∀ (R S T : D), sub R S → sub S T → sub R T
  /-- ⊆_typ is antisymmetric up to isomorphism -/
  sub_antisymm : ∀ (R S : D), sub R S → sub S R → iso R S
  -- Structural axioms for ssub (⊑): a partial order on component sets
  /-- ⊑ is reflexive: every component of R is a component of R -/
  ssub_refl : ∀ (R : D), ssub R R
  /-- ⊑ is transitive -/
  ssub_trans : ∀ (R S T : D), ssub R S → ssub S T → ssub R T
  /-- ⊑ is antisymmetric up to isomorphism: mutual component containment
      means the same component set, hence isomorphic types -/
  ssub_antisymm : ∀ (R S : D), ssub R S → ssub S R → iso R S
  /-- ⊑ **refines** ⊆_typ: a canonical projection is a surjection
      (arXiv Def 2.3). The converse fails — that gap is what makes
      irreducibility non-vacuous. -/
  ssub_sub : ∀ (R S : D), ssub R S → sub R S
  /-- **Structural subtyping is well-founded on any predicate it can reach.**
      Given a property `P` holding of `G`, there is a `⊑`-minimal `K ⊑ G` still
      satisfying `P`.

      arXiv justification: Lemma 3.2's proof is exactly this argument — "the
      structural subtypes of `R` … form a finite, nonempty set … let `G` be a
      `⊑`-minimal element". A type has finitely many structural subtypes, one
      per subset of its components, so minimal elements exist. This is what
      licenses both grain existence and the key-minimization of Grain
      Reduction. -/
  ssub_wf : ∀ (G : D) (P : D → Prop), P G →
    ∃ K : D, ssub K G ∧ P K ∧ ∀ T : D, ssub T K → P T → ssub K T
  /-- Nothing is determined by, or determines, an empty type: independence
      against the bottom element is vacuous. Used to discharge the independence
      hypothesis in the equi-join special cases where `G[R₂] -_typ Jk` is empty
      (arXiv Prop 7.3, cases 1–2). -/
  indep_bot : ∀ (A B : D), (∀ T : D, ssub B T) → indep A B
  -- Structural axioms for iso (equivalence relation)
  /-- ≅ is reflexive -/
  iso_refl : ∀ (R : D), iso R R
  /-- ≅ is symmetric -/
  iso_symm : ∀ (R S : D), iso R S → iso S R
  /-- ≅ is transitive -/
  iso_trans : ∀ (R S T : D), iso R S → iso S T → iso R T
  /-- Isomorphic types have the same subsets: if A ≅ B and C ⊆_typ B, then C ⊆_typ A -/
  iso_sub : ∀ (A B C : D), iso A B → sub C B → sub C A
  -- Grain axioms (PODS Definition 3)
  /-- G[R] ⊆_typ R: the grain is a type-level subset of R -/
  grain_sub : ∀ (R : D), sub (grain R) R
  /-- G[R] ≅ R: the grain is isomorphic to R -/
  grain_iso : ∀ (R : D), iso (grain R) R
  /-- **Structural irreducibility** (arXiv Def 3.1, clause 2): no proper
      *structural* subtype of G[R] is isomorphic to R.
      Contrapositive form: if S ⊑ G[R] and S ≅ R, then G[R] ⊑ S.

      The comparison is structural, so it is not defeated by a declared
      isomorphism between G[R] and one of its proper subtypes — which is
      precisely what made the earlier `sub`-based reading vacuous. -/
  grain_irred : ∀ (R S : D), ssub S (grain R) → iso S R → ssub (grain R) S
  -- Structural axioms for union (least upper bound in ⊆_typ)
  /-- R ⊆_typ (R ∪ S) -/
  ssub_union_left : ∀ (R S : D), ssub R (union R S)
  /-- S ⊆_typ (R ∪ S) -/
  ssub_union_right : ∀ (R S : D), ssub S (union R S)
  /-- If R ⊆_typ T and S ⊆_typ T, then (R ∪ S) ⊆_typ T -/
  union_ssub : ∀ (R S T : D), ssub R T → ssub S T → ssub (union R S) T
  /-- Semantic lub: if R ⊆_typ T and S ⊆_typ T, then (R ∪ S) ⊆_typ T.
      Stated separately from `union_ssub` because the hypotheses may be
      *declared* surjections, which carry no structural information. -/
  union_sub : ∀ (R S T : D), sub R T → sub S T → sub (union R S) T
  -- Structural axioms for inter (greatest lower bound in ⊆_typ)
  /-- (R ∩ S) ⊆_typ R -/
  inter_ssub_left : ∀ (R S : D), ssub (inter R S) R
  /-- (R ∩ S) ⊆_typ S -/
  inter_ssub_right : ∀ (R S : D), ssub (inter R S) S
  /-- If T ⊆_typ R and T ⊆_typ S, then T ⊆_typ (R ∩ S) -/
  ssub_inter : ∀ (R S T : D), ssub T R → ssub T S → ssub T (inter R S)
  -- NOTE: there is deliberately no `sub_inter`. The semantic glb property
  -- "T ⊆_typ R → T ⊆_typ S → T ⊆_typ (R ∩ S)" is **false**: ⊆_typ means
  -- *determines*, and two sources can each determine T while the columns they
  -- share determine nothing. Refuted in `Model/AxiomCheck.lean`.
  -- Structural axioms for diff
  /-- (R \ S) ⊆_typ R -/
  ssub_diff : ∀ (R S : D), ssub (diff R S) R
  /-- R ⊆_typ S ∪ (R \ S): every field of R is either in S or in R \ S -/
  ssub_union_diff : ∀ (R S : D), ssub R (union S (diff R S))
  /-- R ⊆_typ (R ∩ S) ∪ (R \ S): decomposition into the S-part and complement.
      Standard set identity: every field of R is either in both R and S, or in R but not S.
      Stronger than sub_union_diff (which uses S, not R ∩ S) when S ⊄ R. -/
  ssub_inter_union_diff : ∀ (R S : D), ssub R (union (inter R S) (diff R S))
  /-- (A \ B) ∩ B is empty: the set difference removes all B-fields.
      Formally: ∀ T, (A \ B) ∩ B ⊆_typ T (the intersection is the bottom element).
      PODS justification: a field in A \ B is by definition not in B. -/
  diff_inter_empty : ∀ (A B T : D), ssub (inter (diff A B) B) T
  /-- diff is monotone in its first argument: A ⊆_typ B → (A \ C) ⊆_typ (B \ C).
      PODS justification: if A has fewer fields than B, removing the same
      fields from A gives a result no larger than removing them from B. -/
  diff_ssub_left : ∀ (A B C : D), ssub A B → ssub (diff A C) (diff B C)
  -- NOTE: there is deliberately no `diff_sub_left`. Its semantic form
  -- "A ⊆_typ B → (A \ C) ⊆_typ (B \ C)" is **false**: removing columns from a
  -- determiner can destroy the determination outright. Refuted in
  -- `Model/AxiomCheck.lean`.
  /-- Intersection distributes over union (left):
      (A ∩ (B ∪ C)) ⊆_typ (A ∩ B) ∪ (A ∩ C).
      PODS justification: field sets form a distributive lattice (standard
      set theory identity). -/
  inter_distrib_union : ∀ (A B C : D),
    ssub (inter A (union B C)) (union (inter A B) (inter A C))
  -- Grain interaction with type operations
  /-- G[R ∪ S] ≅ G[R] ∪ G[S]: grain distributes over union -/
  grain_union : ∀ (R S : D), iso (grain (union R S)) (union (grain R) (grain S))
  -- Structural axioms for prod
  /-- A ⊆_typ (A × B): first component embeds into the product.
      PODS justification: every column of A is a column of A × B. -/
  ssub_prod_left : ∀ (A B : D), ssub A (prod A B)
  /-- B ⊆_typ (A × B): second component embeds into the product.
      PODS justification: every column of B is a column of A × B. -/
  ssub_prod_right : ∀ (A B : D), ssub B (prod A B)
  /-- Product preserves isomorphism: if A ≅ B and C ≅ D, then A × C ≅ B × D.
      PODS justification: component-wise isos compose to a product iso (see
      Theorem grain-product, Isomorphism step). -/
  prod_iso : ∀ (A B C E : D), iso A B → iso C E → iso (prod A C) (prod B E)
  /-- Products of irreducible types are irreducible — **given independence**.
      If C and E are independent (no determination declared across the
      components), A is irreducible for C, and B is irreducible for E, then
      A × B is irreducible for C × E: any S ⊑ A × B with S ≅ C × E forces
      A × B ⊑ S.

      arXiv justification: Thm 3.8 (Grain of Product Types), irreducibility
      step — a proper structural sub-product omits a component or restricts
      it, contradicting that component's irreducibility. The `indep`
      hypothesis is the side condition added in the post-review revision:
      when a determination holds across components the product is reducible
      and its grain is computed by Grain Inference (Thm 5.10) instead. -/
  prod_irred : ∀ (A B C E S : D),
    indep C E →
    (∀ T : D, ssub T A → iso T C → ssub A T) →
    (∀ T : D, ssub T B → iso T E → ssub B T) →
    ssub S (prod A B) → iso S (prod C E) → ssub (prod A B) S
  /-- Product is commutative up to isomorphism.
      PODS justification: A × B and B × A have the same fields. -/
  prod_comm_iso : ∀ (A B : D), iso (prod A B) (prod B A)
  -- Structural axioms for sum (coproduct)
  /-- Sum preserves isomorphism: if A ≅ B and C ≅ D, then A + C ≅ B + D.
      PODS justification: component-wise isos compose to a sum iso (see
      Theorem grain-sum, Isomorphism step). -/
  sum_iso : ∀ (A B C E : D), iso A B → iso C E → iso (sum A C) (sum B E)
  /-- Sums of irreducible types are irreducible.
      If A is irreducible for C and B is irreducible for E, then A + B is
      irreducible for C + E: any S ⊑ A + B with S ≅ C + E forces A + B ⊑ S.
      arXiv justification: Thm 3.9 (Grain of Sum Types), irreducibility step —
      a proper structural sub-sum restricts to a proper subtype of some
      summand, contradicting that summand's irreducibility.

      **No independence hypothesis is needed** (unlike `prod_irred`): the
      summands of a coproduct are disjoint alternatives, so no determination
      can hold across them (arXiv Remark 4.3). -/
  sum_irred : ∀ (A B C E S : D),
    (∀ T : D, ssub T A → iso T C → ssub A T) →
    (∀ T : D, ssub T B → iso T E → ssub B T) →
    ssub S (sum A B) → iso S (sum C E) → ssub (sum A B) S

namespace GrainStructure

variable {D : Type u} [GrainStructure D]

/-! ## Semantic shadows of the structural lattice laws

  The type-level operations `∪_typ`, `∩_typ`, `-_typ`, `×` and `+` are
  defined on *component sets* (arXiv §2), so every law governing them is a
  structural fact and is axiomatized over `⊑` above. Each has a `⊆_typ`
  shadow, obtained by composing with `ssub_sub` — a canonical projection is a
  surjection.

  Stating them structurally and deriving the semantic versions (rather than
  the reverse) is what lets the equi-join and CalcG developments reuse the
  same field-set arithmetic when discharging *irreducibility*, which lives on
  `⊑` and cannot consume a merely semantic containment. The names below are
  the ones used throughout the development, so no call site had to change. -/

theorem sub_union_left (R S : D) : sub R (union R S) :=
  ssub_sub _ _ (ssub_union_left R S)

theorem sub_union_right (R S : D) : sub S (union R S) :=
  ssub_sub _ _ (ssub_union_right R S)

theorem inter_sub_left (R S : D) : sub (inter R S) R :=
  ssub_sub _ _ (inter_ssub_left R S)

theorem inter_sub_right (R S : D) : sub (inter R S) S :=
  ssub_sub _ _ (inter_ssub_right R S)

theorem sub_diff (R S : D) : sub (diff R S) R :=
  ssub_sub _ _ (ssub_diff R S)

theorem sub_union_diff (R S : D) : sub R (union S (diff R S)) :=
  ssub_sub _ _ (ssub_union_diff R S)

theorem sub_inter_union_diff (R S : D) : sub R (union (inter R S) (diff R S)) :=
  ssub_sub _ _ (ssub_inter_union_diff R S)

theorem sub_inter_distrib_union (A B C : D) :
    sub (inter A (union B C)) (union (inter A B) (inter A C)) :=
  ssub_sub _ _ (inter_distrib_union A B C)

theorem sub_diff_inter_empty (A B T : D) : sub (inter (diff A B) B) T :=
  ssub_sub _ _ (diff_inter_empty A B T)

theorem sub_prod_left (A B : D) : sub A (prod A B) :=
  ssub_sub _ _ (ssub_prod_left A B)

theorem sub_prod_right (A B : D) : sub B (prod A B) :=
  ssub_sub _ _ (ssub_prod_right A B)

-- Notation for type subset (semantic: a surjection exists)
scoped infixl:50 " ⊆_typ " => GrainStructure.sub
-- Notation for structural subtype (schema-decidable: component containment)
scoped infixl:50 " ⊑_typ " => GrainStructure.ssub
-- Notation for type isomorphism
scoped infixl:50 " ≅_typ " => GrainStructure.iso
-- Notation for grain operator
scoped prefix:max "G[" => GrainStructure.grain
-- Closing bracket handled by Lean's parser as function application

end GrainStructure
