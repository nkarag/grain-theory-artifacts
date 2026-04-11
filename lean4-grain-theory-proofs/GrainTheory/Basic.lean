/-
  GrainTheory.Basic — Core axioms for grain theory

  Abstract axiomatization of data types and the grain operator.
  Reference: PODS 2027 paper, §3 (Foundations).

  `D` is an opaque universe of data types. We axiomatize:
  - Type subset relation (⊆_typ)
  - Type isomorphism (≅_typ)
  - Grain operator G[·]
  - Type-level operations (product, sum, intersection, union, difference)
-/

import Mathlib.Tactic

universe u

/-- The core axiomatization of grain theory over an abstract universe of data types `D`.

  `sub R S` means R is a type-level subset of S (PODS Def 1: every field of R is a field of S).
  `iso R S` means R and S are isomorphic (there exists a two-sided inverse between them).
  `grain R` is the grain of R — the irreducible core that is isomorphic to R.

  The three grain axioms (PODS Def 3):
  1. `grain_sub`: G[R] ⊆_typ R
  2. `grain_iso`: G[R] ≅ R
  3. `grain_irred`: if S ⊆_typ G[R] and S ≅ R, then G[R] ⊆_typ S (irreducibility)
-/
class GrainStructure (D : Type u) where
  /-- Type-level subset: `sub A B` means A ⊆_typ B (PODS Def 1) -/
  sub : D → D → Prop
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
  /-- Irreducibility: no proper subset of G[R] is isomorphic to R.
      If S ⊆_typ G[R] and S ≅ R, then G[R] ⊆_typ S. -/
  grain_irred : ∀ (R S : D), sub S (grain R) → iso S R → sub (grain R) S
  -- Structural axioms for union (least upper bound in ⊆_typ)
  /-- R ⊆_typ (R ∪ S) -/
  sub_union_left : ∀ (R S : D), sub R (union R S)
  /-- S ⊆_typ (R ∪ S) -/
  sub_union_right : ∀ (R S : D), sub S (union R S)
  /-- If R ⊆_typ T and S ⊆_typ T, then (R ∪ S) ⊆_typ T -/
  union_sub : ∀ (R S T : D), sub R T → sub S T → sub (union R S) T
  -- Structural axioms for inter (greatest lower bound in ⊆_typ)
  /-- (R ∩ S) ⊆_typ R -/
  inter_sub_left : ∀ (R S : D), sub (inter R S) R
  /-- (R ∩ S) ⊆_typ S -/
  inter_sub_right : ∀ (R S : D), sub (inter R S) S
  /-- If T ⊆_typ R and T ⊆_typ S, then T ⊆_typ (R ∩ S) -/
  sub_inter : ∀ (R S T : D), sub T R → sub T S → sub T (inter R S)
  -- Structural axioms for diff
  /-- (R \ S) ⊆_typ R -/
  sub_diff : ∀ (R S : D), sub (diff R S) R
  /-- R ⊆_typ S ∪ (R \ S): every field of R is either in S or in R \ S -/
  sub_union_diff : ∀ (R S : D), sub R (union S (diff R S))
  /-- R ⊆_typ (R ∩ S) ∪ (R \ S): decomposition into the S-part and complement.
      Standard set identity: every field of R is either in both R and S, or in R but not S.
      Stronger than sub_union_diff (which uses S, not R ∩ S) when S ⊄ R. -/
  sub_inter_union_diff : ∀ (R S : D), sub R (union (inter R S) (diff R S))
  /-- (A \ B) ∩ B is empty: the set difference removes all B-fields.
      Formally: ∀ T, (A \ B) ∩ B ⊆_typ T (the intersection is the bottom element).
      PODS justification: a field in A \ B is by definition not in B. -/
  diff_inter_empty : ∀ (A B T : D), sub (inter (diff A B) B) T
  /-- diff is monotone in its first argument: A ⊆_typ B → (A \ C) ⊆_typ (B \ C).
      PODS justification: if A has fewer fields than B, removing the same
      fields from A gives a result no larger than removing them from B. -/
  diff_sub_left : ∀ (A B C : D), sub A B → sub (diff A C) (diff B C)
  /-- Intersection distributes over union (left):
      (A ∩ (B ∪ C)) ⊆_typ (A ∩ B) ∪ (A ∩ C).
      PODS justification: field sets form a distributive lattice (standard
      set theory identity). -/
  inter_distrib_union : ∀ (A B C : D),
    sub (inter A (union B C)) (union (inter A B) (inter A C))
  -- Grain interaction with type operations
  /-- G[R ∪ S] ≅ G[R] ∪ G[S]: grain distributes over union -/
  grain_union : ∀ (R S : D), iso (grain (union R S)) (union (grain R) (grain S))
  /-- G[R ∩ S] ≅ G[R] ∩ G[S]: grain distributes over intersection -/
  grain_inter : ∀ (R S : D), iso (grain (inter R S)) (inter (grain R) (grain S))
  -- Structural axioms for prod
  /-- A ⊆_typ (A × B): first component embeds into the product.
      PODS justification: every column of A is a column of A × B. -/
  sub_prod_left : ∀ (A B : D), sub A (prod A B)
  /-- B ⊆_typ (A × B): second component embeds into the product.
      PODS justification: every column of B is a column of A × B. -/
  sub_prod_right : ∀ (A B : D), sub B (prod A B)
  /-- Product preserves type subset: if A ⊆_typ B and C ⊆_typ D, then A × C ⊆_typ B × D.
      PODS justification: product is component-wise; sub-products of sub-products
      remain sub-products. -/
  sub_prod : ∀ (A B C E : D), sub A B → sub C E → sub (prod A C) (prod B E)
  /-- Product preserves isomorphism: if A ≅ B and C ≅ D, then A × C ≅ B × D.
      PODS justification: component-wise isos compose to a product iso (see
      Theorem grain-product, Isomorphism step). -/
  prod_iso : ∀ (A B C E : D), iso A B → iso C E → iso (prod A C) (prod B E)
  /-- Products of irreducible types are irreducible.
      If A is irreducible for C and B is irreducible for D, then A × B is
      irreducible for C × D: any S ⊆_typ A × B with S ≅ C × D forces A × B ⊆_typ S.
      PODS justification: Theorem grain-product, Irreducibility step — a proper
      sub-product projects onto a proper subset of some component, contradicting
      that component's irreducibility. -/
  prod_irred : ∀ (A B C E S : D),
    (∀ T : D, sub T A → iso T C → sub A T) →
    (∀ T : D, sub T B → iso T E → sub B T) →
    sub S (prod A B) → iso S (prod C E) → sub (prod A B) S
  /-- Product is associative up to isomorphism.
      PODS justification: (A × B) × C and A × (B × C) have the same fields. -/
  prod_assoc_iso : ∀ (A B C : D), iso (prod (prod A B) C) (prod A (prod B C))
  /-- Product is commutative up to isomorphism.
      PODS justification: A × B and B × A have the same fields. -/
  prod_comm_iso : ∀ (A B : D), iso (prod A B) (prod B A)
  /-- A type decomposes into the product of its Jk-part and non-Jk part.
      When Jk ⊆ R, R ≅ (R \ Jk) × Jk: the Jk fields and non-Jk fields of R
      together form a product that is isomorphic to R.
      PODS justification: a type is the disjoint union of its Jk-portion and
      its complement, and for disjoint field sets union = product. -/
  diff_prod_iso : ∀ (R Jk : D), sub Jk R → iso R (prod (diff R Jk) Jk)
  /-- Sub-types of grain fixpoints are grain fixpoints (diff case).
      If G[R] ≅ R (R is irreducible / is its own grain), then
      G[R \ S] ≅ R \ S for any S.
      PODS justification: Suppose T ⊊ R \ S with T ≅ R \ S. Then
      T ∪ (R ∩ S) ⊊ (R \ S) ∪ (R ∩ S) ≅ R with T ∪ (R ∩ S) ≅ R
      (disjoint component reconstruction), contradicting R's
      irreducibility (G[R] ≅ R means no proper sub-type is iso to R). -/
  grain_diff_idempotent : ∀ (R S : D), iso (grain R) R → iso (grain (diff R S)) (diff R S)
  -- Structural axioms for sum (coproduct)
  /-- Sum preserves type subset: if A ⊆_typ B and C ⊆_typ D, then A + C ⊆_typ B + D.
      PODS justification: sum is component-wise; sub-types of sub-types
      remain sub-types in each summand. -/
  sub_sum : ∀ (A B C E : D), sub A B → sub C E → sub (sum A C) (sum B E)
  /-- Sum preserves isomorphism: if A ≅ B and C ≅ D, then A + C ≅ B + D.
      PODS justification: component-wise isos compose to a sum iso (see
      Theorem grain-sum, Isomorphism step). -/
  sum_iso : ∀ (A B C E : D), iso A B → iso C E → iso (sum A C) (sum B E)
  /-- Sums of irreducible types are irreducible.
      If A is irreducible for C and B is irreducible for D, then A + B is
      irreducible for C + D: any S ⊆_typ A + B with S ≅ C + D forces A + B ⊆_typ S.
      PODS justification: Theorem grain-sum, Irreducibility step — a proper
      sub-sum restricts to a proper subset of some component, contradicting
      that component's irreducibility. -/
  sum_irred : ∀ (A B C E S : D),
    (∀ T : D, sub T A → iso T C → sub A T) →
    (∀ T : D, sub T B → iso T E → sub B T) →
    sub S (sum A B) → iso S (sum C E) → sub (sum A B) S

namespace GrainStructure

variable {D : Type u} [GrainStructure D]

-- Notation for type subset
scoped infixl:50 " ⊆_typ " => GrainStructure.sub
-- Notation for type isomorphism
scoped infixl:50 " ≅_typ " => GrainStructure.iso
-- Notation for grain operator
scoped prefix:max "G[" => GrainStructure.grain
-- Closing bracket handled by Lean's parser as function application

end GrainStructure
