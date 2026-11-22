/-
  GrainTheory.Foundations.CollectionKey — Type grain versus collection key

  arXiv v4 `thm:type-grain-vs-collection-key` (Type grain versus collection key).

  arXiv v4 `rem:grain-vs-pk` (Grain and keys: the base case) claims the grain differs from a
  declared key in three
  respects, the first being that a key is a property of a catalogued base table
  while a pipeline continually produces intermediate results and in-memory
  frames that live in no catalogue and carry no declared key. The grain, fixed
  by the type, is defined for all of them.

  **The difference is a quantifier, and it is a theorem.** For a field-set
  projection `k : R ↠ K` the following are equivalent:

    (1) `k` is injective on the **type** `R`, in every admissible realization;
    (2) `k` is a superkey of **every** collection of `R`-elements, each drawn
        from one realization;
    (3) `k` is itself an isomorphism `R ≅ K` by structure maps, whence
        `R ≡_g K`.

  And `K` is a grain of `R` exactly when no proper sub-projection satisfies
  these.

  Clause (2) is the one that does the work, and its quantifier is why the
  property cannot be checked against data: any finite collection can be filtered
  until a proper sub-projection becomes injective on it. The degenerate case is
  mechanized below — in a collection of one row, *every* projection identifies.
  That is why relational systems enforce declared keys rather than infer them,
  and why the grain discharges the quantifier at the type level instead.

  **Two layers.** One instance of `SemanticGrainStructure` is one realization
  (arXiv v4 `rem:realization-and-change`), and `Coll R = Set (den R)` is a
  collection drawn from it. This module proves (1) ⇔ (2) there, one realization
  at a time, which gives the paper's statement over every realization since
  the theorems hold for every instance. (1) ⇔ (3) is not a statement about one
  realization: a bijection in one realization is no isomorphism (the
  realization in which every employee has an address of their own). It is
  proved in `Foundations/Realization.lean`, on a concrete model of records,
  declarations and realizations, where (1) is quantified over all admissible
  realizations and shown equivalent to the closure step and to an isomorphism
  by structure maps. Until 21 Nov 2026 this module derived (3) from injectivity
  in one realization through the axiom `equivIso`, which the paper's revision
  showed unsound; the axiom and the three corollaries resting on it
  (`iso_of_bijective`, `grainEq_of_superkeyOfEvery`,
  `isGrainOf_of_superkeyOfEvery`) were removed.

  These are element-level statements, so they live on the semantic layer.
-/

import GrainTheory.DependencyTheory.Factorization

universe u v

namespace GrainTheory.Foundations

open GrainStructure SemanticGrainStructure

variable {D : Type u} [SemanticGrainStructure.{u, v} D]

/-- A collection of `R`-elements, drawn from the realization this instance is:
    all its elements taken from `den R`. Bag versus set is immaterial here:
    every clause below is about which elements occur, not how often. -/
abbrev Coll (R : D) : Type v := Set (den R)

/-- **`k` is a superkey of the collection `c`**: it is injective on `c`'s
    elements. This is the ordinary, instance-level notion — a fact about one
    collection at one moment. -/
def SuperkeyOn {R K : D} (k : den R → den K) (c : Coll R) : Prop :=
  Set.InjOn k c

/-- **`k` is a superkey of every collection.** Clause (2): the quantifier that
    separates a type-level grain from an instance-level identifier. -/
def SuperkeyOfEvery {R K : D} (k : den R → den K) : Prop :=
  ∀ c : Coll R, SuperkeyOn k c

/-! ## The equivalence -/

/-- (1) ⇒ (2). "Injectivity on `R` gives injectivity on the elements of any
    collection of `R`-elements." -/
theorem superkeyOfEvery_of_injective {R K : D} {k : den R → den K}
    (h : Function.Injective k) : SuperkeyOfEvery k :=
  fun _ _ _ _ _ hk => h hk

/-- (2) ⇒ (1). Contrapositively: "a collision `k r₁ = k r₂` with `r₁ ≠ r₂`
    makes `k` non-injective on the two-element collection holding both." -/
theorem injective_of_superkeyOfEvery {R K : D} {k : den R → den K}
    (h : SuperkeyOfEvery k) : Function.Injective k := by
  intro r₁ r₂ hk
  exact h {r₁, r₂} (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) hk

/-- **(1) ⟺ (2).** Injective on the type iff a superkey of every collection. -/
theorem injective_iff_superkeyOfEvery {R K : D} (k : den R → den K) :
    Function.Injective k ↔ SuperkeyOfEvery k :=
  ⟨superkeyOfEvery_of_injective, injective_of_superkeyOfEvery⟩

/-- `k` is surjective by construction, and a surjection is injective exactly
    when it is a bijection. In one realization this is all that injectivity
    gives; the isomorphism of clause (3) needs every realization. -/
theorem injective_iff_bijective_of_surjective {R K : D} {k : den R → den K}
    (hs : Function.Surjective k) :
    Function.Injective k ↔ Function.Bijective k :=
  ⟨fun hi => ⟨hi, hs⟩, fun hb => hb.1⟩

/-- **The theorem, in one realization.** For a field-set projection
    `k : R ↠ K`, injectivity is equivalent to being a superkey of every
    collection drawn from this realization, and to bijectivity of `k` here.
    Bijectivity in one realization is not clause (3): see
    `Realizations.type_grain_vs_collection_key`. -/
theorem type_grain_vs_collection_key {R K : D} (k : den R → den K)
    (hs : Function.Surjective k) :
    (Function.Injective k ↔ SuperkeyOfEvery k)
    ∧ (Function.Injective k ↔ Function.Bijective k) :=
  ⟨injective_iff_superkeyOfEvery k, injective_iff_bijective_of_surjective hs⟩

/-! ## Why the quantifier cannot be checked against data

  "Any finite collection can be filtered until a proper sub-projection becomes
  injective on it… Pushed to its limit the notion says nothing about the type at
  all: in a collection of one row, every attribute identifies."

  Mechanized, that limit case is stark: *every* projection whatsoever is a
  superkey of a one-element collection, including projections that identify
  nothing about the type. So clause (2)'s quantifier is doing all the work — a
  single collection, or any finite family of them, constrains the type not at
  all. -/

/-- On a one-element collection every projection is a superkey — even the
    constant one. Instance-level identification says nothing about the type. -/
theorem superkeyOn_singleton {R K : D} (k : den R → den K) (r : den R) :
    SuperkeyOn k ({r} : Coll R) :=
  fun _ ha _ hb _ => by rw [ha, hb]

/-- The gap, stated as a non-implication: being a superkey of *some* collection
    does not make a projection injective on the type. Any `k` at all witnesses
    it on a singleton, so no amount of instance-level evidence closes the
    quantifier. -/
theorem superkeyOn_some_gives_nothing {R K : D} (k : den R → den K)
    (r : den R) : ∃ c : Coll R, SuperkeyOn k c :=
  ⟨{r}, superkeyOn_singleton k r⟩

end GrainTheory.Foundations
