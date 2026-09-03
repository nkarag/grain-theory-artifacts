/-
  GrainTheory.Foundations.CollectionKey — Type grain versus collection key

  arXiv extended version, §3, Theorem [Type grain versus collection key].

  Remark [Grain and keys] claims the grain differs from a declared key in three
  respects, the first being that a key is a property of a catalogued base table
  while a pipeline continually produces intermediate results and in-memory
  frames that live in no catalogue and carry no declared key. The grain, fixed
  by the type, is defined for all of them.

  **The difference is a quantifier, and it is a theorem.** For a field-set
  projection `k : R ↠ K` the following are equivalent:

    (1) `k` is injective on the **type** `R`;
    (2) `k` is a superkey of **every** collection of `R`-elements;
    (3) `k` is itself an isomorphism `R ≅ K`, whence `R ≡_g K`.

  And `K` is a grain of `R` exactly when no proper sub-projection satisfies
  these.

  Clause (2) is the one that does the work, and its quantifier is why the
  property cannot be checked against data: any finite collection can be filtered
  until a proper sub-projection becomes injective on it. The degenerate case is
  mechanized below — in a collection of one row, *every* projection identifies.
  That is why relational systems enforce declared keys rather than infer them,
  and why the grain discharges the quantifier at the type level instead.

  These are element-level statements, so they live on the semantic layer.
-/

import GrainTheory.DependencyTheory.Factorization
import GrainTheory.Relations.GrainEquality

universe u v

namespace GrainTheory.Foundations

open GrainStructure SemanticGrainStructure

variable {D : Type u} [SemanticGrainStructure.{u, v} D]

/-- A collection of `R`-elements. Bag versus set is immaterial here: every
    clause below is about which elements occur, not how often. -/
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

/-- **(1) ⟺ (3).** "`k` is surjective by construction and a surjection is
    injective exactly when it is a bijection." -/
theorem injective_iff_bijective_of_surjective {R K : D} {k : den R → den K}
    (hs : Function.Surjective k) :
    Function.Injective k ↔ Function.Bijective k :=
  ⟨fun hi => ⟨hi, hs⟩, fun hb => hb.1⟩

/-- **The theorem.** For a field-set projection `k : R ↠ K`, all three clauses
    are equivalent. -/
theorem type_grain_vs_collection_key {R K : D} (k : den R → den K)
    (hs : Function.Surjective k) :
    (Function.Injective k ↔ SuperkeyOfEvery k)
    ∧ (Function.Injective k ↔ Function.Bijective k) :=
  ⟨injective_iff_superkeyOfEvery k, injective_iff_bijective_of_surjective hs⟩

/-- Clause (3) reported back at the type level: a bijective field-set
    projection **is** a type isomorphism, "whence `R ≡_g K`". -/
theorem iso_of_bijective {R K : D} {k : den R → den K}
    (hb : Function.Bijective k) : iso R K :=
  equivIso R K (Equiv.ofBijective k hb)

/-- …and therefore `R` and `K` are grain-equal. -/
theorem grainEq_of_superkeyOfEvery {R K : D} {k : den R → den K}
    (hs : Function.Surjective k) (h : SuperkeyOfEvery k) :
    Relations.grainEq R K :=
  Relations.grainEq_of_iso
    (iso_of_bijective ⟨injective_of_superkeyOfEvery h, hs⟩)

/-- **`K` is a grain of `R`** when, in addition, no proper sub-projection
    satisfies the conditions — Definition 3.1's irreducibility clause read
    on `K`. -/
theorem isGrainOf_of_superkeyOfEvery {R K : D} {k : den R → den K}
    (hs : Function.Surjective k) (h : SuperkeyOfEvery k)
    (h_irred : IsIrreducible K) : IsGrainOf K R :=
  IsGrainOf.mk'
    (iso_symm _ _ (iso_of_bijective ⟨injective_of_superkeyOfEvery h, hs⟩))
    h_irred

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
