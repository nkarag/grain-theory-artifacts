/-
  GrainTheory.ADT.Partitioned — grain of a partitioned collection

  arXiv/ICDT §"Grain for Arbitrary Algebraic Data Types":
  - Definition [Partitioned collection]
  - Proposition [Grain of a partitioned collection]

  "A stream acquires a finite, verifiable grain the moment it is windowed or
  partitioned, the move a stream processor must make to evaluate an unbounded
  input at all."

  This is what carries CalcG to streaming pipelines: the grain of the
  partitioned collection is the partition key, a finite product type, whatever
  the fibers hold — a finite list or an unbounded stream. The change-log
  example: `G[CDC-Event] = EntityId × ChangeSeqNo`, partitioned by
  `K = EntityId`, one inhabitant per entity holding the ordered sequence of its
  changes — a Kafka topic partition. Each fiber is unbounded, yet
  `G[Coll] = EntityId` is finite.
-/

import GrainTheory.Foundations.GrainDef
import GrainTheory.Foundations.MultipleGrains

universe u

namespace GrainTheory.ADT

open GrainStructure GrainTheory.Foundations

variable {D : Type u} [GrainStructure D]

/-- **Definition [Partitioned collection].**

    `C` is the `K`-partitioned collection of `R` when `K` is a
    grain-irreducible *structural* subtype of `R`'s grain — the partition key —
    and `C`'s inhabitants are the complete fibers of the `K`-projection, one per
    `k : K`.

    "Each inhabitant is determined by, and unique to, its key", which at the
    type level is exactly `C ≅ K`. The fiber content does not appear: that is
    the point, and it is why an unbounded fiber costs nothing. -/
structure IsPartitionedCollection (C K R : D) : Prop where
  /-- The partition key is a structural subtype of the element grain. -/
  key_ssub : ssub K (grain R)
  /-- The partition key is grain-irreducible. -/
  key_irred : IsIrreducible K
  /-- One inhabitant per key: the collection is isomorphic to the key. -/
  fibers : iso C K

/-- **Proposition [Grain of a partitioned collection], first half.**
    `G[Coll_K R] = K`.

    Immediate from Definition 3.1: the collection is isomorphic to `K` by the
    fiber correspondence, and `K` is irreducible by the definition of a
    partition key. Grain-hood factors into exactly those two clauses. -/
theorem partitioned_grain {C K R : D} (h : IsPartitionedCollection C K R) :
    IsGrainOf K C :=
  IsGrainOf.mk' (iso_symm _ _ h.fibers) h.key_irred

/-- The grain of the partitioned collection is the partition key, up to the
    isomorphism by which any two grains agree. -/
theorem partitioned_grain_iso {C K R : D} (h : IsPartitionedCollection C K R) :
    iso (grain C) K :=
  multiple_grains_iso (grain_isGrainOf C) (partitioned_grain h)

/-- **Proposition [Grain of a partitioned collection], second half.**
    The element grain decomposes as `G[R] = K × V` with `V = G[R] -_typ K`.

    "The key `K` is shared by all elements within one collection inhabitant, and
    `V` identifies an element inside its fiber." This is the type-difference
    split of the product `G[R]` into `K` and its complement, which needs the
    partition key to be a *structural* subtype — as the definition requires. -/
theorem partitioned_element_grain_split {C K R : D}
    (h : IsPartitionedCollection C K R) :
    iso (grain R) (prod (diff (grain R) K) K) :=
  diff_prod_iso (grain R) K h.key_ssub

/-- Both halves together, as the proposition states them. -/
theorem partitioned_grain_proposition {C K R : D}
    (h : IsPartitionedCollection C K R) :
    IsGrainOf K C ∧ iso (grain R) (prod (diff (grain R) K) K) :=
  ⟨partitioned_grain h, partitioned_element_grain_split h⟩

/-- **Why CalcG reaches streaming pipelines.** The grain of the partitioned
    collection is `K` — and `K` is a partition *key*, a finite product type, no
    matter what the fibers hold. Nothing in the statement mentions the fiber, so
    an unbounded one costs nothing: the same grain reasoning applies to
    `Coll_K R` as to a relational collection.

    Formally: the collection's grain depends only on `K`. Two partitioned
    collections over the same key have isomorphic grains, whatever their
    element types. -/
theorem partitioned_grain_independent_of_fiber
    {C₁ C₂ K R₁ R₂ : D}
    (h₁ : IsPartitionedCollection C₁ K R₁)
    (h₂ : IsPartitionedCollection C₂ K R₂) :
    iso (grain C₁) (grain C₂) :=
  iso_trans _ _ _ (partitioned_grain_iso h₁)
    (iso_symm _ _ (partitioned_grain_iso h₂))

end GrainTheory.ADT
