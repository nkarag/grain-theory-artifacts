# Agda Behavioral Classes — Mechanized Type Class Definitions

This artifact contains the Agda implementation of the behavioral type classes
from Section 5 (Definition 5.5) of the PODS 2027 paper. Each behavioral class
is an Agda `record` (type class) with an explicit `grain-cond` field that
constrains the grain structure relative to the entity key — mechanizing the
grain conditions in Table 2 of the paper.

## What This Demonstrates

1. **Behavioral classes are formal type classes**, not informal taxonomy.
   Each class is a record with a `grain-cond : Grain ≡ ...` field that the
   type checker enforces.

2. **Temporal components are generic type parameters**, not nominal types.
   `EventDtm`, `FromDtm`, `SnapshotDtm` are type variables constrained
   to carry `TotalOrd` or `StrictTotalOrd` — any ordered type qualifies.

3. **The subclass hierarchy is mechanized** via Agda's instance mechanism:
   `IsMultiVersion` contains `overlap {{is-an-event}} : IsEvent` as a
   superclass field; `IsSnapshot` contains `overlap {{is-a-seq-event}} : IsSeqEvent`.

4. **Additional constraints are formal record fields**:
   `consecutive-versions-cons` for `IsMultiVersion`,
   `is-complete-entity-coverage` for `IsSnapshot`.

## Correspondence to Paper (Table 2)

| Paper Class    | Agda Record      | Grain Condition Field                              | Ordering          |
|----------------|-------------------|----------------------------------------------------|-------------------|
| IsEntity       | `IsEntity`        | `Grain ≡ EntityKey`                                | —                 |
| IsEvent        | `IsEvent`         | `Grain ≡ (EntityKey × Event-dtm)`                  | `TotalOrd`        |
| IsMultiVersion | `IsMultiVersion`  | inherited from `IsEvent` (superclass)               | `TotalOrd`        |
| IsSeqEvent     | `IsSeqEvent`      | `Grain ≡ EntityKey × Grain ≡ Event-dtm`            | `StrictTotalOrd`  |
| IsSnapshot     | `IsSnapshot`      | inherited from `IsSeqEvent` (superclass)            | `StrictTotalOrd`  |

The Agda implementation includes four additional classes beyond the five
core classes in the paper: `IsOrdered`, `IsSeqOrdered`, `HasParent`, and
`IsNMRelation` (noted as deferred to subsequent work in the paper).

## Module Structure

```
agda-behavioral-classes/
├── pdl.agda-lib              # Agda library file (depends on standard-library)
├── GrainTheory/
│   ├── Ordering.agda         # Ordering type classes (PreOrd, TotalOrd, StrictTotalOrd)
│   ├── Types.agda            # Field definitions, field subset relation
│   ├── Operations.agda       # Type-level operations (⊆typ, ∪typ, ∩typ, -typ)
│   └── Relations.agda        # Grain definition (IsGrainOf), Entity, EntityKey, IsData,
│                              # grain relations (≡g, ≤g, ⟨⟩g), Armstrong axioms
├── GrainTheory.agda          # Root module aggregating all GrainTheory submodules
└── PDA/
    ├── Collections.agda      # Data collection abstraction (IsDataColl), grain-unique
    │                          # insertion, collection operations
    ├── Relations.agda         # Collection-level relations (=c, =g-coll, ⊆g, etc.)
    └── BehavioralClasses.agda # ** THE MAIN FILE ** — all 9 behavioral type classes,
                                # witness system (BehavioralTypeClassWitness, BC[_]),
                                # and worked examples (Customer as IsEntity, Order as IsEvent)
```

## Prerequisites

- **Agda** 2.6.3 or later
- **Agda standard library** (agda-stdlib)

## Verification

```bash
# Type-check the behavioral classes (includes all dependencies)
agda PDA/BehavioralClasses.agda
```

A successful run produces `Checking PDA.BehavioralClasses ...` lines for
all 8 modules with no errors. No output beyond the checking messages means
all definitions type-check and all grain conditions are well-formed.

## Key Definitions to Examine

- **`IsEntity`** (line 10): Simplest class — `grain-cond : Grain ≡ EntityKey`
- **`IsEvent`** (line 22): Generic `Event-dtm` parameter with `TotalOrd` constraint
- **`IsMultiVersion`** (line 109): Superclass `IsEvent`, adds `consecutive-versions-cons`
- **`IsSnapshot`** (line 209): Superclass `IsSeqEvent`, adds `is-complete-entity-coverage`
- **`BehavioralTypeClassWitness`** (line 402): Sum type carrying actual instances
- **`BC[_]`** (line 501): Behavioral class operator — returns the tag via instance resolution
- **Example** (line 514): Customer as `IsEntity`, Order as `IsEvent`, with `BC[ Customer ] ≡ Entity-Tag` proved by `refl`
