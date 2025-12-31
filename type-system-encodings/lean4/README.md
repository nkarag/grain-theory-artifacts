# Lean 4 Grain Encoding Implementation

This folder contains the Lean 4 implementation of grain-aware type checking using Approach B: Type Class for Grained Data.

## Files

- `GrainDefinitions.lean`: Core grain definitions (IsGrainOf relation)
- `GrainedData.lean`: Type class implementation with Customer examples

## Building

```bash
lake build
```

## Type Checking

The Lean 4 type checker automatically enforces grain compatibility:

```lean
-- ✓ Type checks: uses entity grain instance
#check extractGrains ([customer1, customer2] : List Customer)

-- ✗ Type error: grain mismatch
-- Cannot join entity grain with versioned grain
-- #check joinSameGrain
--   ([customer1] : List Customer)  -- entity grain
--   (Versioned.data)               -- versioned grain
```

## Grain Examples

Based on the paper (Section 3.2: Grain Determines Data Semantics):

1. **Entity Grain** (`CustomerEntityGrain`): `G[Customer] = CustomerId`
   - One distinct customer per `CustomerId`
   - No inherent ordering

2. **Versioned Grain** (`CustomerVersionedGrain`): `G[Customer] = CustomerId × EffectiveFrom`
   - Multiple time-stamped versions per customer
   - Causal ordering among versions

3. **Event Grain** (`CustomerEventGrain`): `G[Customer] = CustomerId × CreatedOn × EventType`
   - Each creation/modification event
   - Allows `CustomerId` reuse across events

## Type Class Approach

The `GrainedData R G` type class:
- Encodes grain relation as implicit parameter
- Enables automatic grain inference via instance resolution
- Provides `grain : R → G` and `fromGrain : G → R` functions
- Includes proofs of isomorphism

Multiple instances for the same type are disambiguated using namespaces:
- Default namespace: Entity grain
- `Versioned` namespace: Versioned grain
- `Event` namespace: Event grain

