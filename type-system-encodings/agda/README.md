# Agda Grain Encoding Implementation

This folder contains the Agda implementation of grain-aware type checking using Approach B: Type Class for Grained Data.

## Files

- `GrainDefinitions.agda`: Core grain definitions (`_IsGrainOf_` relation)
- `GrainedData.agda`: Type class implementation with Customer examples

## Building

```bash
agda GrainedData.agda
```

## Type Checking

The Agda type checker automatically enforces grain compatibility:

```agda
-- ✓ Type checks: uses entity grain instance
_ : List CustomerEntityGrain
_ = extractGrains (customer1 ∷ customer2 ∷ [])

-- ✗ Type error: grain mismatch
-- Cannot join entity grain with versioned grain
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

The `IsData` record:
- Encodes grain relation as a parameter
- Enables automatic grain inference via instance arguments (Agda 2.6+)
- Provides `grain : R → G` and `fromGrain : G → R` functions
- Includes proofs of isomorphism

Multiple instances for the same type are disambiguated using modules:
- Default module: Entity grain
- `Versioned` module: Versioned grain
- `Event` module: Event grain

## Equivalence with Lean 4

This implementation is **fully equivalent** to the Lean 4 version in `../lean4/GrainedData.lean`:
- Same type class pattern (`IsData` / `GrainedData`)
- Same grain types and functions
- Same namespace/module structure for disambiguation
- Same grain-aware functions

The only differences are syntactic (Agda's mixfix notation vs Lean 4's notation).

