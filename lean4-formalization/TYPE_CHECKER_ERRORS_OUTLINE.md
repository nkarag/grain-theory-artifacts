# Type-Checker Error Examples: Grain-Aware Compile-Time Verification

This document outlines five Lean 4 examples demonstrating how grain-aware type checking catches semantic mismatches at compile time, before any data processing.

## Overview

These examples demonstrate that **grain-aware type checking enables compile-time error detection** for data transformation bugs. Unlike schema-only checking (which only verifies structural compatibility), grain-aware types catch **semantic mismatches** where the same data structure represents different meanings based on grain definition.

All examples use a common `GrainDefinitions.lean` module that provides the formal definitions of grain and grain relations based on the paper's theoretical framework (Section 3: Grain Theory Foundations, Section 4: Grain Relations and Lattice). This ensures consistency and accuracy across all examples.

## Key Insight

The same data type with different grain definitions represents completely different semantics:
- `G[Customer] = CustomerId` → **Entity semantics** (distinct customer entities)
- `G[Customer] = CustomerId × EffectiveFrom` → **Versioned/temporal semantics** (customer versions over time)
- `G[Customer] = CustomerId × CreatedOn` → **Event semantics** (customer creation events)

Grain-aware type checking prevents using data with wrong grain semantics, even when the schema matches.

---

## Option A: Grain Semantics Mismatch in Function Signature

**File**: `TypeCheckerErrorA.lean`

**Demonstrates**: The SAME Customer type structure with DIFFERENT grain semantics cannot be used interchangeably → type error

**Scenario**:
- Define THE SAME `Customer` type structure (same fields: customerId, name, email, address, effectiveFrom)
- Define grain annotations: `CustomerEntityGrain` (grain = `CustomerId`) vs `CustomerVersionedGrain` (grain = `CustomerId × EffectiveFrom`)
- Create `CustomerWithGrain` type that encodes grain semantics in the type system
- Function `processEntityCustomer` expects `CustomerWithGrain CustomerEntityGrain`
- Try to pass `CustomerWithGrain CustomerVersionedGrain` → **Type error**: grain semantics don't match

**Key Point**: The SAME Customer structure with DIFFERENT grain semantics creates different types. The type checker enforces grain semantics, not just structural compatibility. This catches semantic mismatches that schema-only checking would miss.

---

## Option B: Incorrect Grain Inference Formula Application

**File**: `TypeCheckerErrorB.lean`

**Demonstrates**: Asserting wrong grain after applying inference formula → type error in proof

**Scenario**:
- Apply grouping formula: `γ_{CustomerId}(CustomerVersioned)` 
- Grain inference: `G[Res] = CustomerId × EffectiveFrom` (grouping preserves grain when grouping columns include grain)
- Try to assert: `G[Res] = CustomerId` (wrong - loses versioning semantics)
- **Type error**: Proof fails because computed grain doesn't match asserted grain

**Key Point**: Grain inference formulas are type-checked. Incorrect assertions are caught at compile time.

---

## Option C: Pipeline Composition with Grain Semantics Mismatch

**File**: `TypeCheckerErrorC.lean`

**Demonstrates**: The SAME Customer type with DIFFERENT grain semantics cannot be composed incorrectly → type error

**Scenario**:
- Define THE SAME `Customer` type structure
- Pipeline step `aggregateByCustomer` expects `CustomerWithGrain CustomerEntityGrain` (entity semantics)
- Try to compose with `CustomerWithGrain CustomerVersionedGrain` (versioned semantics)
- **Type error**: Pipeline composition fails because grain semantics don't match

**Key Point**: The SAME Customer structure with DIFFERENT grain semantics creates different types. Grain-aware types prevent incorrect pipeline composition based on semantic mismatches, not just structural differences. This prevents losing versioning information during aggregation.

---

## Option D: Parameterized Type with Grain Type Parameter

**File**: `TypeCheckerErrorD.lean`

**Demonstrates**: The SAME CustomerData structure with DIFFERENT grain type parameters creates different types → type error

**Scenario**:
- Define THE SAME `CustomerData` structure (same fields)
- Define `DataFrame (Grain := EntityGrain)` for entity semantics
- Define `DataFrame (Grain := VersionedGrain)` for versioned semantics
- Function `processEntityDataFrame` expects `DataFrame EntityGrain`
- Try to use `DataFrame VersionedGrain` → **Type error**: Grain type parameters don't match

**Key Point**: The SAME CustomerData structure with DIFFERENT grain type parameters creates different types (`DataFrame EntityGrain ≠ DataFrame VersionedGrain`). Grain can be encoded as a type parameter in a parameterized type, enabling compile-time checking of semantic correctness. This catches semantic mismatches that schema-only checking would miss.

---

## Option E: Temporal Aggregation with Wrong Grain Assumption

**File**: `TypeCheckerErrorE.lean`

**Demonstrates**: The SAME Customer type with versioned grain cannot be incorrectly aggregated → type error

**Scenario**:
- Define THE SAME `Customer` type structure
- Customer has versioned grain: `CustomerWithGrain CustomerVersionedGrain` (grain = `CustomerId × EffectiveFrom`)
- Try to aggregate by only `CustomerId`, losing versioning information
- Assert result `CustomerAggregatedByCustomerId` has grain = `CustomerVersionedGrain`
- **Type error**: Cannot prove grain equivalence - aggregation doesn't preserve grain semantics

**Key Point**: The SAME Customer structure with versioned grain semantics cannot be incorrectly aggregated. Grain-aware types prevent semantic loss during transformations (e.g., losing versioning information). The type system enforces that transformations must preserve or correctly transform grain, catching semantic errors at compile time.

---

## Common Structure

All files import common grain definitions from `GrainDefinitions.lean`, which provides:
- `IsGrainOf G R`: Definition of grain (G is the grain of R)
- `R1 ≡_g R2`: Grain equality (isomorphism between grains)
- `R1 ≤_g R2`: Grain ordering (functional dependency)
- `R1 <_g R2`: Strict grain ordering (finer grain)
- `R1 ⟨⟩_g R2`: Grain incomparability (many-to-many relationship)
- `TypeSubset A B`: Type-level subset relation

Each example file follows this structure:

1. **Imports**: Import `GrainDefinitions` and Mathlib dependencies
2. **Type Definitions**: Define base types and Customer types with different grain semantics
3. **Grain Proofs**: Prove grain relations using `IsGrainOf` for each Customer type
4. **Grain-Aware Functions**: Define functions that require specific grain semantics
5. **Type Error Demonstration**: Attempt to use wrong grain → type checker rejects

## Significance

These examples demonstrate that:

1. **Grain-aware type checking is more powerful than schema checking**: Catches semantic mismatches that structural type checking misses
2. **Compile-time verification**: Errors are caught before data processing, enabling "verify and deploy" workflows
3. **Semantic correctness**: Ensures data transformations preserve or correctly transform grain semantics
4. **Foundation for automated tools**: Type-level grain checking can be integrated into data pipeline development tools

## Connection to Paper

These examples directly support the paper's claim:

> "The grain inference formulas enable correctness verification at compile time by allowing engineers to compute the expected grain and verify that actual results match expectations, proactively detecting bugs before data processing."

They demonstrate that grain-aware type systems can catch errors that would otherwise require runtime testing or manual inspection.

### Formal Definitions

All examples use the formal definitions from `GrainDefinitions.lean`, which precisely implements:
- **Definition 3.1** (Grain): `IsGrainOf G R` - G is the grain of R if G ⊆_{typ} R and G ≅ R
- **Definition 4.1** (Grain Equality): `R1 ≡_g R2` - Grain equality as isomorphism
- **Definition 4.2** (Grain Ordering): `R1 ≤_g R2` - Grain ordering as functional dependency
- **Definition 4.3** (Grain Incomparability): `R1 ⟨⟩_g R2` - Incomparable grains

This ensures the Lean 4 formalization accurately reflects the paper's theoretical framework.

## Compilation

All files compile successfully with Lean 4. To compile:

```bash
cd formal_verification
lake env lean --root=. GrainDefinitions.lean  # Build common definitions first
lake env lean --root=. TypeCheckerErrorA.lean  # Then compile individual examples
```

All files have been verified to compile without errors (only expected `sorry` warnings for placeholder proofs).

