/-
  Type-Checker Error Example C: Pipeline Composition with Grain Semantics Mismatch
  "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

  This demonstrates that grain-aware types prevent incorrect pipeline composition.
  The SAME Customer type with DIFFERENT grain semantics cannot be composed incorrectly.
  The type system enforces grain semantics, not just structural compatibility.

  THE TYPE CHECKER WILL REJECT THIS CODE - demonstrating compile-time grain verification.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import GrainDefinitions

-- Domain types
structure CustomerId : Type where
structure EffectiveFrom : Type where
structure Name : Type where
structure Email : Type where

-- THE SAME Customer type structure
structure Customer : Type where
  customerId : CustomerId
  effectiveFrom : EffectiveFrom
  name : Name
  email : Email

-- Grain types (different semantics for SAME Customer structure)
-- G[Customer] = CustomerEntityGrain (entity semantics)
structure CustomerEntityGrain : Type where
  customerId : CustomerId

-- G[Customer] = CustomerVersionedGrain (versioned semantics)
structure CustomerVersionedGrain : Type where
  customerId : CustomerId
  effectiveFrom : EffectiveFrom

-- Customer annotated with grain semantics
structure CustomerWithGrain (Grain : Type) : Type where
  data : Customer
  grainProof : IsGrainOf Grain Customer

-- Aggregated result
structure CustomerAggregated : Type where
  customerId : CustomerId
  totalCount : Nat

-- ============================================================================
-- PIPELINE STEP: Aggregate by Customer (expects entity semantics)
-- ============================================================================

-- This function expects Customer with entity grain semantics
-- It assumes one row per customer (entity semantics)
def aggregateByCustomer (customers : List (CustomerWithGrain CustomerEntityGrain)) : List CustomerAggregated :=
  customers.map (λ c => { customerId := c.data.customerId, totalCount := 1 })

-- ============================================================================
-- TYPE CHECKER ERROR DEMONSTRATION
-- ============================================================================

-- This will cause a TYPE ERROR at compile time:
-- Trying to compose pipeline step expecting entity semantics with versioned data

-- Uncomment the following to see the type error:
def incorrectPipelineComposition (versionedCustomers : List (CustomerWithGrain CustomerVersionedGrain)) : List CustomerAggregated :=
  aggregateByCustomer versionedCustomers  -- TYPE ERROR: type mismatch
  -- Error: type mismatch
  --   List (CustomerWithGrain CustomerVersionedGrain)
  -- is not convertible to
  --   List (CustomerWithGrain CustomerEntityGrain)

-- The type checker rejects this because:
-- 1. The SAME Customer structure has DIFFERENT grain semantics
-- 2. aggregateByCustomer requires entity semantics (one row per customer)
-- 3. CustomerVersionedGrain ≠ CustomerEntityGrain (different grain types)
-- 4. Using versioned data where entity data is expected would:
--    - Lose versioning information (EffectiveFrom)
--    - Incorrectly aggregate multiple versions as if they were one entity
--    - Produce semantically incorrect results
-- 5. The grain annotation in the type system prevents this semantic mismatch

-- ============================================================================
-- KEY INSIGHT: This is NOT just structural type checking
-- ============================================================================

-- The Customer type structure is THE SAME:
-- - Same fields: customerId, effectiveFrom, name, email
-- - Same structure: Customer

-- But the GRAIN SEMANTICS are different:
-- - Entity grain: G[Customer] = CustomerId (one row per customer)
-- - Versioned grain: G[Customer] = CustomerId × EffectiveFrom (multiple versions per customer)

-- Grain-aware type checking enforces SEMANTIC correctness:
-- - Prevents using versioned data where entity data is expected
-- - Prevents losing versioning information during aggregation
-- - Catches semantic mismatches that schema-only checking would miss

-- ============================================================================
-- CORRECT USAGE
-- ============================================================================

-- Correct: Use entity Customer with entity-processing pipeline
def correctPipelineComposition (entityCustomers : List (CustomerWithGrain CustomerEntityGrain)) : List CustomerAggregated :=
  aggregateByCustomer entityCustomers  -- ✓ Type checks correctly

-- Correct: Process versioned Customer with versioned-aware pipeline
def aggregateVersionedCustomers (versionedCustomers : List (CustomerWithGrain CustomerVersionedGrain)) : List (CustomerId × EffectiveFrom × Nat) :=
  -- Group by CustomerId × EffectiveFrom (preserves versioning)
  versionedCustomers.map (λ c => (c.data.customerId, c.data.effectiveFrom, 1))  -- ✓ Preserves grain semantics
