/-
  Type-Checker Error Example D: Parameterized Type with Grain Type Parameter
  "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

  This demonstrates encoding grain as a type parameter in a parameterized type.
  The SAME Customer data structure with DIFFERENT grain type parameters creates different types,
  and the type system enforces grain semantics at compile time.

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

-- Grain type parameters
-- G[CustomerData] = EntityGrain (entity semantics)
structure EntityGrain : Type where
  customerId : CustomerId

-- G[CustomerData] = VersionedGrain (versioned semantics)
structure VersionedGrain : Type where
  customerId : CustomerId
  effectiveFrom : EffectiveFrom

-- THE SAME Customer data structure
structure CustomerData : Type where
  customerId : CustomerId
  effectiveFrom : EffectiveFrom
  name : Name
  email : Email

-- Parameterized type: DataFrame parameterized by grain type
-- The grain type parameter enforces semantic correctness
-- THE SAME CustomerData with DIFFERENT grain type parameters = DIFFERENT types
structure DataFrame (Grain : Type) : Type where
  data : List CustomerData  -- Same data structure
  -- In a full implementation, this would contain actual data rows
  -- The key is that Grain type parameter differentiates semantics

-- Type-level function to extract grain from CustomerData
-- This shows how the SAME data can have different grain semantics
def extractEntityGrain (c : CustomerData) : EntityGrain :=
  { customerId := c.customerId }

def extractVersionedGrain (c : CustomerData) : VersionedGrain :=
  { customerId := c.customerId, effectiveFrom := c.effectiveFrom }

-- ============================================================================
-- TYPE CHECKER ERROR DEMONSTRATION
-- ============================================================================

-- This will cause a TYPE ERROR at compile time:
-- Trying to use DataFrame with versioned grain where entity grain is expected

-- Function expecting entity semantics (grain = CustomerId)
-- This function assumes one row per customer (entity semantics)
def processEntityDataFrame (df : DataFrame EntityGrain) : List CustomerId :=
  df.data.map (λ c => c.customerId)

-- Uncomment the following to see the type error:
def incorrectUsage (versionedDf : DataFrame VersionedGrain) : List CustomerId :=
  processEntityDataFrame versionedDf  -- TYPE ERROR: type mismatch
  -- Error: type mismatch
  --   DataFrame VersionedGrain
  -- is not convertible to
  --   DataFrame EntityGrain

-- The type checker rejects this because:
-- 1. The SAME CustomerData structure is used in both DataFrames
-- 2. But DataFrame EntityGrain ≠ DataFrame VersionedGrain (different grain type parameters)
-- 3. EntityGrain ≠ VersionedGrain (different grain types)
-- 4. processEntityDataFrame requires entity semantics (one row per customer)
-- 5. Using versioned DataFrame where entity DataFrame is expected would be semantically incorrect
-- 6. The parameterized type system enforces this at compile time through the grain type parameter

-- ============================================================================
-- KEY INSIGHT: This is NOT just structural type checking
-- ============================================================================

-- The CustomerData structure is THE SAME in both cases:
-- - Same fields: customerId, effectiveFrom, name, email
-- - Same structure: CustomerData

-- But the GRAIN PARAMETERS are different:
-- - DataFrame EntityGrain: grain = CustomerId (entity semantics)
-- - DataFrame VersionedGrain: grain = CustomerId × EffectiveFrom (versioned semantics)

-- Grain-aware type checking through parameterized types:
-- 1. Same data structure (CustomerData)
-- 2. Different grain type parameters (EntityGrain vs VersionedGrain)
-- 3. Different types (DataFrame EntityGrain ≠ DataFrame VersionedGrain)
-- 4. Type system enforces grain semantics at compile time
-- 5. This catches semantic mismatches that schema-only checking would miss

-- ============================================================================
-- CORRECT USAGE
-- ============================================================================

-- Correct: Use entity DataFrame with entity-processing function
-- def createEntityDataFrame (data : List CustomerData) : DataFrame EntityGrain :=
--   { data := data }  -- ✓ Type checks correctly

-- def correctUsage (entityDf : DataFrame EntityGrain) : List CustomerId :=
--   processEntityDataFrame entityDf  -- ✓ Type checks correctly

-- Correct: Process versioned DataFrame with versioned-processing function
-- def processVersionedDataFrame (df : DataFrame VersionedGrain) : List (CustomerId × EffectiveFrom) :=
--   df.data.map (λ c => (c.customerId, c.effectiveFrom))  -- ✓ Preserves versioning semantics
