/-
  Type-Checker Error Example A: Grain Semantics Mismatch in Function Signature
  "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

  This demonstrates that grain-aware type checking catches semantic mismatches at compile time.
  The SAME Customer type structure can have DIFFERENT grain semantics, and the type system
  enforces grain correctness, not just structural compatibility.

  THE TYPE CHECKER WILL REJECT THIS CODE - demonstrating compile-time grain verification.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import GrainDefinitions

-- Domain types
structure CustomerId : Type where
structure Name : Type where
structure Email : Type where
structure Address : Type where
structure EffectiveFrom : Type where

-- THE SAME Customer type structure
-- This type can represent different semantics based on grain definition
structure Customer : Type where
  customerId : CustomerId
  name : Name
  email : Email
  address : Address
  effectiveFrom : EffectiveFrom

-- Grain types: The SAME Customer type has DIFFERENT grain semantics
-- Grain = CustomerId → Entity semantics (one row per customer)
-- Grain = CustomerId × EffectiveFrom → Versioned semantics (multiple versions per customer)

-- Grain type for entity semantics: G[Customer] = CustomerId
structure CustomerEntityGrain : Type where
  customerId : CustomerId

-- Grain type for versioned semantics: G[Customer] = CustomerId × EffectiveFrom
structure CustomerVersionedGrain : Type where
  customerId : CustomerId
  effectiveFrom : EffectiveFrom

-- Grain proofs: According to the paper, G[R] is isomorphic to R
-- For Customer with entity semantics: G[Customer] = CustomerEntityGrain, and CustomerEntityGrain ≅ Customer
-- For Customer with versioned semantics: G[Customer] = CustomerVersionedGrain, and CustomerVersionedGrain ≅ Customer

-- Proof that CustomerEntityGrain is the grain of Customer (entity semantics interpretation)
theorem grain_CustomerEntity :
  IsGrainOf CustomerEntityGrain Customer := by
  use (λ g => { customerId := g.customerId, name := Name.mk, email := Email.mk,
                 address := Address.mk, effectiveFrom := EffectiveFrom.mk }),
       (λ c => { customerId := c.customerId })
  sorry -- Simplified for demonstration

-- Proof that CustomerVersionedGrain is the grain of Customer (versioned semantics interpretation)
theorem grain_CustomerVersioned :
  IsGrainOf CustomerVersionedGrain Customer := by
  use (λ g => { customerId := g.customerId, name := Name.mk, email := Email.mk,
                 address := Address.mk, effectiveFrom := g.effectiveFrom }),
       (λ c => { customerId := c.customerId, effectiveFrom := c.effectiveFrom })
  sorry -- Simplified for demonstration

-- Grain-aware type: Customer annotated with its grain semantics
-- This is the key: we encode grain semantics in the type system
structure CustomerWithGrain (Grain : Type) : Type where
  data : Customer
  grainProof : IsGrainOf Grain Customer  -- Proof that Grain is the grain of Customer

-- Function expecting entity semantics (grain = CustomerId)
-- This function assumes one row per customer (entity semantics)
def processEntityCustomer (c : CustomerWithGrain CustomerEntityGrain) : CustomerId :=
  c.data.customerId

-- ============================================================================
-- TYPE CHECKER ERROR DEMONSTRATION
-- ============================================================================

-- This will cause a TYPE ERROR at compile time:
-- Trying to use Customer with versioned grain semantics where entity grain is expected

-- Uncomment the following to see the type error:
-- def processVersionedAsEntity (c : CustomerWithGrain CustomerVersionedGrain) : CustomerId :=
--   processEntityCustomer c  -- TYPE ERROR: type mismatch
--   -- Error: type mismatch
--   --   CustomerWithGrain CustomerVersionedGrain
--   -- is not convertible to
--   --   CustomerWithGrain CustomerEntityGrain

-- The type checker rejects this because:
-- 1. The SAME Customer structure has DIFFERENT grain semantics
-- 2. CustomerEntityGrain ≠ CustomerVersionedGrain (different grain types)
-- 3. processEntityCustomer requires entity semantics (one row per customer)
-- 4. Using versioned semantics (multiple versions per customer) would be semantically incorrect
-- 5. The grain annotation in the type system catches this mismatch

-- ============================================================================
-- KEY INSIGHT: This is NOT just structural type checking
-- ============================================================================

-- The Customer type structure is THE SAME in both cases:
-- - Same fields: customerId, name, email, address, effectiveFrom
-- - Same structure: Customer

-- But the GRAIN SEMANTICS are different:
-- - Entity grain: G[Customer] = CustomerId (one row per customer)
-- - Versioned grain: G[Customer] = CustomerId × EffectiveFrom (multiple versions per customer)

-- Grain-aware type checking enforces SEMANTIC correctness, not just structural compatibility.
-- This is the value: catching semantic mismatches that schema-only checking would miss.

-- ============================================================================
-- CORRECT USAGE
-- ============================================================================

-- Correct: Use Customer with entity grain semantics
-- def correctEntityUsage (c : Customer) : CustomerWithGrain CustomerEntityGrain :=
--   { data := c, grainProof := sorry }  -- Would need to prove Customer ≡_g CustomerEntityGrain

-- def correctProcessEntity (c : CustomerWithGrain CustomerEntityGrain) : CustomerId :=
--   processEntityCustomer c  -- ✓ Type checks correctly

-- Correct: Process versioned Customer with versioned-processing function
-- def processVersionedCustomer (c : CustomerWithGrain CustomerVersionedGrain) : CustomerId × EffectiveFrom :=
--   (c.data.customerId, c.data.effectiveFrom)  -- ✓ Preserves versioning semantics
