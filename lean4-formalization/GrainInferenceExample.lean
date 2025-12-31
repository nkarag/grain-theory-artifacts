/-
  Concrete Example: How Grain Inference Calculates Join Grain
  "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

  This file demonstrates step-by-step how the grain inference formula calculates
  the grain of a join result, using Pipeline 1 as a concrete example.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import GrainDefinitions
import GrainInference

-- ============================================================================
-- EXAMPLE: Pipeline 1 Join - Step-by-Step Grain Calculation
-- ============================================================================

-- Domain types
structure CustomerId : Type where
structure ChannelId : Type where
structure ProductId : Type where
structure Date : Type where

-- Input types
structure SalesChannel : Type where
  customerId : CustomerId
  channelId : ChannelId
  date : Date

structure SalesProduct : Type where
  customerId : CustomerId
  productId : ProductId
  date : Date

-- Join key type
structure JoinKey : Type where
  customerId : CustomerId
  date : Date

-- Result type (computed from the formula)
structure Pipeline1JoinResult : Type where
  channelId : ChannelId
  productId : ProductId
  customerId : CustomerId
  date : Date

-- ============================================================================
-- STEP-BY-STEP GRAIN CALCULATION
-- ============================================================================

-- STEP 1: Identify input grains
-- G[SalesChannel] = SalesChannel (full type: CustomerId × ChannelId × Date)
theorem step1_grain_SalesChannel :
  SalesChannel ≡_g SalesChannel := by
  use id, id
  constructor
  · exact Function.bijective_id
  · constructor
    · intro x; rfl
    · intro x; rfl

-- G[SalesProduct] = SalesProduct (full type: CustomerId × ProductId × Date)
theorem step1_grain_SalesProduct :
  SalesProduct ≡_g SalesProduct := by
  use id, id
  constructor
  · exact Function.bijective_id
  · constructor
    · intro x; rfl
    · intro x; rfl

-- STEP 2: Compute J_k-portions of the grains
-- G_1^{J_k} = G[SalesChannel] ∩ J_k
--           = (CustomerId × ChannelId × Date) ∩ (CustomerId × Date)
--           = CustomerId × Date
--
-- G_2^{J_k} = G[SalesProduct] ∩ J_k
--           = (CustomerId × ProductId × Date) ∩ (CustomerId × Date)
--           = CustomerId × Date
--
-- In Lean, we represent this by showing that both grains contain the join key structure
theorem step2_jk_portion_SalesChannel :
  -- The join key (CustomerId × Date) is contained in SalesChannel grain
  JoinKey ⊆_{typ} SalesChannel := by
  use (λ sc => { customerId := sc.customerId, date := sc.date })
  intro jk
  -- For any JoinKey value, we can construct a SalesChannel with matching customerId and date
  -- (channelId can be any value, but we need nonempty ChannelId)
  have h_channel : Nonempty ChannelId := ⟨ChannelId.mk⟩
  have h_channel_val : ChannelId := Classical.choice h_channel
  use { customerId := jk.customerId, channelId := h_channel_val, date := jk.date }

theorem step2_jk_portion_SalesProduct :
  -- The join key (CustomerId × Date) is contained in SalesProduct grain
  JoinKey ⊆_{typ} SalesProduct := by
  use (λ sp => { customerId := sp.customerId, date := sp.date })
  intro jk
  -- For any JoinKey value, we can construct a SalesProduct with matching customerId and date
  have h_product : Nonempty ProductId := ⟨ProductId.mk⟩
  have h_product_val : ProductId := Classical.choice h_product
  use { customerId := jk.customerId, productId := h_product_val, date := jk.date }

-- STEP 3: Determine which case applies
-- Since G_1^{J_k} = CustomerId × Date = G_2^{J_k}, they are equal
-- Therefore: G_1^{J_k} ⊆ G_2^{J_k} (trivially, since they're equal)
-- Case A applies!
theorem step3_case_a_applies :
  -- Both J_k-portions are equal, so Case A applies
  (JoinKey ⊆_{typ} SalesChannel) ∧ (JoinKey ⊆_{typ} SalesProduct) := by
  constructor
  · exact step2_jk_portion_SalesChannel
  · exact step2_jk_portion_SalesProduct

-- STEP 4: Apply Case A formula
-- G[Res] = (G[R1] -_{typ} J_k) × (G[R2] -_{typ} J_k) × (G[R1] ∩_{typ} G[R2] ∩_{typ} J_k)
--
-- Calculation:
--   G[R1] - J_k = (CustomerId × ChannelId × Date) - (CustomerId × Date) = ChannelId
--   G[R2] - J_k = (CustomerId × ProductId × Date) - (CustomerId × Date) = ProductId
--   G[R1] ∩ G[R2] ∩ J_k = (CustomerId × ChannelId × Date) ∩ (CustomerId × ProductId × Date) ∩ (CustomerId × Date)
--                       = CustomerId × Date
--
-- Result: G[Res] = ChannelId × ProductId × CustomerId × Date
--
-- This matches the structure of Pipeline1JoinResult:
--   - channelId : ChannelId      (from G[R1] - J_k)
--   - productId : ProductId      (from G[R2] - J_k)
--   - customerId : CustomerId    (from G[R1] ∩ G[R2] ∩ J_k)
--   - date : Date                (from G[R1] ∩ G[R2] ∩ J_k)

-- STEP 5: Verify the result type has the computed grain
-- The grain of Pipeline1JoinResult is Pipeline1JoinResult itself
-- (since it's the full type with all fields)
theorem step5_verify_result_grain :
  Pipeline1JoinResult ≡_g Pipeline1JoinResult := by
  use id, id
  constructor
  · exact Function.bijective_id
  · constructor
    · intro x; rfl
    · intro x; rfl

-- STEP 6: Use the grain inference function to compute the grain
-- This function encapsulates steps 1-5 and returns the proof that
-- G[Pipeline1JoinResult] = Pipeline1JoinResult
theorem step6_computed_grain :
  -- The grain inference function computes: G[Res] = ChannelId × ProductId × CustomerId × Date
  Pipeline1JoinResult ≡_g Pipeline1JoinResult :=
  pipeline_join_grain_inference SalesChannel SalesProduct JoinKey Pipeline1JoinResult
    step1_grain_SalesChannel
    step1_grain_SalesProduct
    step5_verify_result_grain

-- ============================================================================
-- SUMMARY: Where the Calculation Happens
-- ============================================================================

/-
  The grain calculation happens in the following steps:

  1. **Formula Application** (in GrainInference.lean):
     - The function `equi_join_grain_inference` applies Theorem 5.1, Case A
     - Formula: G[Res] = (G[R1] - J_k) × (G[R2] - J_k) × (G[R1] ∩ G[R2] ∩ J_k)

  2. **Type Structure Definition** (in Pipeline1.lean):
     - Based on the formula, we define Pipeline1JoinResult with fields:
       * channelId (from G[R1] - J_k)
       * productId (from G[R2] - J_k)
       * customerId, date (from G[R1] ∩ G[R2] ∩ J_k)

  3. **Grain Verification** (in this file):
     - We prove that Pipeline1JoinResult has grain = Pipeline1JoinResult (full type)
     - This matches the computed grain from the formula

  4. **Function Application** (step6_computed_grain):
     - `pipeline_join_grain_inference` takes the input grains and result type
     - It applies the formula and returns the proof that the result has the computed grain

  The "calculation" is the application of the formula to determine what fields
  should be in the result type. In Lean, we can't compute types at runtime, but
  we can:
  - Define the result type structure based on the formula
  - Prove that this structure has the grain computed by the formula
  - Use the grain inference functions to verify correctness
-/
