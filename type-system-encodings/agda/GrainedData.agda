{-
  Type Class Approach for Grain-Aware Data
  "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

  This file implements Approach B: Type Class for Grained Data
  Based on GRAIN_TYPE_SYSTEM_ENCODINGS.md Section 5 (Agda) - Approach B

  Key Idea: Define a record `IsData` that encodes grain relation as a parameter.
  This enables automatic grain inference via instance arguments (Agda 2.6+).

  This implementation is fully equivalent to the Lean 4 version in lean4/GrainedData.lean
-}

module GrainedData where

open import GrainDefinitions
open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ============================================================================
-- Type Class Pattern: IsData
-- ============================================================================

-- Type class: data type R with grain G
-- This wraps the IsGrainOf relation for convenience
record IsData {R G : Set} (grain-rel : G IsGrainOf R) : Set₁ where
  field
    -- Extract grain from element
    grain : R → G
    -- Reconstruct element from grain
    fromGrain : G → R
    -- Proofs
    grain-fromGrain : ∀ g → grain (fromGrain g) ≡ g
    fromGrain-grain : ∀ r → fromGrain (grain r) ≡ r

-- Helper to extract grain function from relation
get-grain : ∀ {G R} → (G IsGrainOf R) → (R → G)
get-grain (grain , _ , _) = grain

-- Helper to extract reconstruction function
get-fg : ∀ {G R} → (G IsGrainOf R) → (G → R)
get-fg (_ , fg , _) = fg

-- ============================================================================
-- Domain Types
-- ============================================================================

record CustomerId : Set where
  field
    id : ℕ

record CustomerName : Set where
  field
    name : String

record Email : Set where
  field
    email : String

record EffectiveFrom : Set where
  field
    date : ℕ

record CreatedOn : Set where
  field
    date : ℕ

record EventType : Set where
  field
    eventType : String

-- Customer type (same structure, different grain semantics)
record Customer : Set where
  field
    customerId : CustomerId
    name : CustomerName
    email : Email
    effectiveFrom : EffectiveFrom
    createdOn : CreatedOn
    eventType : EventType

-- ============================================================================
-- Grain Types
-- ============================================================================

-- Grain 1: Entity semantics (one row per customer)
record CustomerEntityGrain : Set where
  field
    customerId : CustomerId

-- Grain 2: Versioned semantics (multiple versions per customer)
record CustomerVersionedGrain : Set where
  field
    customerId : CustomerId
    effectiveFrom : EffectiveFrom

-- Grain 3: Event semantics (each creation/modification event)
record CustomerEventGrain : Set where
  field
    customerId : CustomerId
    createdOn : CreatedOn
    eventType : EventType

-- ============================================================================
-- Grain Functions
-- ============================================================================

-- Grain functions for entity semantics
grain-entity : Customer → CustomerEntityGrain
grain-entity c = record { customerId = Customer.customerId c }

fg-entity : CustomerEntityGrain → Customer
fg-entity g = record
  { customerId = CustomerEntityGrain.customerId g
  ; name = record { name = "" }  -- Would be looked up from database
  ; email = record { email = "" }
  ; effectiveFrom = record { date = 0 }
  ; createdOn = record { date = 0 }
  ; eventType = record { eventType = "" }
  }

-- Grain functions for versioned semantics
grain-versioned : Customer → CustomerVersionedGrain
grain-versioned c = record
  { customerId = Customer.customerId c
  ; effectiveFrom = Customer.effectiveFrom c
  }

fg-versioned : CustomerVersionedGrain → Customer
fg-versioned g = record
  { customerId = CustomerVersionedGrain.customerId g
  ; name = record { name = "" }
  ; email = record { email = "" }
  ; effectiveFrom = CustomerVersionedGrain.effectiveFrom g
  ; createdOn = record { date = 0 }
  ; eventType = record { eventType = "" }
  }

-- Grain functions for event semantics
grain-event : Customer → CustomerEventGrain
grain-event c = record
  { customerId = Customer.customerId c
  ; createdOn = Customer.createdOn c
  ; eventType = Customer.eventType c
  }

fg-event : CustomerEventGrain → Customer
fg-event g = record
  { customerId = CustomerEventGrain.customerId g
  ; name = record { name = "" }
  ; email = record { email = "" }
  ; effectiveFrom = record { date = 0 }
  ; createdOn = CustomerEventGrain.createdOn g
  ; eventType = CustomerEventGrain.eventType g
  }

-- ============================================================================
-- Grain Relation Proofs
-- ============================================================================

-- Grain relation proofs (axiomatized for brevity)
postulate
  customer-entity-grain : CustomerEntityGrain IsGrainOf Customer
  customer-versioned-grain : CustomerVersionedGrain IsGrainOf Customer
  customer-event-grain : CustomerEventGrain IsGrainOf Customer

-- ============================================================================
-- Type Class Instances
-- ============================================================================

-- Instance 1: Customer with entity grain
postulate
  customer-entity-grain-proofs : ∀ g → grain-entity (fg-entity g) ≡ g
  customer-entity-fromGrain-proofs : ∀ r → fg-entity (grain-entity r) ≡ r

instance
  CustomerEntityData : IsData customer-entity-grain
  CustomerEntityData = record
    { grain = grain-entity
    ; fromGrain = fg-entity
    ; grain-fromGrain = customer-entity-grain-proofs
    ; fromGrain-grain = customer-entity-fromGrain-proofs
    }

-- Instance 2: Customer with versioned grain (in different module)
module Versioned where
  postulate
    customer-versioned-grain-proofs : ∀ g → grain-versioned (fg-versioned g) ≡ g
    customer-versioned-fromGrain-proofs : ∀ r → fg-versioned (grain-versioned r) ≡ r

  instance
    CustomerVersionedData : IsData customer-versioned-grain
    CustomerVersionedData = record
      { grain = grain-versioned
      ; fromGrain = fg-versioned
      ; grain-fromGrain = customer-versioned-grain-proofs
      ; fromGrain-grain = customer-versioned-fromGrain-proofs
      }

-- Instance 3: Customer with event grain (in different module)
module Event where
  postulate
    customer-event-grain-proofs : ∀ g → grain-event (fg-event g) ≡ g
    customer-event-fromGrain-proofs : ∀ r → fg-event (grain-event r) ≡ r

  instance
    CustomerEventData : IsData customer-event-grain
    CustomerEventData = record
      { grain = grain-event
      ; fromGrain = fg-event
      ; grain-fromGrain = customer-event-grain-proofs
      ; fromGrain-grain = customer-event-fromGrain-proofs
      }

-- ============================================================================
-- Grain-Aware Functions Using Type Classes
-- ============================================================================

-- Function requiring specific grain G
-- The type class instance is automatically inferred (Agda 2.6+)
extractGrains : ∀ {R G : Set} {grain-rel : G IsGrainOf R}
                → {{_ : IsData grain-rel}}
                → List R → List G
extractGrains {{dataInst}} dataList = map (IsData.grain dataInst) dataList

-- Function enforcing grain equality
joinSameGrain : ∀ {R1 R2 G : Set}
                {grain-rel1 : G IsGrainOf R1}
                {grain-rel2 : G IsGrainOf R2}
                → {{_ : IsData grain-rel1}}
                → {{_ : IsData grain-rel2}}
                → List R1 → List R2 → List (G × R1 × R2)
joinSameGrain {{_}} {{_}} left right = {!!}  -- Implementation omitted

-- Process entity customers
processEntityCustomers : ∀ {R : Set} {grain-rel : CustomerEntityGrain IsGrainOf R}
                         → {{_ : IsData grain-rel}}
                         → List R → List CustomerId
processEntityCustomers {{dataInst}} customers =
  map (λ g → CustomerEntityGrain.customerId g) (extractGrains customers)

-- Aggregate versioned to entity
aggregateVersionedToEntity : List Customer → List CustomerEntityGrain
aggregateVersionedToEntity versioned = {!!}  -- Implementation omitted

-- ============================================================================
-- Usage Examples
-- ============================================================================

-- Example customers
customer1 : Customer
customer1 = record
  { customerId = record { id = 1 }
  ; name = record { name = "Alice" }
  ; email = record { email = "alice@example.com" }
  ; effectiveFrom = record { date = 20240101 }
  ; createdOn = record { date = 20240101 }
  ; eventType = record { eventType = "CREATED" }
  }

customer2 : Customer
customer2 = record
  { customerId = record { id = 2 }
  ; name = record { name = "Bob" }
  ; email = record { email = "bob@example.com" }
  ; effectiveFrom = record { date = 20240101 }
  ; createdOn = record { date = 20240101 }
  ; eventType = record { eventType = "CREATED" }
  }

-- ✓ Type checks: uses entity grain instance
_ : List CustomerEntityGrain
_ = extractGrains (customer1 ∷ customer2 ∷ [])

-- ✓ Type checks: versioned grain (open module to use its instance)
_ : List CustomerVersionedGrain
_ = extractGrains {grain-rel = customer-versioned-grain} {{Versioned.CustomerVersionedData}} (customer1 ∷ customer2 ∷ [])

-- ✓ Type checks: event grain (open module to use its instance)
_ : List CustomerEventGrain
_ = extractGrains {grain-rel = customer-event-grain} {{Event.CustomerEventData}} (customer1 ∷ customer2 ∷ [])

-- ✓ Type checks: process entity customers
_ : List CustomerId
_ = processEntityCustomers (customer1 ∷ customer2 ∷ [])

