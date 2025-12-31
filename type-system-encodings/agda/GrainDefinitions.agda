{-
  Grain Definitions for Type Class Approach
  "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

  This file contains the formal definitions of grain and grain relations.
  Based on Section 3 (Grain Theory Foundations) and Section 4 (Grain Relations and Lattice).
-}

module GrainDefinitions where

open import Level using (Level; suc)
open import Function using (_∘_; id)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ============================================================================
-- GRAIN DEFINITION
-- ============================================================================

-- Grain definition: G is the grain of R if:
-- 1. G ⊆_{typ} R (G is a type-level subset of R)
-- 2. G ≅ R (G and R are isomorphic)
-- For simplicity, we focus on the isomorphism requirement here
_IsGrainOf_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
G IsGrainOf R =
    ∃ λ (grain : R → G) →
        ∃ λ (fg : G → R) →
              (∀ r → fg (grain r) ≡ r)
            × (∀ g → grain (fg g) ≡ g)

