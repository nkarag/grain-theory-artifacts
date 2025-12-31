/-
  Grain Definitions for Type Class Approach
  "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

  This file contains the formal definitions of grain and grain relations.
  Based on Section 3 (Grain Theory Foundations) and Section 4 (Grain Relations and Lattice).
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

-- ============================================================================
-- GRAIN DEFINITION
-- ============================================================================

-- Type-level subset relation: A ⊆_{typ} B means there exists a surjective projection B → A
def TypeSubset (A B : Type) : Prop :=
  ∃ (p : B → A), Function.Surjective p

infix:50 " ⊆_{typ} " => TypeSubset

-- Grain definition: G is the grain of R if:
-- 1. G ⊆_{typ} R (G is a type-level subset of R)
-- 2. G ≅ R (G and R are isomorphic)
def _IsGrainOf_ (G R : Type) : Prop :=
  ∃ (f : G → R) (g : R → G),
    Function.Bijective f ∧ Function.LeftInverse g f ∧ Function.RightInverse g f

-- Alias for backward compatibility
def IsGrainOf := _IsGrainOf_

-- Infix notation: G IsGrainOf R
infix:50 " IsGrainOf " => _IsGrainOf_
