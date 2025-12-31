/-
  Common Grain Definitions
  "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

  This file contains the formal definitions of grain and grain relations based on the paper.
  All type-checker error examples import these definitions.

  Based on Section 3 (Grain Theory Foundations) and Section 4 (Grain Relations and Lattice).
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

-- ============================================================================
-- GRAIN DEFINITION
-- ============================================================================

-- According to the paper (Definition 3.1):
-- Given a data type R, the grain of R, denoted G[R], is a subset of R, G[R] ⊆_{typ} R, such that:
-- 1. Isomorphism: G[R] and R are isomorphic sets G[R] ≅ R
-- 2. Irreducibility: No proper subset of G[R] can serve as the grain of R

-- In Lean, we represent grain as a type that is isomorphic to R
-- The grain G[R] is a type such that G[R] ≅ R

-- Type-level subset relation: A ⊆_{typ} B means there exists a surjective projection B → A
def TypeSubset (A B : Type) : Prop :=
  ∃ (p : B → A), Function.Surjective p

infix:50 " ⊆_{typ} " => TypeSubset

-- Grain definition: G is the grain of R if:
-- 1. G ⊆_{typ} R (G is a type-level subset of R)
-- 2. G ≅ R (G and R are isomorphic)
-- 3. G is irreducible (no proper subset of G can serve as grain of R)
-- For simplicity, we focus on the isomorphism requirement here
def _IsGrainOf_ (G R : Type) : Prop :=
  ∃ (f : G → R) (g : R → G),
    Function.Bijective f ∧ Function.LeftInverse g f ∧ Function.RightInverse g f

-- Alias for backward compatibility
def IsGrainOf := _IsGrainOf_

-- Infix notation: G IsGrainOf R
infix:50 " IsGrainOf " => _IsGrainOf_

-- ============================================================================
-- GRAIN EQUALITY (≡_g)
-- ============================================================================

-- According to the paper (Definition 4.1):
-- R1 ≡_g R2 if and only if there exists an isomorphism f: G[R1] → G[R2] between their grains
--
-- By the Grain Equality Theorem (Theorem 4.1):
-- R1 ≡_g R2 if and only if R1 and R2 are isomorphic sets
--
-- So we can define grain equality as isomorphism between types
def GrainEquiv (R1 R2 : Type) : Prop :=
  ∃ (f : R1 → R2) (g : R2 → R1),
    Function.Bijective f ∧ Function.LeftInverse g f ∧ Function.RightInverse g f

infix:50 " ≡_g " => GrainEquiv

-- Alias for backward compatibility with existing Pipeline files
def GrainEquivSimple (R1 R2 : Type) : Prop := GrainEquiv R1 R2

-- ============================================================================
-- GRAIN ORDERING (≤_g)
-- ============================================================================

-- According to the paper (Definition 4.2):
-- R1 ≤_g R2 if and only if there exists a function f: G[R1] → G[R2] between their grains
--
-- By the Grain Ordering Theorem (Theorem 4.2):
-- R1 ≤_g R2 if and only if there exists a function h: R1 → R2 that establishes
-- a one-to-many correspondence between the elements of the two types
--
-- So we can define grain ordering as existence of a surjective function R1 → R2
def GrainOrdering (R1 R2 : Type) : Prop :=
  ∃ (f : R1 → R2), Function.Surjective f

infix:50 " ≤_g " => GrainOrdering

-- Strict grain ordering (<_g): R1 <_g R2 means R1 ≤_g R2 but not R2 ≤_g R1
-- This means R1 is finer (more granular) than R2
def StrictGrainOrdering (R1 R2 : Type) : Prop :=
  (R1 ≤_g R2) ∧ ¬(R2 ≤_g R1)

infix:50 " <_g " => StrictGrainOrdering

-- ============================================================================
-- GRAIN INCOMPARABILITY (⟨⟩_g)
-- ============================================================================

-- According to the paper (Definition 4.3):
-- R1 ⟨⟩_g R2 if and only if:
-- - ¬(R1 ≡_g R2) (not equal)
-- - ¬(R1 ≤_g R2) (not ordered)
-- - ¬(R2 ≤_g R1) (not ordered in reverse)
def GrainIncomparable (R1 R2 : Type) : Prop :=
  ¬(R1 ≡_g R2) ∧ ¬(R1 ≤_g R2) ∧ ¬(R2 ≤_g R1)

infix:50 " ⟨⟩_g " => GrainIncomparable
