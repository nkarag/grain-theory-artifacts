module GrainTheory where

-- Only import what's NOT already in upstream files (GrainTheory.Types, GrainTheory.Ordering, GrainTheory.Operations)
-- Fields file has: Bool, Σ, ∃, _×_, _,_ , proj₁, proj₂, _≡_, refl, _≢_, cong, trans, sym,
--                  ¬_, id, _∘_, REL, Level, 0ℓ, zero, _⊔_, suc, Nat, ⊤, tt, Dec, yes, no
-- Ordering file has: Bool, true, false, _×_, _≡_, refl, Either, Dec, yes, no, ¬_
-- Types file has: Data.Product, Relation.Binary.PropositionalEquality, Relation.Nullary,
--                 Relation.Binary, Function.Base, Level (most overlap with Fields)

-- Unique imports needed here:
open import Data.Product using (∄) public  -- Only ∄ is missing from fields
open import Data.Nat hiding ( _⊔_ ; _≟_ ; _≤?_ ; suc ; zero) 
                     renaming (ℕ to Nat
                              ; _≤ᵇ_ to _n≤ᵇ_
                              ; _≡ᵇ_ to _n≡ᵇ_
                              ) public  -- Fields has Nat but not the renamed _n≤ᵇ_, _n≡ᵇ_
open import Data.Sum hiding (assocʳ ; assocˡ ; map₁ ; map₂ ; swap ; map)
                     renaming (_⊎_ to Either 
                              ; inj₁ to left 
                              ; inj₂ to right) public  -- Ordering only has Either, not left/right
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate funext : ∀ {a b} → Extensionality a b

-- Import all field definitions
open import GrainTheory.Types public

-- Import all ordering relation definitions
open import GrainTheory.Ordering public

-- Import all type definitions (union, intersection, subset relations)
open import GrainTheory.Operations public

-- Note: Type relation properties and proofs are in GrainTheory.Axioms.agda
-- Import separately when needed: open import GrainTheory.Axioms

------------------------------------------------------------------------   
-- Useful functions
------------------------------------------------------------------------   

-- Inspect pattern matching
-- Problem:
-- when we pattern match like this:
--      with e
--      ... | pattern = 
-- then Agda does not give us a value of the type e ≡ pattern
-- The solution is to use the inspect function:
--      with inspect e
--      ... | it pattern eq = 
-- This gives us  eq which is a value of the type e ≡ y, which we can use after
-- the = sign.
data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} (x : A) → Inspect x
inspect x = it x refl

-- Number of fields in a product type
record HasArity (A : Set) : Set where
  field 
    arity : Nat

open HasArity {{...}} public

instance
  hasArity× : ∀ {A B : Set} {{_ : HasArity B}} → HasArity (A × B)
  hasArity× {{hB}} .arity = 1 + HasArity.arity hB

  hasArityBase : ∀ {A : Set} → HasArity A
  hasArityBase .arity = 1


to-bool : {A : Set} → A → Bool
to-bool _ = true

to-bool1 : {A : Set₁} → A → Bool
to-bool1 _ = true

module example-proving-decidable-predicates where
    open import Relation.Nullary using (Dec ; yes ; no)

    -- predicate
    _==_ : Nat → Nat → Set
    x == y = x ≡ y

    -- Predicate is decidable
    _==-dec_ : (x : Nat) → (y : Nat) → Dec (x ≡ y)
    Nat.zero ==-dec Nat.zero = yes refl
    Nat.zero ==-dec Nat.suc y = no λ ()
    Nat.suc x ==-dec Nat.zero = no λ ()
    Nat.suc x ==-dec Nat.suc y with x ==-dec y
    ... | yes p = yes (cong Nat.suc p)
    ... | no not-p = no λ {refl → not-p refl}

    -- Convert the predicate to a boolean
    _==-bool_ : (x : Nat) → (y : Nat) → Bool
    _==-bool_  = λ x y → decToBool (x ==-dec y)

