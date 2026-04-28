module GrainTheory.Ordering where

open import Data.Bool using (Bool ; true ; false) public
open import Data.Product using (_×_) public
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl) public
open import Data.Sum hiding (assocʳ ; assocˡ ; map₁ ; map₂ ; swap ; map)
                     renaming (_⊎_ to Either) public
open import Relation.Nullary using (Dec ; yes ; no ; ¬_) public

-- Convert a decidable predicate to a boolean
decToBool : {A : Set} → Dec A → Bool
decToBool (yes _) = true
decToBool (no _) = false

------------------------------------------------------------------------   
-- Ordering relations
------------------------------------------------------------------------   
-- A typeclass to model the notion of "preorder" 
record PreOrd   {A : Set} (_<pr=_ : A → A → Set) 
                : Set where
    field
        <pr=-refl    : {x : A} → x <pr= x
        <pr=-trans   : {x y z : A} → x <pr= y → y <pr= z → x <pr= z
        zero-element-pr : A 
        suc-element-pr : A → A

    _>pr=_ : A → A → Set 
    x >pr= y = y <pr= x

    _<pr_ : A → A → Set 
    a₁ <pr a₂ = (suc-element-pr a₁) <pr= a₂

    _>pr_ : A → A → Set 
    a₁ >pr a₂ = a₂ <pr a₁ 

open PreOrd {{...}} public


-- A typeclass to model the notion of "partial order" 
record PartialOrd   {A : Set} (_<pa=_ : A → A → Set) 
                : Set where
    field
        <pa=-refl    : {x : A} → x <pa= x
        <pa=-trans   : {x y z : A} → x <pa= y → y <pa= z → x <pa= z
        <pa=-antisym : {x y : A} →  x <pa= y → y <pa= x → x ≡ y
        zero-element-pa : A 
        suc-element-pa : A → A

        -- Decidable version of the order
        <pa=-dec : (x y : A) → Dec (x <pa= y)

    -- Boolean version of the order
    <pa=-bool : (x y : A) → Bool
    <pa=-bool x y = decToBool (<pa=-dec x y)

    _>pa=_ : A → A → Set 
    x >pa= y = y <pa= x

    _<pa_ : A → A → Set 
    a₁ <pa a₂ = (suc-element-pa a₁) <pa= a₂

    _>pa_ : A → A → Set 
    a₁ >pa a₂ = a₂ <pa a₁ 

    _<pa=ᵇ_ : A → A → Bool
    x <pa=ᵇ y = <pa=-bool x y

    _>pa=ᵇ_ : A → A → Bool
    x >pa=ᵇ y = <pa=-bool y x

open PartialOrd {{...}} public


-- A typeclass to model the notion of "total order"
record TotalOrd   {A : Set} (_<to=_ : A → A → Set) 
                : Set where
    field
        <to=-refl    : {x : A} → x <to= x
        <to=-trans   : {x y z : A} → x <to= y → y <to= z → x <to= z
        <to=-antisym : {x y : A} →  x <to= y → y <to= x → x ≡ y
        <to=-compar  : {x y : A} → Either (x <to= y) (y <to= x)
        zero-element-to : A 
        suc-element-to : A → A

        -- Standard library practice is to provide both propositional and 
        -- boolean relations, with a decidable version (returns Dec) and 
        -- a boolean version (returns Bool). Here we add a Decidable and 
        -- Bool version for the order.

        -- We declare <to=-dec as a field, but do not implement it here.
        -- This is because TotalOrd is a record (typeclass), and the
        -- implementation of <to=-dec must be provided for each concrete
        -- instance of TotalOrd. For example, for Nat, we can use the
        -- standard library's decidable order.
        <to=-dec : (x y : A) → Dec (x <to= y)

    <to=-bool : (x y : A) → Bool
    <to=-bool x y = decToBool (<to=-dec x y)

    _>to=_ : A → A → Set 
    x >to= y = y <to= x

    _<to_ : A → A → Set 
    a₁ <to a₂ = (suc-element-to a₁) <to= a₂

    _>to_ : A → A → Set 
    a₁ >to a₂ = a₂ <to a₁ 

    _<to=ᵇ_ : A → A → Bool
    x <to=ᵇ y = <to=-bool x y

    _>to=ᵇ_ : A → A → Bool
    x >to=ᵇ y = <to=-bool y x

open TotalOrd {{...}} public

record StrictTotalOrd {A : Set} (_<st_ : A → A → Set) : Set where
  field
    <st-irreflexive : {x : A} → ¬ (x <st x)
    <st-trans       : {x y z : A} → x <st y → y <st z → x <st z
    <st-trichotomy  : {x y : A} → Either (x <st y) (Either (x ≡ y) (y <st x))
    zero-element-st : A
    suc-element-st  : A → A

    -- Decidable and boolean versions of the strict order
    <st-dec : (x y : A) → Dec (x <st y)

  <st-bool : (x y : A) → Bool
  <st-bool x y = decToBool (<st-dec x y)

  _<stᵇ_ : A → A → Bool
  x <stᵇ y = <st-bool x y

  _>st_ : A → A → Set
  x >st y = y <st x

  _>stᵇ_ : A → A → Bool
  x >stᵇ y = <st-bool y x

open StrictTotalOrd {{...}} public

