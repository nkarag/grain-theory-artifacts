module GrainTheory.Operations where

open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂) public
open import Relation.Binary.PropositionalEquality 
                                    using (_≡_ ; refl ; _≢_ ; cong ; trans ; sym) public
open import Relation.Nullary using (¬_) public
open import Relation.Binary using (REL ; IsPartialOrder ; IsPreorder ; IsEquivalence ; IsStrictPartialOrder) public
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence) public
open import Function.Base using (id ; _∘_) public
open import Level using (Level ; 0ℓ ; zero ; _⊔_ ; suc) public

------------------------------------------------------------
-- Types Subset relation
------------------------------------------------------------

-- Type subset relation as a data type with partial order properties
-- `A ⊆typ B` means there exists a surjective function from B to A
-- This expresses that every element of A can be obtained from some element of B
-- This is a partial order: reflexive, transitive, and antisymmetric
data _⊆typ_ : (A B : Set) → Set (suc (suc 0ℓ)) where
    -- Witness: There exists a surjective projection function from B to A
    witness-⊆typ : {A B : Set}
                 → (proj : B → A)
                 → (surjective : ∀ (a : A) → ∃ λ b → proj b ≡ a)
                 → A ⊆typ B
    
    -- Reflexivity: Every type is a subset of itself
    refl-⊆typ : {A : Set} → A ⊆typ A
    
    -- Transitivity: Subset relations compose
    trans-⊆typ : {A B C : Set}
               → A ⊆typ B
               → B ⊆typ C
               → A ⊆typ C

infix 4 _⊆typ_

-- Extract projection function from witness
-- This is a utility function for working with _⊆typ_ relations
get-projection-typ : {A B : Set}
              → A ⊆typ B
              → Σ (B → A) (λ proj → ∀ (a : A) → Σ B (λ b → proj b ≡ a))
get-projection-typ (witness-⊆typ proj surj) = proj , surj
get-projection-typ refl-⊆typ = id , (λ a → a , refl)
get-projection-typ (trans-⊆typ {B = B} sub₁ sub₂) = 
    let (proj₁ , surj₁) = get-projection-typ sub₁
        (proj₂ , surj₂) = get-projection-typ sub₂
    in (proj₁ ∘ proj₂) , (λ a → 
        let (b , eq₁) = surj₁ a
            (c , eq₂) = surj₂ b
        in c , trans (cong proj₁ eq₂) eq₁)

-- Proofs for _⊆typ_ are in GrainTheory.Axioms.agda
-- Import separately: open import GrainTheory.Axioms

------------------------------------------------------------
-- Types Proper Subset relation
------------------------------------------------------------

-- Type proper subset relation as a data type
-- `A ⊂typ B` means A ⊆typ B but B ⊈typ A
-- This is a strict partial order: irreflexive, transitive, and asymmetric
data _⊂typ_ : (A B : Set) → Set (suc (suc 0ℓ)) where
    -- Witness: A is a proper subset of B
    witness-⊂typ : {A B : Set}
                 → A ⊆typ B
                 → ¬ (B ⊆typ A)  -- and NOT the reverse
                 → A ⊂typ B
    
    -- Transitivity: Proper subset relations compose
    trans-⊂typ : {A B C : Set}
               → A ⊂typ B
               → B ⊂typ C
               → A ⊂typ C

infix 4 _⊂typ_

-- Proofs for _⊂typ_ are in GrainTheory.Axioms.agda
-- Import separately: open import GrainTheory.Axioms

------------------------------------------------------------
-- Types Union Operation _∪typ[_]_
------------------------------------------------------------

-- Type union operator (with deduplication and flattening)
-- Usage: A ∪typ[ ResultType ] B
-- Where ResultType is the union type (with duplicates eliminated and flattened)
-- Example: (D × E × F) ∪[ D × E × F × G ] (D × E × G) = D × E × F × G
-- 
-- This operator returns the ResultType you specify, enabling unions with:
-- - Duplicate elimination (common types appear only once)
-- - Flattening (all components in a single product)
_∪[_]_ : (A : Set) → (ResultType : Set) → (B : Set) → Set
_∪[_]_ _ ResultType _ = ResultType

infixl 6 _∪[_]_

record FieldUnionGuide (A B C : Set) : Set where
  field
    to-union    : A × B → C        -- How to construct the union from a record
    proj-left   : C → A        -- How to recover A from the union
    proj-right  : C → B        -- How to recover B from the union

open FieldUnionGuide {{...}} public

_∪typ_ :  (A : Set)
        → (B : Set)
        → {C : Set}
        → {{ev : FieldUnionGuide A B C}}
        → Set
_∪typ_ A B {C} {{ev}} = C

infixl 6 _∪typ_


_∪typ[_]_ : (A : Set)
          → {B C : Set}
          → (ev : FieldUnionGuide A B C)
          → B
          → Set
_∪typ[_]_ A {C} ev B  = C

infixl 6 _∪typ[_]_

module type-union-example where
    postulate
        A B C : Set
        ev : FieldUnionGuide A B C

    instance
        ev-instance : FieldUnionGuide A B C
        ev-instance = ev

    myType : Set
    myType = A ∪typ B 


-- Example with Customer and Order records sharing CustomerId and CustomerName
module customer-order-union-example where
    postulate
        CustomerId OrderId Name Email Amount Quantity Status : Set
        default-email : Email
        default-amount : Amount
        default-quantity : Quantity
        default-status : Status
        default-order-id : OrderId
    
    -- Customer record type with CustomerId, CustomerName, and Email
    record Customer : Set where
        field
            customer-id : CustomerId
            customer-name : Name
            email : Email
    
    -- Order record type with OrderId, CustomerId, CustomerName, and order-specific fields
    -- Note: Order also has CustomerId and CustomerName (shared with Customer)
    record Order : Set where
        field
            order-id : OrderId
            order-customer-id : CustomerId      -- Shared with Customer
            order-customer-name : Name           -- Shared with Customer
            amount : Amount
            quantity : Quantity
            status : Status

    record CustomerOrder : Set where
        field
            customer-id : CustomerId
            customer-name : Name
            email : Email
            order-id : OrderId
            amount : Amount
            quantity : Quantity
            status : Status

    -- Example: Union of Customer and Order types
    -- CustomerOrder is the union type that combines Customer and Order,
    -- deduplicating shared fields (CustomerId and CustomerName)
    
    -- Using explicit ResultType
    myType : Set
    myType = Customer ∪[ CustomerOrder ] Order

    -- Construct the union guide evidence
    ev-customer-order : FieldUnionGuide Customer Order CustomerOrder
    ev-customer-order = record
        { to-union = λ (c , o) → record
            { customer-id = Customer.customer-id c
            ; customer-name = Customer.customer-name c
            ; email = Customer.email c
            ; order-id = Order.order-id o
            ; amount = Order.amount o
            ; quantity = Order.quantity o
            ; status = Order.status o
            }
        ; proj-left = λ co → record
            { customer-id = CustomerOrder.customer-id co
            ; customer-name = CustomerOrder.customer-name co
            ; email = CustomerOrder.email co
            }
        ; proj-right = λ co → record
            { order-id = CustomerOrder.order-id co
            ; order-customer-id = CustomerOrder.customer-id co
            ; order-customer-name = CustomerOrder.customer-name co
            ; amount = CustomerOrder.amount co
            ; quantity = CustomerOrder.quantity co
            ; status = CustomerOrder.status co
            }
        }

    instance
        ev-customer-order-instance : FieldUnionGuide Customer Order CustomerOrder
        ev-customer-order-instance = ev-customer-order

    -- Using implicit instance (FieldUnionGuide)
    myType' : Set
    myType' = Customer ∪typ Order


    join-op : Customer → Order → Customer ∪typ Order
    join-op c o = to-union (c , o)

    -- Example: Union of product types with duplicate elimination
    -- (D × E × F) ∪typ[ D × E × F × G ] (D × E × G) = D × E × F × G
    -- The union type D × E × F × G:
    -- - Deduplicates D and E (they appear in both input types)
    -- - Flattens all components into a single product
    -- - Includes F from left, G from right
    module product-union-with-dedup where
        postulate
            D E F G : Set
        
        -- Using explicit ResultType
        ProductUnionType : Set
        ProductUnionType = (D × E × F) ∪[ D × E × F × G ] (D × E × G)
        -- Result: D × E × F × G

        -- Construct the union guide evidence
        ev-product-union : FieldUnionGuide (D × E × F) (D × E × G) (D × E × F × G)
        ev-product-union = record
            { to-union = λ ((d , e , f) , (d' , e' , g)) → (d , e , f , g)
            -- We use d and e from the left side (they're the same in both)
            ; proj-left = λ (d , e , f , g) → (d , e , f)
            ; proj-right = λ (d , e , f , g) → (d , e , g)
            }
        
        instance
            ev-product-union-instance : FieldUnionGuide (D × E × F) (D × E × G) (D × E × F × G)
            ev-product-union-instance = ev-product-union

        -- Using implicit instance (FieldUnionGuide)
        ProductUnionType' : Set
        ProductUnionType' = (D × E × F) ∪typ (D × E × G)

------------------------------------------------------------
-- Types Intersection Operation _∩typ[_]_
------------------------------------------------------------

-- Type intersection operator (extract common types)
-- Usage: A ∩typ[ ResultType ] B
-- Where ResultType is the intersection type (common types)
-- Example: (D × E × F) ∩[ D × E ] (D × E × G) = D × E
-- 
-- This operator returns the ResultType you specify, enabling intersections with:
-- - Common type extraction (types that appear in both)
-- - Flattening (all common components in a single product)
_∩[_]_ : (A : Set) → (ResultType : Set) → (B : Set) → Set
_∩[_]_ _ ResultType _ = ResultType

infixl 7 _∩[_]_

record FieldIntersectionGuide (A B C : Set) : Set where
  field
    proj-from-A   : A → C        -- How to extract the intersection from A
    proj-from-B   : B → C        -- How to extract the intersection from B
    embed-in-A    : C → A        -- Witness that C embeds into A
    embed-in-B    : C → B        -- Witness that C embeds into B

open FieldIntersectionGuide {{...}} public

_∩typ_ :  (A : Set)
        → (B : Set)
        → {C : Set}
        → {{ev : FieldIntersectionGuide A B C}}
        → Set
_∩typ_ A B {C} {{ev}} = C

infixl 7 _∩typ_

_∩typ[_]_ : (A : Set)
          → {B C : Set}
          → (ev : FieldIntersectionGuide A B C)
          → B
          → Set
_∩typ[_]_ A {C} ev B  = C

infixl 7 _∩typ[_]_

-- Example with Customer and Order records sharing CustomerId and CustomerName
module customer-order-intersection-example where
    postulate
        CustomerId OrderId Name Email Amount Quantity Status : Set
    
    -- Customer record type with CustomerId, CustomerName, and Email
    record Customer : Set where
        field
            customer-id : CustomerId
            customer-name : Name
            email : Email
    
    -- Order record type with OrderId, CustomerId, CustomerName, and order-specific fields
    -- Note: Order also has CustomerId and CustomerName (shared with Customer)
    record Order : Set where
        field
            order-id : OrderId
            order-customer-id : CustomerId      -- Shared with Customer
            order-customer-name : Name           -- Shared with Customer
            amount : Amount
            quantity : Quantity
            status : Status
    
    -- Intersection type: CustomerId × Name
    -- This is the intersection of Customer and Order
    -- Customer gives us: CustomerId × Name × Email
    -- Order gives us: OrderId × CustomerId × Name × Amount × Quantity × Status
    -- Intersection (common): CustomerId × Name
    
    postulate
        default-email : Email
        default-amount : Amount
        default-quantity : Quantity
        default-status : Status
        default-order-id : OrderId
    
    -- Example: Intersection of Customer and Order types
    -- The intersection type CustomerId × Name represents the common fields
    
    -- Using explicit ResultType
    myIntersectionType : Set
    myIntersectionType = Customer ∩[ CustomerId × Name ] Order
    
    -- Construct the intersection guide evidence
    ev-customer-order-intersection : FieldIntersectionGuide Customer Order (CustomerId × Name)
    ev-customer-order-intersection = record
        { proj-from-A = λ c → (Customer.customer-id c , Customer.customer-name c)
        ; proj-from-B = λ o → (Order.order-customer-id o , Order.order-customer-name o)
        ; embed-in-A = λ (cid , n) → record
            { customer-id = cid
            ; customer-name = n
            ; email = default-email
            }
        ; embed-in-B = λ (cid , n) → record
            { order-id = default-order-id
            ; order-customer-id = cid
            ; order-customer-name = n
            ; amount = default-amount
            ; quantity = default-quantity
            ; status = default-status
            }
        }
    
    instance
        ev-customer-order-intersection-instance : 
            FieldIntersectionGuide Customer Order (CustomerId × Name)
        ev-customer-order-intersection-instance = ev-customer-order-intersection
    
    -- Using implicit instance (FieldIntersectionGuide)
    myIntersectionType' : Set
    myIntersectionType' = Customer ∩typ Order
    
    -- Example: Intersection of product types (extract common types)
    -- (D × E × F) ∩typ[ D × E ] (D × E × G) = D × E
    -- The intersection type D × E:
    -- - Extracts D and E (they appear in both input types)
    -- - Common components in a single product
    module product-intersection-example where
        postulate
            D E F G : Set
            default-f : F
            default-g : G
        
        -- Using explicit ResultType
        ProductIntersectionType : Set
        ProductIntersectionType = (D × E × F) ∩[ D × E ] (D × E × G)
        -- Result: D × E
        
        -- Construct the intersection guide evidence
        ev-product-intersection : FieldIntersectionGuide (D × E × F) (D × E × G) (D × E)
        ev-product-intersection = record
            { proj-from-A = λ (d , e , f) → (d , e)
            ; proj-from-B = λ (d , e , g) → (d , e)
            ; embed-in-A = λ (d , e) → (d , e , default-f)
            ; embed-in-B = λ (d , e) → (d , e , default-g)
            }
        
        instance
            ev-product-intersection-instance : FieldIntersectionGuide (D × E × F) (D × E × G) (D × E)
            ev-product-intersection-instance = ev-product-intersection
        
        -- Using implicit instance (FieldIntersectionGuide)
        ProductIntersectionType' : Set
        ProductIntersectionType' = (D × E × F) ∩typ (D × E × G)
        -- Result: D × E

------------------------------------------------------------
-- Types Difference Operation _-typ[_]_
------------------------------------------------------------

-- Type difference: fields in A but not in B
-- Uses TypeDifferenceGuide (analogous to FieldUnionGuide/FieldIntersectionGuide)
-- Implicit operator: A -typ B (instance resolved)
-- Explicit operator: A -typ[ guide ] B

record TypeDifferenceGuide (A B C : Set) : Set where
  field
    to-difference : A → C        -- Project out fields not in B
    embed-in-A    : C → A        -- Witness that C ⊆typ A (difference is a subset of A)

open TypeDifferenceGuide {{...}} public

_-typ_ :  (A : Set)
        → (B : Set)
        → {C : Set}
        → {{ev : TypeDifferenceGuide A B C}}
        → Set
_-typ_ A B {C} {{ev}} = C

infixl 6 _-typ_

_-typ[_]_ : (A : Set)
          → {B C : Set}
          → (ev : TypeDifferenceGuide A B C)
          → B
          → Set
_-typ[_]_ A {C} ev B = C

infixl 6 _-typ[_]_

-- Example: Difference of product types (fields in A not in B)
-- (D × E × F) -typ[ F ] (D × E × G) = F
-- The difference type F:
-- - D and E are shared, so they are removed
-- - F is unique to A, G is unique to B (ignored)
-- - Only F remains
module product-difference-example where
    postulate
        D E F G : Set
        default-d : D
        default-e : E

    -- Construct the difference guide evidence
    ev-product-difference : TypeDifferenceGuide (D × E × F) (D × E × G) F
    ev-product-difference = record
        { to-difference = λ (d , e , f) → f
        ; embed-in-A = λ f → (default-d , default-e , f)
        }

    instance
        ev-product-difference-instance : TypeDifferenceGuide (D × E × F) (D × E × G) F
        ev-product-difference-instance = ev-product-difference

    -- Using implicit instance (TypeDifferenceGuide)
    ProductDifferenceType : Set
    ProductDifferenceType = (D × E × F) -typ (D × E × G)
    -- Result: F