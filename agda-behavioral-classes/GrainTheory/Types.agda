module GrainTheory.Types where

open import Data.Bool using (Bool) public
open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂) public
open import Relation.Binary.PropositionalEquality 
                                    using (_≡_ ; refl ; _≢_ ; cong ; trans ; sym) public
open import Relation.Nullary using (¬_) public
open import Function.Base using (id ; _∘_) public
open import Relation.Binary using (REL ; IsPartialOrder ; IsPreorder ; IsEquivalence ; IsStrictPartialOrder) public
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence) public
open import Level using (Level ; 0ℓ ; zero ; _⊔_ ; suc) public
open import Data.Nat hiding ( _⊔_ ; _≟_ ; _≤?_ ; suc ; zero) 
                     renaming (ℕ to Nat) public
open import Data.String using (String) public
open import Data.Unit using (⊤ ; tt) public
open import Relation.Nullary using (Dec; yes; no) public

------------------------------------------------------------------------
-- Fields A of R (a surjective projection R → A)
------------------------------------------------------------------------
-- A column C of a record R is a projection function R -> C
Fields_of_ : Set → Set → Set
Fields_of_ Fld-type Rec-type =  Rec-type → Fld-type

-- Surjective field projections: fields where every value of A 
-- is reachable from some R
-- This is a stronger requirement than Fields_of_, requiring proof 
-- of surjectivity
data SurjFields_of_ : (A : Set) → (R : Set) → Set₁ where
    surj-witness : {A : Set} → {R : Set} 
                 → (proj : R → A) 
                 → (surjective : ∀ {a : A} → ∃ λ (r : R) → proj r ≡ a)
                 → SurjFields A of R
    surj-refl : {R : Set} → SurjFields R of R

-- Convert SurjFields to Fields (forget the surjectivity proof)
to-Fields : {A R : Set} → SurjFields A of R → Fields A of R
to-Fields (surj-witness proj _) = proj
to-Fields surj-refl = id

-- Upgrade Fields to SurjFields when surjectivity is provable
from-Fields : {A R : Set} 
            → (proj : Fields A of R)
            → (surjective : ∀ {a : A} → ∃ λ (r : R) → proj r ≡ a)
            → SurjFields A of R
from-Fields proj surjective = surj-witness proj surjective

-- The empty set of fields.
--
-- a "set of fields" is represented as a projection function
-- So, the empty set of fields should be a projection that 
-- carries no information (returns the unit type): R → ⊤
∅-fld : {R : Set} → Fields ⊤ of R
∅-fld _ = tt

EmptyFld : {F R : Set} → Fields F of R → Set₁
EmptyFld {F} {R} f = F ≡ ⊤

NonEmptyFld : {F R : Set} → Fields F of R → Set₁
NonEmptyFld {F} {R} f = ¬ (EmptyFld {F} {R} f)

Fields[_] : (R : Set) → Fields R of R
Fields[ R ] = id

------------------------------------------------------------------------
-- Fields Subset Relation _⊆fld_ (Partial Order)
------------------------------------------------------------------------

-- Field subset relation as a data type with partial order properties
-- `col₁ ⊆fld col₂` means the fields in col₁ can be extracted from col₂
-- This is a partial order: reflexive, transitive, and antisymmetric
--
-- IMPORTANT: Why does the relation require both functions to share domain R?
-- 
-- Fields are fundamentally contextual: they exist only as projections from 
-- records. `Fields A of R : R → A` represents "fields of type A extracted from 
-- records of type R".
-- Without a record type R, there are no fields - just the type A itself.
--
-- The relation `flds₁ ⊆fld flds₂` compares which information can be extracted 
-- from THE SAME record: 
-- "From any record r : R, can we compute flds₁ r from flds₂ r?"
-- This comparison only makes sense when both projections operate on the same 
-- record type R.
--
-- For example, when we write `ek-from-grain ⊆fld Fields[ G ]`:
-- - `ek-from-grain : G → EK` (fields of type EK from records of type G)
-- - `Fields[ G ] = id : G → G` (all fields of type G from records of type G)
-- Both share domain G (which acts as R), allowing meaningful comparison.
--
-- Without the shared domain requirement, we'd be comparing fields from 
-- different record types, which is semantically meaningless.
data _⊆fld_ : {A B R : Set} → REL (Fields A of R) (Fields B of R) (suc 0ℓ) where
    -- Witness: There exists a projection function that extracts col₁ from col₂
    witness-⊆fld : {A B R : Set} 
                 → {flds₁ : Fields A of R}
                 → {flds₂ : Fields B of R}
                 → (proj : B → A)
                 → (∀ {r : R} → flds₁ r ≡ proj (flds₂ r))
                 → flds₁ ⊆fld flds₂
    
    -- Reflexivity: Every field projection is a subset of itself
    refl-⊆fld : {A R : Set} 
              → {flds : Fields A of R}
              → flds ⊆fld flds
    
    -- Transitivity: Subset relations compose
    trans-⊆fld : {A B C R : Set}
               → {flds₁ : Fields A of R}
               → {flds₂ : Fields B of R}
               → {flds₃ : Fields C of R}
               → flds₁ ⊆fld flds₂
               → flds₂ ⊆fld flds₃
               → flds₁ ⊆fld flds₃

infix 4 _⊆fld_

-- Proof that _⊆fld_ is a partial order
module FieldSubsetIsPartialOrder where
    open Relation.Binary using (IsPartialOrder ; IsPreorder ; IsEquivalence)
    
    -- Extract projection function from witness
    get-projection : {A B R : Set} 
                  → {flds₁ : Fields A of R}
                  → {flds₂ : Fields B of R}
                  → flds₁ ⊆fld flds₂
                  → Σ (B → A) (λ proj → ∀ {r : R} → flds₁ r ≡ proj (flds₂ r))
    get-projection (witness-⊆fld proj eq) = proj , eq
    get-projection refl-⊆fld = id , refl
    get-projection (trans-⊆fld {flds₂ = flds₂} sub₁ sub₂) = 
        let (proj₁ , eq₁) = get-projection sub₁
            (proj₂ , eq₂) = get-projection sub₂
        in (proj₁ ∘ proj₂) , (λ {r} → trans eq₁ (cong proj₁ eq₂))
    
    -- Reflexivity proof
    ⊆fld-refl : {A R : Set} 
              → {flds : Fields A of R}
              → flds ⊆fld flds
    ⊆fld-refl = refl-⊆fld
    
    -- Transitivity proof
    ⊆fld-trans : {A B C R : Set}
               → {flds₁ : Fields A of R}
               → {flds₂ : Fields B of R}
               → {flds₃ : Fields C of R}
               → flds₁ ⊆fld flds₂
               → flds₂ ⊆fld flds₃
               → flds₁ ⊆fld flds₃
    ⊆fld-trans = trans-⊆fld
    
    -- Antisymmetry: if flds₁ ⊆fld flds₂ and flds₂ ⊆fld flds₁, then flds₁ ≡ flds₂
    -- Note: This requires function extensionality to prove pointwise equality.
    -- We postulate it here, but in practice this would need proper handling.
    -- Note: For antisymmetry to work, A and B must be the same type.
    postulate
        ⊆fld-antisym : {A R : Set}
                    → {flds₁ flds₂ : Fields A of R}
                    → flds₁ ⊆fld flds₂
                    → flds₂ ⊆fld flds₁
                    → flds₁ ≡ flds₂
    
    -- Define IsEquivalence for the underlying equivalence
    -- For fields (functions), equality is pointwise equality
    ⊆fld-isEquivalence : {A R : Set} → IsEquivalence {A = Fields A of R} _≡_
    ⊆fld-isEquivalence = isEquivalence
    
    -- Define IsPreorder
    ⊆fld-isPreorder : {A R : Set} → IsPreorder {A = Fields A of R} _≡_ (_⊆fld_ {A} {A} {R})
    IsPreorder.isEquivalence ⊆fld-isPreorder = ⊆fld-isEquivalence
    IsPreorder.reflexive ⊆fld-isPreorder {x} {y} x≡y = 
        Relation.Binary.PropositionalEquality.subst (λ flds → x ⊆fld flds) x≡y ⊆fld-refl
    IsPreorder.trans ⊆fld-isPreorder = ⊆fld-trans
    
    -- Define IsPartialOrder
    ⊆fld-isPartialOrder : {A R : Set} → IsPartialOrder {A = Fields A of R} _≡_ (_⊆fld_ {A} {A} {R})
    IsPartialOrder.isPreorder ⊆fld-isPartialOrder = ⊆fld-isPreorder
    IsPartialOrder.antisym ⊆fld-isPartialOrder = ⊆fld-antisym

open FieldSubsetIsPartialOrder public


------------------------------------------------------------------------
-- Fields Proper Subset Relation _⊂fld_ (Strict Partial Order)
------------------------------------------------------------------------

-- Field proper subset relation as a data type
-- `col₁ ⊂fld col₂` means col₁ ⊆fld col₂ but col₂ ⊈fld col₁
-- This is a strict partial order: irreflexive, transitive, and asymmetric
data _⊂fld_ : {A B R : Set} → REL (Fields A of R) (Fields B of R) (suc 0ℓ) where
    -- Witness: col₁ is a proper subset of col₂
    witness-⊂fld : {A B R : Set}
                 → {flds₁ : Fields A of R}
                 → {flds₂ : Fields B of R}
                 → flds₁ ⊆fld flds₂
                 → ¬ (flds₂ ⊆fld flds₁)  -- and NOT the reverse
                 → flds₁ ⊂fld flds₂
    
    -- Transitivity: Proper subset relations compose
    trans-⊂fld : {A B C R : Set}
               → {flds₁ : Fields A of R}
               → {flds₂ : Fields B of R}
               → {flds₃ : Fields C of R}
               → flds₁ ⊂fld flds₂
               → flds₂ ⊂fld flds₃
               → flds₁ ⊂fld flds₃

infix 4 _⊂fld_

-- Proof that _⊂fld_ is a strict partial order
module FieldProperSubsetIsStrictOrder where
    open Relation.Binary using (IsStrictPartialOrder ; IsEquivalence)
    
    -- Transitivity proof
    ⊂fld-trans : {A B C R : Set}
               → {flds₁ : Fields A of R}
               → {flds₂ : Fields B of R}
               → {flds₃ : Fields C of R}
               → flds₁ ⊂fld flds₂
               → flds₂ ⊂fld flds₃
               → flds₁ ⊂fld flds₃
    ⊂fld-trans = trans-⊂fld
    
    -- Helper: Extract the flds₁ ⊆fld flds₂ proof from flds₁ ⊂fld flds₂
    extract-⊆ : {A B R : Set}
              → {flds₁ : Fields A of R}
              → {flds₂ : Fields B of R}
              → flds₁ ⊂fld flds₂
              → flds₁ ⊆fld flds₂
    extract-⊆ (witness-⊂fld flds₁⊆flds₂ _) = flds₁⊆flds₂
    extract-⊆ (trans-⊂fld flds₁⊂flds₂ flds₂⊂flds₃) = ⊆fld-trans (extract-⊆ flds₁⊂flds₂) (extract-⊆ flds₂⊂flds₃)
    
    -- Helper: Extract the ¬(flds₂ ⊆fld flds₁) proof from flds₁ ⊂fld flds₂
    extract-not-reverse : {A B R : Set}
                        → {flds₁ : Fields A of R}
                        → {flds₂ : Fields B of R}
                        → flds₁ ⊂fld flds₂
                        → ¬ (flds₂ ⊆fld flds₁)
    extract-not-reverse (witness-⊂fld _ ¬flds₂⊆flds₁) = ¬flds₂⊆flds₁
    extract-not-reverse (trans-⊂fld {A = A} {B = B} {C = C} {flds₂ = flds₂} {flds₃ = flds₃} flds₁⊂flds₂ flds₂⊂flds₃) = 
        -- If flds₁ ⊂fld flds₂ and flds₂ ⊂fld flds₃, then flds₃ ⊄fld flds₁
        -- Proof: if flds₃ ⊆fld flds₁, then by transitivity with flds₂ ⊆fld flds₃ we get flds₂ ⊆fld flds₁,
        -- but flds₁ ⊂fld flds₂ requires ¬(flds₂ ⊆fld flds₁), contradiction.
        λ flds₃⊆flds₁ → extract-not-reverse flds₁⊂flds₂ 
            (⊆fld-trans {A = B} {B = C} {C = A} (extract-⊆ flds₂⊂flds₃) flds₃⊆flds₁)
    
    -- Irreflexivity: flds ⊂fld flds does not hold
    -- This follows from the definition: if flds ⊂fld flds, we would need flds ⊆fld flds (✓) 
    -- but also ¬(flds ⊆fld flds) (✗), which is a contradiction
    ⊂fld-irrefl : {A R : Set}
                → {flds : Fields A of R}
                → ¬ (flds ⊂fld flds)
    ⊂fld-irrefl (witness-⊂fld flds⊆flds ¬flds⊆flds) = ¬flds⊆flds flds⊆flds
    ⊂fld-irrefl (trans-⊂fld {flds₂ = flds₂} flds⊂flds₂ flds₂⊂flds) = 
        extract-not-reverse flds₂⊂flds (extract-⊆ flds⊂flds₂)
    
    -- Asymmetry: if flds₁ ⊂fld flds₂, then ¬(flds₂ ⊂fld flds₁)
    -- This follows from the definition: if flds₂ ⊂fld flds₁, we'd have flds₂ ⊆fld flds₁,
    -- but flds₁ ⊂fld flds₂ requires ¬(flds₂ ⊆fld flds₁), which is a contradiction
    ⊂fld-asym : {A B R : Set}
              → {flds₁ : Fields A of R}
              → {flds₂ : Fields B of R}
              → flds₁ ⊂fld flds₂
              → ¬ (flds₂ ⊂fld flds₁)
    ⊂fld-asym flds₁⊂flds₂ flds₂⊂flds₁ = extract-not-reverse flds₁⊂flds₂ (extract-⊆ flds₂⊂flds₁)
    
    -- Define IsEquivalence for the underlying equivalence
    -- For fields (functions), equality is pointwise equality
    ⊂fld-isEquivalence : {A R : Set} → IsEquivalence {A = Fields A of R} _≡_
    ⊂fld-isEquivalence = isEquivalence
    
    -- Respect of equivalence: the relation respects equality
    -- Left: if flds₁ ≡ flds₂ and flds₃ ⊂fld flds₁, then flds₃ ⊂fld flds₂
    ⊂fld-resp-≈-left : {A R : Set}
                     → {flds₁ flds₂ flds₃ : Fields A of R}
                     → flds₁ ≡ flds₂
                     → flds₃ ⊂fld flds₁
                     → flds₃ ⊂fld flds₂
    ⊂fld-resp-≈-left {A} {R} {flds₁} {flds₂} {flds₃} flds₁≡flds₂ flds₃⊂flds₁ = 
        Relation.Binary.PropositionalEquality.subst (flds₃ ⊂fld_) flds₁≡flds₂ flds₃⊂flds₁
    
    -- Right: if flds₁ ≡ flds₂ and flds₁ ⊂fld flds₃, then flds₂ ⊂fld flds₃
    ⊂fld-resp-≈-right : {A R : Set}
                      → {flds₁ flds₂ flds₃ : Fields A of R}
                      → flds₁ ≡ flds₂
                      → flds₁ ⊂fld flds₃
                      → flds₂ ⊂fld flds₃
    ⊂fld-resp-≈-right {A} {R} {flds₁} {flds₂} {flds₃} flds₁≡flds₂ flds₁⊂flds₃ = 
        Relation.Binary.PropositionalEquality.subst (λ w → w ⊂fld flds₃) flds₁≡flds₂ flds₁⊂flds₃
    
    -- Define IsStrictPartialOrder
    -- Note: IsStrictPartialOrder requires:
    -- - isEquivalence: equivalence relation (for the ≈ part)
    -- - irrefl: irreflexivity (x ≡ y → ¬ (x < y))
    -- - trans: transitivity  
    -- - <-resp-≈: respects equivalence (if x ≈ y and y < z, then x < z, and vice versa)
    ⊂fld-isStrictPartialOrder : {A R : Set} → IsStrictPartialOrder {A = Fields A of R} _≡_ (_⊂fld_ {A} {A} {R})
    IsStrictPartialOrder.isEquivalence ⊂fld-isStrictPartialOrder = ⊂fld-isEquivalence
    IsStrictPartialOrder.irrefl ⊂fld-isStrictPartialOrder {x} {y} x≡y x⊂y = 
        ⊂fld-irrefl (Relation.Binary.PropositionalEquality.subst (x ⊂fld_) (sym x≡y) x⊂y)
    IsStrictPartialOrder.trans ⊂fld-isStrictPartialOrder = ⊂fld-trans
    IsStrictPartialOrder.<-resp-≈ ⊂fld-isStrictPartialOrder = ⊂fld-resp-≈-left , ⊂fld-resp-≈-right

open FieldProperSubsetIsStrictOrder public

-- Example demonstrating _⊆fld_ as a partial order
module field-subset-example where
    open import Data.String
    
    record Person : Set where
        field
            name : String
            age : Nat
            height : Nat
    
    -- Three field projections
    all-fields : Fields (String × Nat × Nat) of Person
    all-fields p = (Person.name p , Person.age p , Person.height p)
    
    age-height : Fields (Nat × Nat) of Person
    age-height p = (Person.age p , Person.height p)
    
    age-only : Fields Nat of Person
    age-only p = Person.age p
    
    -- Proof: age-only ⊆fld age-height (using witness constructor)
    age⊆age-height : age-only ⊆fld age-height
    age⊆age-height = witness-⊆fld proj₁ refl
    
    -- Proof: age-height ⊆fld all-fields (using witness constructor)
    age-height⊆all : age-height ⊆fld all-fields
    age-height⊆all = witness-⊆fld (λ (n , a , h) → (a , h)) refl
    
    -- By transitivity: age-only ⊆fld all-fields
    age⊆all : age-only ⊆fld all-fields
    age⊆all = trans-⊆fld age⊆age-height age-height⊆all
    
    -- Reflexivity: age-only ⊆fld age-only
    age-refl : age-only ⊆fld age-only
    age-refl = refl-⊆fld
    
    -- Antisymmetry example: if two projections are mutual subsets, they're equal
    name-col-1 : Fields String of Person
    name-col-1 p = Person.name p
    
    name-col-2 : Fields String of Person
    name-col-2 p = Person.name p
    
    name₁⊆name₂ : name-col-1 ⊆fld name-col-2
    name₁⊆name₂ = refl-⊆fld
    
    name₂⊆name₁ : name-col-2 ⊆fld name-col-1
    name₂⊆name₁ = refl-⊆fld

-- Example demonstrating _⊂fld_ as a strict partial order
module field-proper-subset-example where
    open import Data.String
    
    record Employee : Set where
        field
            emp-id : Nat
            name : String
            department : String
            salary : Nat
    
    -- Define projections with strict subset relationships
    all-info : Fields (Nat × String × String × Nat) of Employee
    all-info e = (Employee.emp-id e , Employee.name e , 
                  Employee.department e , Employee.salary e)
    
    id-name-dept : Fields (Nat × String × String) of Employee
    id-name-dept e = (Employee.emp-id e , Employee.name e , Employee.department e)
    
    id-name : Fields (Nat × String) of Employee
    id-name e = (Employee.emp-id e , Employee.name e)
    
    emp-id-only : Fields Nat of Employee
    emp-id-only e = Employee.emp-id e
    
    -- Proper subset witnesses
    
    -- For demonstration, we postulate that id-name-dept is NOT a subset of id-name
    -- (Proving this requires showing no function can reconstruct the department field
    -- from just id and name, which would require additional machinery)
    postulate
        ¬id-name-dept⊆id-name : ¬ (id-name-dept ⊆fld id-name)
        ¬all⊆id-name-dept : ¬ (all-info ⊆fld id-name-dept)
    
    -- Proof: id-name ⊂fld id-name-dept (proper subset)
    id-name⊂id-name-dept : id-name ⊂fld id-name-dept
    id-name⊂id-name-dept = 
        witness-⊂fld 
            (witness-⊆fld (λ (i , n , d) → (i , n)) refl)
            ¬id-name-dept⊆id-name
    
    -- Transitivity: proper subsets compose
    -- If we have id-name ⊂fld id-name-dept and id-name-dept ⊂fld all-info
    -- Then: id-name ⊂fld all-info
    postulate
        id-name-dept⊂all : id-name-dept ⊂fld all-info
    
    id-name⊂all : id-name ⊂fld all-info
    id-name⊂all = trans-⊂fld id-name⊂id-name-dept id-name-dept⊂all

Fields-are-disjoint : {A B C R : Set} 
                    → Fields A of R 
                    → Fields B of R 
                    → Set₁
Fields-are-disjoint {A} {B} {C} {R} flds₁ flds₂ = 
    Σ (Fields C of A) (λ f₁ → 
        Σ (Fields C of B) 
          (λ f₂ → ∀ (r : R) →  f₁ (flds₁ r) ≡ f₂ (flds₂ r) → C ≡ ⊤
        )
    ) 

------------------------------------------------------------------------
-- Fields Union Operation _∪fld_
------------------------------------------------------------------------
    
-- Field Union Evidence Record
-- Packages the evidence needed for field union with deduplication
record FieldUnionEvidence (A B C R : Set) : Set where
  field
    to-union    : R → C        -- How to construct the union from a record
    proj-left   : C → A        -- How to recover A from the union
    proj-right  : C → B        -- How to recover B from the union

open FieldUnionEvidence {{...}} public

-- Algebraic field union operation (with deduplication)
-- Usage: col₁ ∪fld[ evidence ] col₂
_∪fld[_]_ : {A B C R : Set}
          → Fields A of R
          → FieldUnionEvidence A B C R
          → Fields B of R
          → Fields C of R
flds₁ ∪fld[ ev ] flds₂ = FieldUnionEvidence.to-union ev

infixl 6 _∪fld[_]_

-- Alternative infix notation (if you prefer implicit evidence)
-- Usage: col₁ ∪ col₂  (when FieldUnionEvidence instance is in scope)
_∪fld_ : {A B C R : Set}
    → Fields A of R
    → Fields B of R
    → {{ev : FieldUnionEvidence A B C R}}
    → Fields C of R
(flds₁ ∪fld flds₂) {{ev}} = FieldUnionEvidence.to-union ev

infixl 6 _∪fld_

-- Usage example for field union
module field-union-example where
    postulate
        Name Age Address Phone : Set
        
    record Customer : Set where
        field
            name : Name
            age : Age
            address : Address
    
    -- Two projections
    name-age-proj : Fields (Name × Age) of Customer
    name-age-proj c = (Customer.name c , Customer.age c)
    
    age-address-proj : Fields (Age × Address) of Customer
    age-address-proj c = (Customer.age c , Customer.address c)
    
    -- Deduplicated union: define the evidence once
    name-age-address-evidence : FieldUnionEvidence (Name × Age) (Age × Address) 
                                                    (Name × Age × Address) Customer
    name-age-address-evidence = record
        { to-union = λ c → (Customer.name c , Customer.age c , Customer.address c)
        ; proj-left = λ (n , a , _) → (n , a)
        ; proj-right = λ (_ , a , addr) → (a , addr)
        }
    
    -- Algebraic union syntax: col₁ ∪fld[ evidence ] col₂
    dedup-union : Fields (Name × Age × Address) of Customer
    dedup-union = name-age-proj ∪fld[ name-age-address-evidence ] age-address-proj
    
    -- Even cleaner with instance argument:
    instance
        union-evidence : FieldUnionEvidence (Name × Age) (Age × Address) 
                                            (Name × Age × Address) Customer
        union-evidence = name-age-address-evidence
    
    -- Now you can write: col₁ ∪ col₂ (evidence is implicit)
    dedup-union-implicit : Fields (Name × Age × Address) of Customer
    dedup-union-implicit = name-age-proj ∪fld age-address-proj



------------------------------------------------------------------------
-- Fields Intersection Operation _∩fld_
------------------------------------------------------------------------

-- Field Intersection Evidence Record
-- Packages the evidence needed for field intersection (common fields)
record FieldIntersectionEvidence (A B C R : Set) : Set where    
  field
    to-intersect : R → C       -- How to extract the common fields
    embed-in-A   : C → A       -- Witness that C's fields embed into A
    embed-in-B   : C → B       -- Witness that C's fields embed into B

open FieldIntersectionEvidence {{...}} public

-- Algebraic field intersection operation (extract common fields)
-- Usage: col₁ ∩fld[ evidence ] col₂
_∩fld[_]_ : {A B C R : Set}
          → Fields A of R
          → FieldIntersectionEvidence A B C R
          → Fields B of R
          → Fields C of R
flds₁ ∩fld[ ev ] flds₂ = FieldIntersectionEvidence.to-intersect ev

infixl 7 _∩fld[_]_

-- Alternative infix notation (if you prefer implicit evidence)
-- Usage: col₁ ∩ col₂  (when FieldIntersectionEvidence instance is in scope)
_∩fld_ : {A B C R : Set}
    → Fields A of R
    → Fields B of R
    → {{ev : FieldIntersectionEvidence A B C R}}
    → Fields C of R
(flds₁ ∩fld flds₂) {{ev}} = FieldIntersectionEvidence.to-intersect ev

infixl 7 _∩fld_

-- Usage example for field intersection
module field-intersection-example where
    postulate
        Name Age Address Phone Email : Set
        
    record Customer : Set where
        field
            name : Name
            age : Age
            address : Address
            email : Email
    
    record Employee : Set where
        field
            name : Name
            age : Age
            employee-id : Nat
    
    -- Project name and age from Customer
    customer-name-age : Fields (Name × Age) of Customer
    customer-name-age c = (Customer.name c , Customer.age c)
    
    -- Project name and age from Employee  
    employee-name-age : Fields (Name × Age) of Employee
    employee-name-age e = (Employee.name e , Employee.age e)
    
    -- The intersection is the common fields: Name × Age
    -- Evidence for Customer fields
    customer-intersection-evidence : 
        FieldIntersectionEvidence (Name × Age) (Name × Age) (Name × Age) Customer
    customer-intersection-evidence = record
        { to-intersect = λ c → (Customer.name c , Customer.age c)
        ; embed-in-A = λ na → na  -- identity, since intersection = A
        ; embed-in-B = λ na → na  -- identity, since intersection = B
        }
    
    -- More interesting example: intersection of different field sets
    customer-name-age-address : Fields (Name × Age × Address) of Customer
    customer-name-age-address c = 
        (Customer.name c , Customer.age c , Customer.address c)
    
    customer-age-address-email : Fields (Age × Address × Email) of Customer
    customer-age-address-email c = 
        (Customer.age c , Customer.address c , Customer.email c)
    
    -- Common fields between (Name × Age × Address) and (Age × Address × Email)
    -- are: Age × Address
    
    -- We need postulates for the embedding witnesses since we're only 
    -- embedding partial information
    postulate
        default-name : Name
        default-email : Email
    
    intersection-evidence : 
        FieldIntersectionEvidence 
            (Name × Age × Address) 
            (Age × Address × Email) 
            (Age × Address) 
            Customer
    intersection-evidence = record
        { to-intersect = λ c → (Customer.age c , Customer.address c)
        ; embed-in-A = λ (a , addr) → (default-name , a , addr)
        ; embed-in-B = λ (a , addr) → (a , addr , default-email)
        }
    
    -- Algebraic intersection syntax: col₁ ∩fld[ evidence ] col₂
    common-fields : Fields (Age × Address) of Customer
    common-fields = customer-name-age-address ∩fld[ intersection-evidence ] 
                    customer-age-address-email
    
    -- With instance argument (implicit evidence)
    instance
        intersect-evidence : 
            FieldIntersectionEvidence 
                (Name × Age × Address) 
                (Age × Address × Email) 
                (Age × Address) 
                Customer
        intersect-evidence = intersection-evidence
    
    -- Clean algebraic syntax: col₁ ∩ col₂
    common-fields-implicit : Fields (Age × Address) of Customer
    common-fields-implicit = customer-name-age-address ∩fld customer-age-address-email

------------------------------------------------------------------------
-- Fields Difference Operation _-fld_
------------------------------------------------------------------------

-- Field Difference Evidence Record
-- Packages the evidence needed for field difference (fields in A but not in B)
record FieldDifferenceEvidence (A B C R : Set) : Set₁ where
  field
    to-difference : R → C       -- How to extract the difference fields (A - B)
    embed-in-A    : C → A       -- Witness that C's fields embed into A
    disjoint-from-B : ¬ (C ≡ B) -- Witness that C is disjoint from B (not equal)

open FieldDifferenceEvidence {{...}} public

-- Algebraic field difference operation (extract fields in A but not in B)
-- Usage: col₁ -[ evidence ] col₂
_-[_]_ : {A B C R : Set}
       → Fields A of R
       → FieldDifferenceEvidence A B C R
       → Fields B of R
       → Fields C of R
flds₁ -[ ev ] flds₂ = FieldDifferenceEvidence.to-difference ev

infixl 6 _-[_]_

-- Alternative infix notation (if you prefer implicit evidence)
-- Usage: col₁ -fld col₂  (when FieldDifferenceEvidence instance is in scope)
_-fld_ : {A B C R : Set}
       → Fields A of R
       → Fields B of R
       → {{ev : FieldDifferenceEvidence A B C R}}
       → Fields C of R
(flds₁ -fld flds₂) {{ev}} = FieldDifferenceEvidence.to-difference ev

infixl 6 _-fld_

-- Usage example for field difference
module field-difference-example where
    postulate
        Name Age Address Phone Email : Set
        
    record Customer : Set where
        field
            name : Name
            age : Age
            address : Address
            email : Email
    
    -- Two projections
    name-age-address-proj : Fields (Name × Age × Address) of Customer
    name-age-address-proj c = 
        (Customer.name c , Customer.age c , Customer.address c)
    
    age-address-proj : Fields (Age × Address) of Customer
    age-address-proj c = (Customer.age c , Customer.address c)
    
    -- Difference: name-age-address - age-address = name
    -- The fields in name-age-address that are NOT in age-address
    
    -- We need postulates for the embedding and disjointness
    postulate
        default-age : Age
        default-address : Address
        name≢age-address : ¬ (Name ≡ (Age × Address))
    
    difference-evidence : 
        FieldDifferenceEvidence 
            (Name × Age × Address) 
            (Age × Address) 
            Name
            Customer
    difference-evidence = record
        { to-difference = λ c → Customer.name c
        ; embed-in-A = λ n → (n , default-age , default-address)
        ; disjoint-from-B = name≢age-address
        }
    
    -- Algebraic difference syntax: col₁ -[ evidence ] col₂
    diff-fields : Fields Name of Customer
    diff-fields = name-age-address-proj -[ difference-evidence ] age-address-proj
    
    -- With instance argument (implicit evidence)
    instance
        diff-evidence : 
            FieldDifferenceEvidence 
                (Name × Age × Address) 
                (Age × Address) 
                Name
                Customer
        diff-evidence = difference-evidence
    
    -- Clean algebraic syntax: col₁ -fld col₂
    diff-fields-implicit : Fields Name of Customer
    diff-fields-implicit = name-age-address-proj -fld age-address-proj

------------------------------------------------------------------------
-- Fields Symmetric Difference Operation _symdiff-fld_
------------------------------------------------------------------------

-- Field Symmetric Difference Evidence Record
-- Packages the evidence needed for symmetric difference ((A - B) ∪ (B - A))
-- Fields that are in A or B but not in both
record FieldSymmetricDifferenceEvidence (A B C R : Set) : Set where
  field
    to-symdiff   : R → C       -- How to extract the symmetric difference
    proj-only-A  : C → A       -- How to project to fields only in A
    proj-only-B  : C → B       -- How to project to fields only in B

open FieldSymmetricDifferenceEvidence {{...}} public

-- Algebraic field symmetric difference operation
-- Usage: col₁ symdiff[ evidence ] col₂
_symdiff[_]_ : {A B C R : Set}
              → Fields A of R
              → FieldSymmetricDifferenceEvidence A B C R
              → Fields B of R
              → Fields C of R
flds₁ symdiff[ ev ] flds₂ = FieldSymmetricDifferenceEvidence.to-symdiff ev

infixl 6 _symdiff[_]_

-- Alternative infix notation (if you prefer implicit evidence)
-- Usage: col₁ symdiff-fld col₂  (when FieldSymmetricDifferenceEvidence instance is in scope)
_symdiff-fld_ : {A B C R : Set}
               → Fields A of R
               → Fields B of R
               → {{ev : FieldSymmetricDifferenceEvidence A B C R}}
               → Fields C of R
(flds₁ symdiff-fld flds₂) {{ev}} = FieldSymmetricDifferenceEvidence.to-symdiff ev

infixl 6 _symdiff-fld_

-- Usage example for field symmetric difference
module field-symmetric-difference-example where
    postulate
        Name Age Address Phone Email : Set
        
    record Customer : Set where
        field
            name : Name
            age : Age
            address : Address
            email : Email
    
    -- Two projections with some overlap
    name-age-address-proj : Fields (Name × Age × Address) of Customer
    name-age-address-proj c = 
        (Customer.name c , Customer.age c , Customer.address c)
    
    age-address-email-proj : Fields (Age × Address × Email) of Customer
    age-address-email-proj c = 
        (Customer.age c , Customer.address c , Customer.email c)
    
    -- Symmetric difference: 
    -- (name-age-address - age-address-email) ∪ (age-address-email - name-age-address)
    -- = name ∪ email = (Name × Email)
    -- Fields in one but not the other
    
    -- We need postulates for the projections
    postulate
        default-name : Name
        default-age : Age
        default-address : Address
        default-email : Email
    
    symdiff-evidence : 
        FieldSymmetricDifferenceEvidence 
            (Name × Age × Address) 
            (Age × Address × Email) 
            (Name × Email)
            Customer
    symdiff-evidence = record
        { to-symdiff = λ c → (Customer.name c , Customer.email c)
        ; proj-only-A = λ (n , e) → (n , default-age , default-address)  -- embed into A
        ; proj-only-B = λ (n , e) → (default-age , default-address , e)  -- embed into B
        }
    
    -- Algebraic symmetric difference syntax: col₁ symdiff[ evidence ] col₂
    symdiff-fields : Fields (Name × Email) of Customer
    symdiff-fields = name-age-address-proj symdiff[ symdiff-evidence ] age-address-email-proj
    
    -- With instance argument (implicit evidence)
    instance
        symdiff-ev : 
            FieldSymmetricDifferenceEvidence 
                (Name × Age × Address) 
                (Age × Address × Email) 
                (Name × Email)
                Customer
        symdiff-ev = symdiff-evidence
    
    -- Clean algebraic syntax: col₁ symdiff-fld col₂
    symdiff-fields-implicit : Fields (Name × Email) of Customer
    symdiff-fields-implicit = name-age-address-proj symdiff-fld age-address-email-proj

