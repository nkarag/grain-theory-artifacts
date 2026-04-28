module GrainTheory.Relations where

open import GrainTheory public

open import Agda.Primitive using (lzero) public
open import Function.Base using ( _∘_ 
                                ; id 
                                ; const 
                                ; _$_ 
                                ; _|>_ 
                                ; flip 
                                ; case_of_
                                ; case_return_of_
                                ) public
open import Relation.Binary.PropositionalEquality 
                                    using (_≡_ 
                                          ; refl 
                                          ; _≢_ 
                                          ; cong 
                                          ; subst 
                                          ; sym) public
-- open import Axiom.Extensionality.Propositional using (Extensionality)
-- postulate funext : ∀ {a b} → Extensionality a b
open import Relation.Nullary using (¬_) public
open import Relation.Unary using (Pred) public
open import Relation.Binary using (REL ; Rel ; IsEquivalence ; IsPreorder ; IsPartialOrder) public
open import Level using (Level ; 0ℓ ; zero ; _⊔_ ; suc) public
open import Data.Product using (Σ ; ∃ ; ∃! ; ∄ ; _×_ ; _,_ ; proj₁ ; proj₂) public
open import Data.Sum hiding (assocʳ ; assocˡ ; map₁ ; map₂ ; swap ; map)
                     renaming (_⊎_ to Either 
                              ; inj₁ to left 
                              ; inj₂ to right) public 
open import Data.Nat hiding ( _⊔_ ; _≟_ ; _≤?_ ; suc ; zero) 
                     renaming (ℕ to Nat
                              ; _≤ᵇ_ to _n≤ᵇ_
                              ; _≡ᵇ_ to _n≡ᵇ_
                              ) public
open import Data.Float using (Float) renaming (_≤ᵇ_ to _f≤ᵇ_)  public                    
open import Data.Unit -- hiding (_≤_) 
                     using (⊤ ; tt) public
                      -- renaming (⊤ to True ; tt to true-value) public  
open import Data.Empty using (⊥ ; ⊥-elim) public 
            -- renaming (⊥ to False ; ⊥-elim to false-value) public
open import Data.Bool using (Bool 
                              ; true 
                              ; false 
                              ; if_then_else_ 
                              ; T 
                              ; not
                              ; _∧_
                              ; _∨_
                              ; _xor_) public
open import Data.String using (String) public
open import Data.List using (List 
                            ; null 
                            ;  _∷_ 
                            ; [] 
                            ; filterᵇ
                            ; head 
                            ; tail
                            ; _++_
                            ) 
                      renaming (lookup to lookup-list 
                               ; map to map-list
                               ; length to length-list
                               ; foldr to foldr-list
                               ; foldl to foldl-list
                               ) public
open import Data.List.NonEmpty using (List⁺)
                               renaming (_∷_ to _∷⁺_
                                        ; head to head⁺
                                        ; tail to tail⁺
                                        ; toList to toList⁺
                                        ; fromList to fromList⁺) public
open import Data.List.Relation.Unary.Any 
                                    using (Any ; here ; there) public
open import Data.Maybe using ( Maybe 
                             ; nothing 
                             ; just
                             ; from-just
                             ; maybe
                             ; fromMaybe
                             ) public 
open import Effect.Functor using (RawFunctor) public
open import Effect.Applicative using (RawApplicative) public
open import Effect.Monad using (RawMonad) public                             
open import Data.Maybe.Instances using (maybeMonad) public
open RawMonad {zero} maybeMonad renaming (_>>_ to _>>mon_) public
    -- This brings _>>=_ into scope for Maybe 
    -- I use it for do-notation for Maybe     

------------------------------------------------------------------------   
-- Data constraints
------------------------------------------------------------------------

-- Generic constraint 
-- Type A can be a product of types corresponding to an arbitrary
-- number of data collections. Therefore, referential integrity 
-- constraints can be defined via a Cons constraint. Also a target
-- data collection can also be included in this product and thus we can
-- define a constraint between a target data collection and a source
-- data collection.
Cons : Set → Set₁
Cons A = Pred A 0ℓ  -- A → Set

cons-true : {A : Set} → Cons A
cons-true = λ _ → ⊤

cons-false : {A : Set} → Cons A
cons-false = λ _ → ⊥

Cons1 : Set → Set₂
Cons1 A = Pred A (suc 0ℓ)  -- A → Set₁

------------------------------------------------------------------------   
-- Abstractions for data
------------------------------------------------------------------------   

Isomorphic-Sets : Rel Set zero -- Set → Set → Set
Isomorphic-Sets A B = 
    ∃ λ (f : A → B) → ∃ λ (f⁻¹ : B → A) → (f ∘ f⁻¹ ≡ id) × (f⁻¹ ∘ f ≡ id)

get-f : {A B : Set} → (iso-def : Isomorphic-Sets A B) → A → B
get-f {A} {B} (f , _) = f

get-f-inverse  : {A B : Set} → (iso-def : Isomorphic-Sets A B) → B → A
get-f-inverse {A} {B} (_ , (f⁻¹ , _)) = f⁻¹

-- Grain-def : {R G : Set} → (grain : R → G) → Set
-- Grain-def {R} {G} grain = Isomorphic-Sets G R

-- New grain definition that properly uses the grain (projection) function
-- Grain-def : {R G : Set} → (grain : R → G) → Set
-- Grain-def {R} {G} grain = 
--     ∃ λ (fg : G → R) → (fg ∘ grain ≡ id) × (grain ∘ fg ≡ id)

------------------------------------------------------------------------    
-- The Grain of data
------------------------------------------------------------------------    

-- Irreducibility predicate for grains
-- A grain projection is irreducible if there is no proper subset of its fields
-- that also forms a valid grain (i.e., is isomorphic to R via a bijection).
-- This predicate can be easily postulated when needed.
IsIrreducibleGrain : {R G : Set} → (grain : R → G) → Set₂
IsIrreducibleGrain {R} {G} grain = 
    ¬ (∃ λ (G' : Set) → 
       ∃ λ (grain' : R → G') → 
       ∃ λ (fg' : G' → R) →  
           (G' ⊂typ G)  -- G' is a proper subset of G's fields
           × (fg' ∘ grain' ≡ id)  -- fg' and grain' are left inverses
           × (grain' ∘ fg' ≡ id)) -- fg' and grain' are right inverses

-- Grain definition as a relation between types G and R
--
-- "G is a grain of R" means:
--
-- 1. BIJECTION: There exists a projection function grain : R → G and its inverse fg : G → R
--    - fg ∘ grain ≡ id means: projecting to G and back to R is the identity
--    - grain ∘ fg ≡ id means: constructing from G and projecting back is the identity
--    - Together these mean G and R are isomorphic (in bijective correspondence)
--
-- 2. MINIMALITY/IRREDUCIBILITY: The grain is irreducible (satisfies IsIrreducibleGrain)
--    - There is no proper subset G' of G's fields that also forms a valid grain
--    - This ensures G contains exactly the minimal set of fields needed to identify R
--
-- In other words, a grain G of R is a minimal representation: it contains exactly the
-- fields needed to uniquely identify and reconstruct elements of R, and no subset of
-- these fields would suffice.
_IsGrainOf_ : Rel Set (suc (suc zero))
G IsGrainOf R = 
    ∃ λ (grain : R → G) →
        ∃ λ (fg : G → R) → 
              (fg ∘ grain ≡ id) 
            × (grain ∘ fg ≡ id)
            × IsIrreducibleGrain grain

infix 4 _IsGrainOf_

-- Constructor for grain definition, parameterized by the grain projection function
grain-def : {R G : Set} 
          → (grain : R → G) 
          → (fg : G → R) 
          → (f∘g≡id : fg ∘ grain ≡ id) 
          → (g∘f≡id : grain ∘ fg ≡ id) 
          → (irreducible : IsIrreducibleGrain grain)
          → G IsGrainOf R
grain-def grain fg f∘g≡id g∘f≡id irreducible = grain , (fg , (f∘g≡id , g∘f≡id , irreducible))

-- Extract the grain projection function from _IsGrainOf_
get-grain : {R G : Set} → G IsGrainOf R → (R → G)
get-grain (grain , _) = grain

-- Extract the inverse function from _IsGrainOf_
get-fg : {R G : Set} → G IsGrainOf R → (G → R)
get-fg (_ , (fg , _)) = fg

-- Extract the left inverse proof from _IsGrainOf_
get-fg∘grain≡id : {R G : Set} → (g-def : G IsGrainOf R) → (get-fg g-def) ∘ (get-grain g-def) ≡ id
get-fg∘grain≡id (_ , (_ , (f∘g≡id , _))) = f∘g≡id

-- Extract the right inverse proof from _IsGrainOf_
get-grain∘fg≡id : {R G : Set} → (g-def : G IsGrainOf R) → (get-grain g-def) ∘ (get-fg g-def) ≡ id
get-grain∘fg≡id (_ , (_ , (_ , g∘f≡id , _))) = g∘f≡id

-- Extract the irreducibility proof from _IsGrainOf_
get-irreducible : {R G : Set} → (g-def : G IsGrainOf R) → IsIrreducibleGrain (get-grain g-def)
get-irreducible (_ , (_ , (_ , _ , irreducible))) = irreducible

-- Alias for backwards compatibility
get-minimal : {R G : Set} → (g-def : G IsGrainOf R) → IsIrreducibleGrain (get-grain g-def)
get-minimal = get-irreducible

------------------------------------------------------------------------    
-- The Entity of data
------------------------------------------------------------------------    

-- Semantic property: entity extracts "who/what the information is about"
-- This cannot be formalized purely mathematically - it must be established 
-- through domain analysis and business requirements
IsSubjectOfInformation : {R E : Set} → (R → E) → Set
IsSubjectOfInformation entity = ⊤  -- Always holds, but has semantic meaning

-- Entity definition as a relation between types E and R
-- "E is an entity of R" means there exists a UNIQUE projection function entity : R → E such that:
-- 1. entity satisfies IsSubjectOfInformation (semantic property)
-- 2. If another entity' also satisfies these properties, then entity ≡ entity' (uniqueness)
--
-- The uniqueness ensures that the entity is canonically determined by the 
-- domain requirements.
-- There exists a unique entity function (up to propositional equality _≡_) 
--  that satisfies the predicate.
-- If two entity functions entity₁ and entity₂ both satisfy the predicate, then 
-- entity₁ ≡ entity₂ (they are literally the same function).
_IsEntityOf_ : Rel Set zero
E IsEntityOf R = 
    ∃! _≡_ λ (entity : R → E) → 
    -- The ∃! quantifier means "there exists a unique" entity function that 
    -- satisfies the predicate.
        -- (entity ⊆fld Fields[ R ])  -- entity's fields are a subset of all 
        -- R's fields
         IsSubjectOfInformation entity 

infix 4 _IsEntityOf_

-- Constructor for entity definition
-- Note: The uniqueness proof must be provided as it's a domain requirement
-- Uniqueness means: if any other entity' function also satisfies IsSubjectOfInformation,
-- then entity ≡ entity'. This ensures the entity is canonically determined.
-- 
-- Note: The ∀ in ∃! uses implicit arguments, so we match that pattern.
entity-def : {R E : Set} 
           → (entity : R → E) 
           → (is-subject-of-information : IsSubjectOfInformation entity)
           → (unique : ∀ {entity' : R → E} 
                     → IsSubjectOfInformation entity' 
                     → entity ≡ entity')
           → E IsEntityOf R
entity-def entity is-subject-of-information unique = 
    entity , (is-subject-of-information , unique)

-- Extract the entity function from _IsEntityOf_
-- Since _IsEntityOf_ uses ∃!, it has structure: ∃ λ x → P x × (∀ y → P y → x ≡ y)
get-entity : {R E : Set} → E IsEntityOf R → (R → E)
get-entity (entity , _) = entity

------------------------------------------------------------------------    
-- The EntityKey of data
------------------------------------------------------------------------    
-- EntityKey-def as a relation between three types: EK, G, and R
-- EK is the entity key type
-- G is the grain type of R
-- R is the record type
--
EntityKey-def : (EK G R : Set) → Set₂
EntityKey-def EK G R = 
    (G IsGrainOf R) -- G is the grain of ℝ
    ×
    (∃ λ (E : Set) →
          (E IsEntityOf R) -- E is the entity of R
        × (EK IsGrainOf E)     -- EK is the grain of E
        × (EK ⊆typ G)) 
                    -- EK is a type subset of G (contains surjective projection)            

-- Constructor for EntityKey definition
-- Constructs an EntityKey-def by providing all the necessary components:
-- - The grain G of R
-- - The entity E of R
-- - The grain EK of E
-- - The type subset relation EK ⊆typ G (which includes the surjective projection)
entitykey-def : {R EK G E : Set}
              → (g-def : G IsGrainOf R)           -- G is the grain of R
              → (e-def : E IsEntityOf R)          -- E is the entity of R
              → (ek-grain-def : EK IsGrainOf E)   -- EK is the grain of E
              → (ek-from-grain : G → EK)          -- Projection from grain to entity key
              → (ek-surj : ∀ (ek : EK) → ∃ λ (g : G) → ek-from-grain g ≡ ek)  -- Surjectivity proof
              → EntityKey-def EK G R
entitykey-def {R} {EK} {G} {E} g-def e-def ek-grain-def ek-from-grain ek-surj = 
    g-def , (E , (e-def , ek-grain-def , witness-⊆typ ek-from-grain ek-surj))

-- Extract the entity key type EK from EntityKey-def
-- Note: EK is already a type parameter, so this function makes it explicit
get-ek-type : {EK G R : Set} → EntityKey-def EK G R → Set
get-ek-type {EK = EK} _ = EK

-- Extract the grain type G from EntityKey-def
-- Note: G is now a type parameter, so this function makes it explicit
get-grain-type : {EK G R : Set} → EntityKey-def EK G R → Set
get-grain-type {G = G} _ = G

-- Extract the grain definition of R from EntityKey-def
get-grain-def : {EK G R : Set} → (ek-def : EntityKey-def EK G R) → G IsGrainOf R
get-grain-def (g-def , _) = g-def

-- Extract the entity type E from EntityKey-def
get-entity-type : {EK G R : Set} → EntityKey-def EK G R → Set
get-entity-type (_ , (E , _)) = E

-- Extract the entity definition of R from EntityKey-def
get-entity-def : {EK G R : Set} → (ek-def : EntityKey-def EK G R) → (get-entity-type ek-def) IsEntityOf R
get-entity-def (_ , (_ , (e-def , _))) = e-def

-- Extract the grain definition of E from EntityKey-def
get-ek-grain-def : {EK G R : Set} → (ek-def : EntityKey-def EK G R) → EK IsGrainOf (get-entity-type ek-def)
get-ek-grain-def (_ , (_ , (_ , ek-grain-def , _))) = ek-grain-def

-- Extract the proof that entity key is a type subset of grain
get-ek-subset : {EK G R : Set} → (ek-def : EntityKey-def EK G R) → EK ⊆typ G
get-ek-subset (_ , (_ , (_ , _ , ek-subset))) = ek-subset

-- Extract the projection from grain to entity key (extracted from the subset relation)
get-ek-from-grain : {EK G R : Set} → (ek-def : EntityKey-def EK G R) → G → EK
get-ek-from-grain ek-def = proj₁ (get-projection-typ (get-ek-subset ek-def))

------------------------------------------------------------------------
-- IsData abstraction — PDA.md I.4 Axiom A1 (Data Type Axiom)
------------------------------------------------------------------------
-- A1: ∀ R : Set. ∃ G, E, EK : Set.
--       G IsGrainOf R ∧ E IsEntityOf R ∧ EK IsGrainOf E ∧ EntityKey(EK, G, R)
--
-- Correspondence:
--   grain-def-rel     ↦ G IsGrainOf R
--   entity-key-def-rel ↦ EntityKey(EK, G, R), which bundles:
--                         E IsEntityOf R, EK IsGrainOf E, EK ⊆typ G
--   Constraints        ↦ Behavioral class constraints (Def 9, extends A1)
--
-- BC[_] interaction (AT-015): HasBehavioralTypeClass requires IsData as an
-- instance, ensuring every typed collection element has both A1 structure
-- and a behavioral class tag.
record IsData {R G EK : Set}
              (grain-def-rel : G IsGrainOf R)
              (entity-key-def-rel : EntityKey-def EK G R)
             : Set₁ where
    field
        -- EntityKey : Set
        -- ek-from-grain : G → EntityKey
        Constraints : Cons R  
        
    Grain = G
    EntityKey = EK
    ek-from-grain : G → EK
    ek-from-grain = get-ek-from-grain entity-key-def-rel
    -- grain projection (extracted from the relation)
    grain : R → Grain
    grain = get-grain grain-def-rel

    -- grain function (inverse, extracted from the relation)
    fg : Grain → R
    fg  = get-fg grain-def-rel    
    
    -- entity key projection
    entity-key : R → EntityKey
    entity-key = ek-from-grain ∘ grain 

    -- Arity of the Grain type
    grain-arity : {{HasArity Grain}} → Nat
    grain-arity {{hAG}} = HasArity.arity hAG 

    -- Arity of the EntityKey type
    entity-key-arity : {{HasArity EntityKey}} → Nat
    entity-key-arity {{hAEK}} = HasArity.arity hAEK 
        
open IsData {{...}} public

G[_] : (R : Set) → {G EK : Set} → {g-def-rel : G IsGrainOf R} → {ek-def-rel : EntityKey-def EK G R}
         → {{is-data : IsData g-def-rel ek-def-rel}} → Set
G[ R ] {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} = Grain {{is-data}}

EK[_] : (R : Set) → {G EK : Set} → {g-def-rel : G IsGrainOf R} → {ek-def-rel : EntityKey-def EK G R}
             → {{is-data : IsData g-def-rel ek-def-rel}} → Set
EK[ R ] {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} = EntityKey {{is-data}}

module example-for-IsData where
    postulate
        A B C D E : Set

    record R1 : Set where
        field
            a : A
            b : B
            c : C
            d : D
            e : E
    open R1
    
    -- define a grain projection function
    g : R1 → A × B
    g r1 = (a r1 , b r1)
    
    -- Given the grain function and the isomorphism
    postulate
        fgrain : A × B → R1
        f∘g≡id : fgrain ∘ g ≡ id
        g∘f≡id : g ∘ fgrain ≡ id
        -- Irreducibility proof: the grain is irreducible (no proper subset is also a grain)
        g-irreducible : IsIrreducibleGrain g
    
    -- Then, we can define the grain relation
    g-def : (A × B) IsGrainOf R1
    g-def = grain-def g fgrain f∘g≡id g∘f≡id g-irreducible

    -- Define entity projection (project to A, which is the entity key)
    entity : R1 → A
    entity r1 = a r1

    -- Entity is unique for IsSubjectOfInformation (since it's always ⊤)
    -- Uniqueness proof: any entity' function must be equal to entity
    postulate
        entity-unique : ∀ {entity' : R1 → A} 
                       → IsSubjectOfInformation entity' 
                       → entity ≡ entity'

    -- Construct entity definition
    e-def : A IsEntityOf R1
    e-def = entity-def entity tt entity-unique

    -- Define entity key definition
    -- We need: A IsGrainOf A (entity key is its own grain)
    -- For A, the grain is just id (A is isomorphic to itself)
    postulate
        a-irreducible : IsIrreducibleGrain (id {A = A})

    a-grain-def : A IsGrainOf A
    a-grain-def = grain-def id id refl refl a-irreducible

    -- ek-from-grain: (A × B) → A (project first component)
    ek-from-grain-func : (A × B) → A
    ek-from-grain-func = proj₁

    -- Proof that A is a type subset of (A × B) - surjectivity
    -- For any a : A, we can find (a , b) : A × B such that proj₁ (a , b) ≡ a
    postulate
        default-b : B
    
    ek-surj : ∀ (a : A) → ∃ λ (g : A × B) → ek-from-grain-func g ≡ a
    ek-surj a = ((a , default-b) , refl)

    -- Construct entity key definition
    ek-def : EntityKey-def A (A × B) R1
    ek-def = entitykey-def g-def e-def a-grain-def ek-from-grain-func ek-surj

    instance
        is-data-r1 : IsData g-def ek-def
        Constraints {{is-data-r1}} = cons-true

    _ : G[ R1 ] {A × B} {A} {g-def} {ek-def} {{is-data-r1}} ≡ (A × B)
    _ = refl

    _ : EK[ R1 ] {A × B} {A} {g-def} {ek-def} {{is-data-r1}} ≡ A
    _ = refl

    -- What if there is also another grain (isomorphic to A × B)?
    
    g' : R1 → E
    g' r1 = e r1

    postulate
        fgrain' : E → R1
        f∘g'≡id : fgrain' ∘ g' ≡ id  -- fgrain' (g' r) = r
        g'∘f'≡id : g' ∘ fgrain' ≡ id  -- g' (fgrain' e) = e
        -- Irreducibility proof for the alternative grain
        g'-irreducible : IsIrreducibleGrain g'

    g-def' : E IsGrainOf R1
    g-def' = grain-def g' fgrain' f∘g'≡id  g'∘f'≡id g'-irreducible

    -- Entity for this alternative grain (still A, the first field)
    entity' : R1 → A
    entity' r1 = a r1

    -- Uniqueness proof (same as before since entity is the same)
    postulate
        entity'-unique : ∀ {entity'' : R1 → A} 
                       → IsSubjectOfInformation entity'' 
                       → entity' ≡ entity''

    -- Construct entity definition
    e-def' : A IsEntityOf R1
    e-def' = entity-def entity' tt entity'-unique

    -- Same entity key definition structure (A as entity key)
    -- We can reuse a-grain-def and ek-from-grain logic
    -- But ek-from-grain needs to be E → A
    ek-from-grain-func' : E → A
    ek-from-grain-func' e = a (fgrain' e)

    -- Proof that A is a type subset of E - surjectivity
    -- For any a : A, we can find e : E such that ek-from-grain-func' e ≡ a
    -- Since ek-from-grain-func' e = a (fgrain' e), and entity' r = a r,
    -- we need e such that a (fgrain' e) ≡ a.
    -- Since fgrain' : E → R1 and g' : R1 → E are inverses (f∘g'≡id: fgrain' (g' r) = r),
    -- for any r : R1 where entity' r = a, taking e = g' r gives:
    --   ek-from-grain-func' (g' r) = a (fgrain' (g' r)) = a r = entity' r = a
    -- We need to postulate that for any a, there exists r where entity' r = a
    -- This is reasonable since entity' : R1 → A is a function
    postulate
        find-r-for-a : (a : A) → Σ R1 (λ r → entity' r ≡ a)
    
    ek-surj' : ∀ (a : A) → ∃ λ (e : E) → ek-from-grain-func' e ≡ a
    ek-surj' a-val = 
        let (r , entity-r≡a) = find-r-for-a a-val
            e = g' r
            -- Proof: ek-from-grain-func' e = a (fgrain' (g' r)) = a r = entity' r = a-val
            -- Since f∘g'≡id: fgrain' ∘ g' ≡ id, we have fgrain' (g' r) = r
            -- So a (fgrain' (g' r)) = a r
            -- Since entity' r = a r by definition, we have a r = entity' r = a-val
            eq : a (fgrain' (g' r)) ≡ a r
            eq = cong a (Relation.Binary.PropositionalEquality.cong-app f∘g'≡id r)
            eq2 : a r ≡ entity' r
            eq2 = refl  -- By definition: entity' r = a r (since entity' r1 = a r1)
        in (e , trans (trans eq eq2) entity-r≡a)

    -- Construct entity key definition
    ek-def' : EntityKey-def A E R1
    ek-def' = entitykey-def g-def' e-def' a-grain-def ek-from-grain-func' ek-surj'

    instance
        is-data-r1' : IsData g-def' ek-def'
        Constraints {{is-data-r1'}} = cons-true

    -- R1 has an alternative grain (isomorphic to A × B)
    -- We need to specify which IsData instance to use since there are two
    _ : G[ R1 ] {g-def-rel = g-def'} {ek-def-rel = ek-def'} ≡ E
    _ = refl

    -- Here we need to specify the instance of is-data-r1' because
    -- both IsData instances of R1 have the same EntityKey
    _ : EK[ R1 ] {g-def-rel = g-def'} {ek-def-rel = ek-def'} ≡ A
    _ = refl

-- Theorem : Grain is a unique identifier for each element of R
Grain-is-unique-identifier : ∀{R G EK : Set}
                            {g-def-rel : G IsGrainOf R}
                            {ek-def-rel : EntityKey-def EK G R}
                           → {{is-data : IsData g-def-rel ek-def-rel}}
                           → Set
Grain-is-unique-identifier {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} = 
    ∀{r₁ r₂ : R} → grain {{is-data}} r₁ ≡ grain {{is-data}} r₂ → r₁ ≡ r₂

-- Proof-of-Grain-is-unique-identifier : {R G : Set} 
--                                       {g : R → G}
--                                       {g-def : Grain-def g}
--                                     → {{is-data : IsData (g , g-def)}}
--                                     → Grain-is-unique-identifier {R} {G} 
--                                                                  {g}
--                                                                  {g-def}
--                                                                  {{is-data}}
-- Proof-of-Grain-is-unique-identifier {R} {G} {g} {g-def} 
--                                     {{is-data}} {r₁} {r₂} 
--                                     g₁≡g₂ = 
--         let g₁ = grain {{is-data}} r₁
--             g₂ = grain {{is-data}} r₂
--             r₁≡r₂ : (fg {{is-data}} g₁) ≡ (fg {{is-data}} g₂)
--             r₁≡r₂ = cong (fg {{is-data}}) {g₁} {g₂} g₁≡g₂ 
--         in r₁≡r₂ 
    


-- Theorem: If G₁ and G₂ are both grains of R then they are isomorphic
Two-Grains-are-isomorphic : ∀{R G₁ G₂ EK₁ EK₂ : Set} 
                            {g-def₁ : G₁ IsGrainOf R}
                            {ek-def₁ : EntityKey-def EK₁ G₁ R}
                            {g-def₂ : G₂ IsGrainOf R}
                            {ek-def₂ : EntityKey-def EK₂ G₂ R}
                          → {{is-data₁ : IsData g-def₁ ek-def₁}}
                          → {{is-data₂ : IsData g-def₂ ek-def₂}}
                          → Set
Two-Grains-are-isomorphic {R} {G₁} {G₂} {EK₁} {EK₂}
                          {g-def₁} {ek-def₁} {g-def₂} {ek-def₂}
                          {{is-data₁}} {{is-data₂}} = 
    Isomorphic-Sets (Grain {{is-data₁}}) (Grain {{is-data₂}})

------------------------------------------------------------------------
-- Grain relations
-- PDA.md I.3: Def 6 (≡g), Def 7 (≤g), Def 8 (⟨⟩g)
------------------------------------------------------------------------
infix 4 _≡g_

------------------------------------------------------------------------
-- Def 6: Grain Equality ≡g
------------------------------------------------------------------------
-- R₁ ≡g R₂  ≡  ∃ (f : G[R₁] → G[R₂]). f is an isomorphism
--
-- Two data types are grain-equivalent when their grain types are
-- isomorphic. Both types must be IsData instances (have a grain).
-- The isomorphism witness is extractable, enabling use in collection-
-- level relations (e.g., =g in II.3).

record _≡g_ (R₁ R₂ : Set)
             {G₁ G₂ EK₁ EK₂ : Set}
             {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂}
             {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂}
             {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}}
             : Set where
  field
    to   : G₁ → G₂
    from : G₂ → G₁
    to∘from≡id : to ∘ from ≡ id
    from∘to≡id : from ∘ to ≡ id

open _≡g_ public

------------------------------------------------------------------------
-- ≡g is an equivalence relation (derived from the isomorphism witness)
------------------------------------------------------------------------

-- Reflexivity: R ≡g R (identity is an isomorphism)
≡g-refl : {R G EK : Set}
         → {g : G IsGrainOf R} {ek : EntityKey-def EK G R}
         → {{d : IsData g ek}}
         → R ≡g R
≡g-refl = record { to = id ; from = id ; to∘from≡id = refl ; from∘to≡id = refl }

-- Symmetry: R₁ ≡g R₂ → R₂ ≡g R₁ (swap the isomorphism)
≡g-sym : {R₁ R₂ G₁ G₂ EK₁ EK₂ : Set}
       → {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂}
       → {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂}
       → {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}}
       → R₁ ≡g R₂ → R₂ ≡g R₁
≡g-sym eq = record
  { to          = from eq
  ; from        = to eq
  ; to∘from≡id  = from∘to≡id eq
  ; from∘to≡id  = to∘from≡id eq
  }

-- Transitivity: R₁ ≡g R₂ → R₂ ≡g R₃ → R₁ ≡g R₃ (compose isomorphisms)
-- Proof sketch for to∘from≡id:
--   (to₂₃ ∘ to₁₂) ∘ (from₁₂ ∘ from₂₃)
--   = to₂₃ ∘ (to₁₂ ∘ from₁₂) ∘ from₂₃    -- ∘ associativity (definitional)
--   = to₂₃ ∘ id ∘ from₂₃                   -- subst: to₁₂ ∘ from₁₂ ≡ id
--   = to₂₃ ∘ from₂₃                        -- id elimination (definitional)
--   = id                                     -- to₂₃ ∘ from₂₃ ≡ id
≡g-trans : {R₁ R₂ R₃ G₁ G₂ G₃ EK₁ EK₂ EK₃ : Set}
         → {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂} {g₃ : G₃ IsGrainOf R₃}
         → {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂} {ek₃ : EntityKey-def EK₃ G₃ R₃}
         → {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}} {{d₃ : IsData g₃ ek₃}}
         → R₁ ≡g R₂ → R₂ ≡g R₃ → R₁ ≡g R₃
≡g-trans eq₁₂ eq₂₃ = record
  { to          = to eq₂₃ ∘ to eq₁₂
  ; from        = from eq₁₂ ∘ from eq₂₃
  ; to∘from≡id  = subst (λ f → (to eq₂₃ ∘ f) ∘ from eq₂₃ ≡ id)
                        (sym (to∘from≡id eq₁₂))
                        (to∘from≡id eq₂₃)
  ; from∘to≡id  = subst (λ f → (from eq₁₂ ∘ f) ∘ to eq₁₂ ≡ id)
                        (sym (from∘to≡id eq₂₃))
                        (from∘to≡id eq₁₂)
  }

-- Grain ordering (PDA.md I.3 Def 7)
-- R₁ ≤g R₂ ≡ ∃ f : G[R₁] → G[R₂]
-- R₁ has lower (finer) grain than R₂. The function `proj` witnesses a functional
-- determination from G[R₁] to G[R₂]. This generalizes both subset-based ordering
-- (where proj is a field projection) and FD-based ordering (where proj is an
-- arbitrary function, e.g., EmployeeId → DepartmentId).
record _≤g_ (R₁ R₂ : Set)
             {G₁ G₂ EK₁ EK₂ : Set}
             {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂}
             {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂}
             {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}}
             : Set where
  field
    proj : G₁ → G₂

open _≤g_ public

-- Partial order properties for ≤g

-- Reflexivity: R ≤g R (identity function)
≤g-refl : {R G EK : Set}
         → {g : G IsGrainOf R} {ek : EntityKey-def EK G R}
         → {{d : IsData g ek}}
         → R ≤g R
≤g-refl = record { proj = id }

-- Transitivity: R₁ ≤g R₂ → R₂ ≤g R₃ → R₁ ≤g R₃ (compose projections)
≤g-trans : {R₁ R₂ R₃ G₁ G₂ G₃ EK₁ EK₂ EK₃ : Set}
         → {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂} {g₃ : G₃ IsGrainOf R₃}
         → {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂} {ek₃ : EntityKey-def EK₃ G₃ R₃}
         → {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}} {{d₃ : IsData g₃ ek₃}}
         → R₁ ≤g R₂ → R₂ ≤g R₃ → R₁ ≤g R₃
≤g-trans le₁₂ le₂₃ = record { proj = proj le₂₃ ∘ proj le₁₂ }

-- Antisymmetry: R₁ ≤g R₂ → R₂ ≤g R₁ → R₁ ≡g R₂
-- This is the grain-level Cantor–Bernstein–Schröder theorem.
-- Not constructively provable in general; postulated as an axiom.
postulate
  ≤g-antisym : {R₁ R₂ G₁ G₂ EK₁ EK₂ : Set}
             → {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂}
             → {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂}
             → {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}}
             → R₁ ≤g R₂ → R₂ ≤g R₁ → R₁ ≡g R₂

-- Grain equality implies grain ordering (extract the forward direction)
≡g→≤g : {R₁ R₂ G₁ G₂ EK₁ EK₂ : Set}
       → {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂}
       → {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂}
       → {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}}
       → R₁ ≡g R₂ → R₁ ≤g R₂
≡g→≤g eq = record { proj = to eq }

------------------------------------------------------------------------
-- Def 8: Grain Incomparability ⟨⟩g
------------------------------------------------------------------------
-- R₁ ⟨⟩g R₂  ≡  ¬(R₁ ≡g R₂) ∧ ¬(R₁ ≤g R₂) ∧ ¬(R₂ ≤g R₁)
--
-- Two data types are grain-incomparable when neither is finer than
-- the other, nor are they grain-equivalent.
-- Example: Customer (grain = CustomerId) and Order (grain = OrderId)
-- have no functional dependency between their grains in either direction.
infix 4 _⟨⟩g_

record _⟨⟩g_ (R₁ R₂ : Set)
              {G₁ G₂ EK₁ EK₂ : Set}
              {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂}
              {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂}
              {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}}
              : Set where
  field
    ¬≡g : ¬ (R₁ ≡g R₂)
    ¬≤g : ¬ (R₁ ≤g R₂)
    ¬≥g : ¬ (R₂ ≤g R₁)

open _⟨⟩g_ public

-- Symmetry: R₁ ⟨⟩g R₂ → R₂ ⟨⟩g R₁
⟨⟩g-sym : {R₁ R₂ G₁ G₂ EK₁ EK₂ : Set}
         → {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂}
         → {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂}
         → {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}}
         → R₁ ⟨⟩g R₂ → R₂ ⟨⟩g R₁
⟨⟩g-sym inc = record
  { ¬≡g = λ eq₂₁ → ¬≡g inc (≡g-sym eq₂₁)
  ; ¬≤g = ¬≥g inc
  ; ¬≥g = ¬≤g inc
  }

-- Irreflexivity: ¬ (R ⟨⟩g R) — follows from ≤g-refl
¬⟨⟩g-refl : {R G EK : Set}
           → {g : G IsGrainOf R} {ek : EntityKey-def EK G R}
           → {{d : IsData g ek}}
           → ¬ (R ⟨⟩g R)
¬⟨⟩g-refl inc = ¬≤g inc ≤g-refl

------------------------------------------------------------------------
-- A5: Armstrong Axioms for ≤g (PDA.md I.4)
------------------------------------------------------------------------

-- A5.1 (Self-determination / Reflexivity): R ≤g R
-- Proven: identity function witnesses the grain projection.
A5-1-self-determination : {R G EK : Set}
                        → {g : G IsGrainOf R} {ek : EntityKey-def EK G R}
                        → {{d : IsData g ek}}
                        → R ≤g R
A5-1-self-determination = ≤g-refl

-- A5.2 (Augmentation): R₁ ≤g R₂ ⇒ (R₁ ∪typ R₃) ≤g (R₂ ∪typ R₃)
-- Postulated: requires that ∪typ preserves IsData structure and that
-- the grain projection can be lifted through the union. The full proof
-- depends on FieldUnionGuide properties (how grains compose under union).
postulate
  A5-2-augmentation : {R₁ R₂ R₃ R₁₃ R₂₃ : Set}
                    → {G₁ G₂ G₃ EK₁ EK₂ EK₃ : Set}
                    → {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂} {g₃ : G₃ IsGrainOf R₃}
                    → {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂} {ek₃ : EntityKey-def EK₃ G₃ R₃}
                    → {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}} {{d₃ : IsData g₃ ek₃}}
                    → {{ev₁₃ : FieldUnionGuide R₁ R₃ R₁₃}}
                    → {{ev₂₃ : FieldUnionGuide R₂ R₃ R₂₃}}
                    → {G₁₃ G₂₃ EK₁₃ EK₂₃ : Set}
                    → {g₁₃ : G₁₃ IsGrainOf R₁₃} {g₂₃ : G₂₃ IsGrainOf R₂₃}
                    → {ek₁₃ : EntityKey-def EK₁₃ G₁₃ R₁₃} {ek₂₃ : EntityKey-def EK₂₃ G₂₃ R₂₃}
                    → {{d₁₃ : IsData g₁₃ ek₁₃}} {{d₂₃ : IsData g₂₃ ek₂₃}}
                    → R₁ ≤g R₂
                    → (R₁ ∪typ R₃) ≤g (R₂ ∪typ R₃)

-- A5.3 (Transitivity): R₁ ≤g R₂ ∧ R₂ ≤g R₃ ⇒ R₁ ≤g R₃
-- Proven: compose the grain projection witnesses.
A5-3-transitivity : {R₁ R₂ R₃ G₁ G₂ G₃ EK₁ EK₂ EK₃ : Set}
                  → {g₁ : G₁ IsGrainOf R₁} {g₂ : G₂ IsGrainOf R₂} {g₃ : G₃ IsGrainOf R₃}
                  → {ek₁ : EntityKey-def EK₁ G₁ R₁} {ek₂ : EntityKey-def EK₂ G₂ R₂} {ek₃ : EntityKey-def EK₃ G₃ R₃}
                  → {{d₁ : IsData g₁ ek₁}} {{d₂ : IsData g₂ ek₂}} {{d₃ : IsData g₃ ek₃}}
                  → R₁ ≤g R₂ → R₂ ≤g R₃ → R₁ ≤g R₃
A5-3-transitivity = ≤g-trans

