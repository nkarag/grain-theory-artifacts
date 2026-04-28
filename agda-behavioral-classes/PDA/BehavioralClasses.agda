module PDA.BehavioralClasses where

open import PDA.Relations public

------------------------------------------------------------------------    
-- Behavioral type classes
------------------------------------------------------------------------
-- See: https://agda.readthedocs.io/en/v2.5.2/language/record-types.html#instance-fields

record IsEntity (R : Set) 
                {G EK : Set} 
                {g-def-rel : G IsGrainOf R}
                {ek-def-rel : EntityKey-def EK G R}
                {{is-data : IsData g-def-rel ek-def-rel}}
                : Set₁ where
    constructor is-entity
    field    
        grain-cond : Grain {{is-data}} ≡ EntityKey {{is-data}}

open IsEntity {{...}} public 

record IsEvent {R : Set} 
               {G EK : Set} 
               {g-def-rel : G IsGrainOf R}
               {ek-def-rel : EntityKey-def EK G R}
               {{is-data : IsData g-def-rel ek-def-rel}}
               {Event-dtm : Set}
               (event-dtm : R → Event-dtm)
               : Set₁ where
    constructor is-event
    field
        -- Event-dtm total ordering
        _<to=_ : Rel Event-dtm 0ℓ -- Event-dtm → Event-dtm → Set
        overlap {{tot-ordering}} : TotalOrd _<to=_

        -- Grain condition
        grain-cond : Grain {{is-data}} ≡ (EntityKey {{is-data}} × Event-dtm)

    -- Causality relation is a partial order.
    -- When two events take place at the same point in time 
    -- event-dtm r₁ = event-dtm r₂, which means they happen concurrently,
    -- the causality relation is undefined. They are independent, they don't
    -- have a cause-and-effect relationship.
    -- The following proves that the Event-dtm ordering 
    -- is consistent with causality:
    -- if r₁ happened-before r₂, then event-dtm r₁ <to event-dtm r₂
    -- which means that if r₁ causes r₂, then event-dtm r₁ < event-dtm r₂
    -- or if r₁ is-concurrent-with r₂, then event-dtm r₁ = event-dtm r₂
    -- -------
    --   The total order ≤ on EventDtm gives us three cases for any two timestamps t₁ and t₂:            
    -- * t₁ < t₂ (strictly less)
    -- * t₁ = t₂ (equal)          
    -- * t₁ > t₂ (strictly greater)
    -- When we lift this to events, we map these cases to:                 
    -- * t₁ < t₂ → r₁ happened-before r₂           
    -- * t₁ = t₂ → r₁ is-concurrent-with r₂ (incomparable in causal order)
    -- * t₁ > t₂ → r₂ happened-before r₁
    _happened-before_  : Rel R 0ℓ -- R → R → Set
    r₁ happened-before r₂ = (event-dtm r₁) <to (event-dtm r₂)

    _is-concurrent-with_ : Rel R 0ℓ -- R → R → Set
    r₁ is-concurrent-with r₂ = 
        (entity-key r₁ ≢ entity-key r₂) 
        × 
        (event-dtm r₁) ≡ (event-dtm r₂)

open IsEvent {{...}} public 

------------------------------------------------------------------------    
-- IsMultiVersion
------------------------------------------------------------------------
-- Payload constraint
-- Payload does not include any field from grain
Payload-cons : {R : Set} 
               {G EK : Set} 
               {g-def-rel : G IsGrainOf R} 
               {ek-def-rel : EntityKey-def EK G R}
               {{is-data : IsData g-def-rel ek-def-rel}} 
               {Payload : Set}
             → (payload : R → Payload) → Set₁
Payload-cons {R} {G} {g-def-rel} {{is-data}} {Payload} payload = 
      {F : Set}
    → (payload ⊂fld id)
      × 
      (Fields-are-disjoint {Payload} {Grain {{is-data}}} {F} {R} payload grain)

-- Consecutive versions constraint
Consecutive-versions-cons : {R : Set} 
                            {G EK : Set} 
                            {g-def-rel : G IsGrainOf R} 
                            {ek-def-rel : EntityKey-def EK G R}
                            {{is-data : IsData g-def-rel ek-def-rel}} 
                            {From-dtm : Set}
                            {from-dtm : R → From-dtm}
                            {Payload : Set}
                            (payload : R → Payload)
                            {{is-ev : IsEvent {R} {G} {EK} {g-def-rel} {ek-def-rel} {From-dtm} from-dtm}}
                          → Set
Consecutive-versions-cons {R} {G} {g-def-rel} {{is-data}}{From-dtm} {from-dtm}  {Payload} payload {{is-ev}} = 
      ∀(r₁ r₂ : R)
    → entity-key {{is-data}} r₁ ≡ entity-key {{is-data}} r₂
    → r₁ happened-before r₂
    → payload r₁ ≡ payload r₂
    → ∃(λ r →  (payload r ≢ payload r₁) 
            ×  r₁ happened-before r
            ×  r happened-before r₂
        )   

record IsMultiVersion {R : Set} 
                      {G EK : Set} 
                      {g-def-rel : G IsGrainOf R} 
                      {ek-def-rel : EntityKey-def EK G R}
                      {{is-data : IsData g-def-rel ek-def-rel}}
                      {From-dtm : Set}
                      (from-dtm : R → From-dtm)
                      {Payload : Set}
                      (payload : R → Payload)
                      : Set₁ where
    constructor is-multi-version
    field
        -- superclass
        overlap {{is-an-event}} : IsEvent {R} {G} {EK} {g-def-rel} {ek-def-rel}
                                         {From-dtm} from-dtm

        -- Payload constraint
        -- Payload does not include any field from grain
        payload-cons : Payload-cons {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {Payload} payload
                       
        -- Consecutive versions constraint
        consecutive-versions-cons : Consecutive-versions-cons {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {From-dtm} {from-dtm} {Payload} payload                
        
    _effective-before_ = _happened-before_

open IsMultiVersion {{...}} public 

instance
    -- A multi-version is also an event
    a-multi-version-is-an-event : 
          {R : Set} 
        → {G EK : Set} 
        → {g-def-rel : G IsGrainOf R} 
        → {ek-def-rel : EntityKey-def EK G R}
        → {{is-data : IsData g-def-rel ek-def-rel}}
        → {From-dtm : Set}
        → {from-dtm : R → From-dtm}
        → {Payload : Set}
        → {payload : R → Payload}
        → {{is-mv : IsMultiVersion {R} {G} {EK} {g-def-rel} {ek-def-rel}
                                          {From-dtm} from-dtm {Payload} payload}}
        → IsEvent {R} {G} {EK} {g-def-rel} {ek-def-rel} {From-dtm} from-dtm
    a-multi-version-is-an-event {{is-mv}} = is-an-event 

record IsSeqEvent {R : Set} 
                  {G EK : Set} 
                  {g-def-rel : G IsGrainOf R}
                  {ek-def-rel : EntityKey-def EK G R}
                  {{is-data : IsData g-def-rel ek-def-rel}}
                  {Event-dtm : Set}
                  (event-dtm : R → Event-dtm)
                  : Set₁ where
    constructor is-seq-event
    field
        -- Event-dtm strict total ordering (no equality of time points)
        _<st_ : Rel Event-dtm 0ℓ -- Event-dtm → Event-dtm → Set
        overlap {{tot-ordering}} : StrictTotalOrd _<st_

        -- Grain condition
        grain-cond : Grain {{is-data}} ≡ EntityKey {{is-data}} 
                     × 
                     Grain {{is-data}} ≡ Event-dtm

    -- Linearizability of events is a strict total order.
    -- We do not allow two events to happen at the same time.
    -- so we do not allow equality of time points.
    -- The following proves that the Event-dtm ordering 
    -- is consistent with Linearizability:
    -- if r₁ happened-before-strict r₂, then event-dtm r₁ <st event-dtm r₂
    _happened-before-seq_  : Rel R 0ℓ -- R → R → Set
    r₁ happened-before-seq r₂ = (event-dtm r₁) <st (event-dtm r₂)

open IsSeqEvent {{...}} public 

-- Complete entity coverage constraint:
-- For any snapshot element r, the entity grain function applied to its 
-- timestamp returns exactly the collection stored in the snapshot field.
-- This ensures that each snapshot captures the complete state of all 
-- entities at that point in time.
IsCompleteEntityCoverage : {R : Set} 
                           {G EK : Set} 
                           {C : Set → Set}
                           {{is-coll : IsDataColl C}}                  
                           {g-def-rel : G IsGrainOf R}
                           {ek-def-rel : EntityKey-def EK G R}
                           {{is-data : IsData g-def-rel ek-def-rel}}
                           {Snapshot-dtm : Set}
                           {S : Set} -- state of an entity
                           (snapshot-dtm : R → Snapshot-dtm)
                           (snapshot : R → C S)
                           (entity-fg : Snapshot-dtm → C S)
                           → Set₁
IsCompleteEntityCoverage {R} {G} {EK} {C} 
                         {{is-coll}} 
                         {g-def-rel} {ek-def-rel} {{is-data}} 
                         {Snapshot-dtm} {S} 
                         snapshot-dtm snapshot entity-fg = 
   ∀(r : R)
   → (entity-fg (snapshot-dtm r)) =coll (snapshot r) 

record IsSnapshot {R : Set} 
                  {G EK : Set} 
                  {C : Set → Set}
                  {{is-coll : IsDataColl C}}                  
                  {g-def-rel : G IsGrainOf R}
                  {ek-def-rel : EntityKey-def EK G R}
                  {{is-data : IsData g-def-rel ek-def-rel}}
                  {Snapshot-dtm : Set}
                  {S : Set} -- state of an entity
                  (snapshot-dtm : R → Snapshot-dtm)
                  (snapshot : R → C S)
                  : Set₁ where
    constructor is-snapshot
    field
        -- superclass
        overlap {{is-a-seq-event}} : IsSeqEvent {R} {G} {EK} {g-def-rel} {ek-def-rel}
                                              {Snapshot-dtm} snapshot-dtm

        -- Entity grain function
        -- Given the snapshot-dtm we get a collection of entities' states
        entity-fg : Snapshot-dtm → C S

        -- Complete entity coverage condition
        is-complete-entity-coverage : IsCompleteEntityCoverage {R} {G} {EK} {C} 
                                                               {{is-coll}} 
                                                               {g-def-rel} 
                                                               {ek-def-rel}
                                                               {{is-data}} 
                                                               {Snapshot-dtm} 
                                                               {S} 
                                                               snapshot-dtm 
                                                               snapshot 
                                                               entity-fg



open IsSnapshot {{...}} public

instance
    -- A snapshot is also a seq-event
    a-snapshot-is-a-seq-event : 
                  {R : Set} 
                  {G EK : Set} 
                  {C : Set → Set}
                  {{is-coll : IsDataColl C}}                  
                  {g-def-rel : G IsGrainOf R}
                  {ek-def-rel : EntityKey-def EK G R}
                  {{is-data : IsData g-def-rel ek-def-rel}}
                  {Snapshot-dtm : Set}
                  {S : Set} -- state of an entity
                  {snapshot-dtm : R → Snapshot-dtm}
                  {snapshot : R → C S}
                → {{is-snap : IsSnapshot {R} {G} {EK} {C} {{is-coll}}
                                             {g-def-rel} 
                                             {ek-def-rel}
                                             {{is-data}} 
                                             {Snapshot-dtm} {S}
                                             snapshot-dtm snapshot}}
                → IsSeqEvent {R} {G} {EK} {g-def-rel} {ek-def-rel} {Snapshot-dtm} snapshot-dtm
    a-snapshot-is-a-seq-event {R} {G} {EK} {C} {{is-coll}} {g-def-rel} {ek-def-rel} {{is-data}} {Snapshot-dtm} {S} {snapshot-dtm} {snapshot} {{is-snap}} = is-a-seq-event

-- This is just a generalization of IsEvent for any partial-ordering relation
record IsOrdered {R : Set} 
                        {G EK : Set} 
                        {g-def-rel : G IsGrainOf R}
                        {ek-def-rel : EntityKey-def EK G R}
                        {{is-data : IsData g-def-rel ek-def-rel}}
                        {OrdType : Set}
                        (ord-field : R → OrdType)
                        : Set₁ where
    constructor is-ordered
    field
        -- Ordering (total order)
        _<to=_ : Rel OrdType 0ℓ -- OrdType → OrdType → Set
        overlap {{tot-ordering}} : TotalOrd _<to=_

        -- Grain condition
        grain-cond : Grain {{is-data}} ≡ (EntityKey {{is-data}} × OrdType)

    _precedes_ : Rel R 0ℓ -- R → R → Set
    r₁ precedes r₂ = (ord-field r₁) <to (ord-field r₂)

    _ties_ : Rel R 0ℓ -- R → R → Set
    r₁ ties r₂ = (ord-field r₁) ≡ (ord-field r₂)

open IsOrdered {{...}} public 

-- This is just a generalization of IsSeqEvent for any total-ordering relation
record IsSeqOrdered {R : Set} 
                  {G EK : Set} 
                  {g-def-rel : G IsGrainOf R}
                  {ek-def-rel : EntityKey-def EK G R}
                  {{is-data : IsData g-def-rel ek-def-rel}}
                  {OrdType : Set}
                  (ord-field : R → OrdType)
                  : Set₁ where
    constructor is-seq-ordered
    field
        -- Ordering (strict total order)
        _<st-gen_ : Rel OrdType 0ℓ -- OrdType → OrdType → Set
        overlap {{tot-ordering}} : StrictTotalOrd _<st-gen_

        -- Grain condition
        grain-cond : Grain {{is-data}} ≡ EntityKey {{is-data}} 
                     × 
                     Grain {{is-data}} ≡ OrdType

    _precedes-seq_ : Rel R 0ℓ -- R → R → Set
    r₁ precedes-seq r₂ = (ord-field r₁) <st-gen (ord-field r₂)

open IsSeqOrdered {{...}} public 

-- This models a 1:N relation between two types Child and Parent.
-- A Child has one Parent and a Parent can have many Children.
-- We leave it generic without specifying the type class of the Parent
-- or the Child. It can be anything (an entity, an event, etc.).
-- The only requirement is that Child has a field pointing to
-- the grain of the Parent.
-- The use of Maybe indicates that a child may or may not have a parent (e.g., -- root nodes in a hierarchy).
record HasParent {Child Parent : Set}
                 {G-Child EK-Child : Set}
                 {G-Parent EK-Parent : Set}
                 {g-def-child-rel : G-Child IsGrainOf Child}
                 {ek-def-child-rel : EntityKey-def EK-Child G-Child Child}
                 {g-def-parent-rel : G-Parent IsGrainOf Parent}
                 {ek-def-parent-rel : EntityKey-def EK-Parent G-Parent Parent}
                 {{is-data-child : IsData g-def-child-rel ek-def-child-rel}}
                 {{is-data-parent : IsData g-def-parent-rel ek-def-parent-rel}}
                 (parent : Child → Maybe G-Parent)
                 : Set₁ where
    constructor has-parent-constructor

    _has-parent_ : REL Child Parent 0ℓ -- Child → Parent → Set
    c has-parent p = parent c ≡ just (grain p)

open HasParent {{...}} public 

-- Generic N:M relation between two types
-- This can be considered as the edge (an arrow) of a directed graph 
-- modelling this relation: r₁ is-related-to r₂
--
record IsNMRelation {R Party₁ Party₂ : Set}
                    {G EK G₁ EK₁ G₂ EK₂ : Set}
                    {g-def-rel : G IsGrainOf R}
                    {ek-def-rel : EntityKey-def EK G R}
                    {g-def-r₁-rel : G₁ IsGrainOf Party₁}
                    {ek-def-r₁-rel : EntityKey-def EK₁ G₁ Party₁}
                    {g-def-r₂-rel : G₂ IsGrainOf Party₂}
                    {ek-def-r₂-rel : EntityKey-def EK₂ G₂ Party₂}
                    {{is-data : IsData g-def-rel ek-def-rel}}
                    {{is-data-party₁ : IsData g-def-r₁-rel ek-def-r₁-rel}}
                    {{is-data-party₂ : IsData g-def-r₂-rel ek-def-r₂-rel}}
                    (party₁ : R → G₁)
                    (party₂ : R → G₂)
                    : Set₁ where
    constructor is-nm-relation
    field
        grain-cond : Grain {{is-data}} ≡ EntityKey {{is-data}}
                     ×
                     Grain {{is-data}} ≡ (G₁ × G₂)
     

    _relates-to_ : REL Party₁ Party₂ 0ℓ -- R → Party₁ → Party₂ → Set
    p₁ relates-to p₂ = ∃ λ r → 
                        (party₁ r ≡ grain p₁) 
                         × 
                        (party₂ r ≡ grain p₂)

open IsNMRelation {{...}} public 

IsGraphEdge = IsNMRelation

------------------------------------------------------------------------    
-- Behavioral TypeClass Witness System
------------------------------------------------------------------------
-- This provides a way to tag types with their behavioral type class
-- and to query which behavioral type class a type belongs to

-- Simple tag version (for pattern matching / display)
data BehavioralTypeClassTag : Set₁ where
    Entity-Tag : BehavioralTypeClassTag
    Event-Tag : BehavioralTypeClassTag
    MultiVersion-Tag : BehavioralTypeClassTag
    SeqEvent-Tag : BehavioralTypeClassTag
    Snapshot-Tag : BehavioralTypeClassTag
    Ordered-Tag : BehavioralTypeClassTag
    SeqOrdered-Tag : BehavioralTypeClassTag
    NMRelation-Tag : BehavioralTypeClassTag
    NotClassified-Tag : BehavioralTypeClassTag

-- Behavioral TypeClass Witness
-- This sum type carries the ACTUAL type class instance, ensuring consistency
-- between the tag and the actual behavioral properties of a type
data BehavioralTypeClassWitness (R : Set) 
                                 {G EK : Set} 
                                 {g-def-rel : G IsGrainOf R}
                                 {ek-def-rel : EntityKey-def EK G R}
                                 {{is-data : IsData g-def-rel ek-def-rel}}
                                 : Set₂ where
    -- Each constructor requires the actual instance, ensuring tag consistency
    
    Entity-BTC : IsEntity R {G} {EK} {g-def-rel} {ek-def-rel}
               → BehavioralTypeClassWitness R
               
    Event-BTC : {Event-dtm : Set}
              → {event-dtm : R → Event-dtm}
              → IsEvent {R} {G} {EK} {g-def-rel} {ek-def-rel} {Event-dtm} event-dtm
              → BehavioralTypeClassWitness R
              
    MultiVersion-BTC : {From-dtm : Set}
                     → {from-dtm : R → From-dtm}
                     → {Payload : Set}
                     → {payload : R → Payload}
                     → IsMultiVersion {R} {G} {EK} {g-def-rel} {ek-def-rel} {From-dtm} from-dtm {Payload} payload
                     → BehavioralTypeClassWitness R
                     
    SeqEvent-BTC : {Event-dtm : Set}
                 → {event-dtm : R → Event-dtm}
                 → IsSeqEvent {R} {G} {EK} {g-def-rel} {ek-def-rel} {Event-dtm} event-dtm
                 → BehavioralTypeClassWitness R
                 
    Snapshot-BTC : {C : Set → Set}
                 → {{is-coll : IsDataColl C}}
                 → {Snapshot-dtm : Set}
                 → {S : Set}
                 → {snapshot-dtm : R → Snapshot-dtm}
                 → {snapshot : R → C S}
                 → IsSnapshot {R} {G} {EK} {C} {{is-coll}} {g-def-rel} {ek-def-rel} {Snapshot-dtm} {S} snapshot-dtm snapshot
                 → BehavioralTypeClassWitness R
                 
    Ordered-BTC : {OrdType : Set}
                → {ord-field : R → OrdType}
                → IsOrdered {R} {G} {EK} {g-def-rel} {ek-def-rel} {OrdType} ord-field
                → BehavioralTypeClassWitness R
                
    SeqOrdered-BTC : {OrdType : Set}
                   → {ord-field : R → OrdType}
                   → IsSeqOrdered {R} {G} {EK} {g-def-rel} {ek-def-rel} {OrdType} ord-field
                   → BehavioralTypeClassWitness R
                   
    NMRelation-BTC : {Party₁ Party₂ : Set}
                   → {G₁ EK₁ G₂ EK₂ : Set}
                   → {g-def-r₁-rel : G₁ IsGrainOf Party₁}
                   → {ek-def-r₁-rel : EntityKey-def EK₁ G₁ Party₁}
                   → {g-def-r₂-rel : G₂ IsGrainOf Party₂}
                   → {ek-def-r₂-rel : EntityKey-def EK₂ G₂ Party₂}
                   → {{is-data-party₁ : IsData g-def-r₁-rel ek-def-r₁-rel}}
                   → {{is-data-party₂ : IsData g-def-r₂-rel ek-def-r₂-rel}}
                   → {party₁ : R → G₁}
                   → {party₂ : R → G₂}
                   → IsNMRelation {R} {Party₁} {Party₂} party₁ party₂
                   → BehavioralTypeClassWitness R

    NotClassified-BTC : BehavioralTypeClassWitness R  -- No instance required

-- Extract just the tag from a witness
get-btc-tag : {R : Set} {G EK : Set} {g-def-rel : G IsGrainOf R}
            → {ek-def-rel : EntityKey-def EK G R}
            → {{is-data : IsData g-def-rel ek-def-rel}}
            → BehavioralTypeClassWitness R → BehavioralTypeClassTag
get-btc-tag (Entity-BTC _) = Entity-Tag
get-btc-tag (Event-BTC _) = Event-Tag
get-btc-tag (MultiVersion-BTC _) = MultiVersion-Tag
get-btc-tag (SeqEvent-BTC _) = SeqEvent-Tag
get-btc-tag (Snapshot-BTC _) = Snapshot-Tag
get-btc-tag (Ordered-BTC _) = Ordered-Tag
get-btc-tag (SeqOrdered-BTC _) = SeqOrdered-Tag
get-btc-tag (NMRelation-BTC _) = NMRelation-Tag
get-btc-tag NotClassified-BTC = NotClassified-Tag

-- Record that provides the behavioral type class witness for a type
-- This is what you implement as an instance to tag your types
record HasBehavioralTypeClass (R : Set) 
                               {G EK : Set} 
                               {g-def-rel : G IsGrainOf R}
                               {ek-def-rel : EntityKey-def EK G R}
                               {{is-data : IsData g-def-rel ek-def-rel}}
                               : Set₂ where
    field
        behavioral-witness : BehavioralTypeClassWitness R

open HasBehavioralTypeClass {{...}} public

-- BC-witness[R] — returns the full behavioral type class witness for R
BC-witness[_] : (R : Set) 
               → {G EK : Set} → {g-def-rel : G IsGrainOf R}
               → {ek-def-rel : EntityKey-def EK G R}
               → {{is-data : IsData g-def-rel ek-def-rel}} 
               → {{has-btc : HasBehavioralTypeClass R {G} {EK} {g-def-rel} {ek-def-rel}}}
               → BehavioralTypeClassWitness R
BC-witness[ R ] {{has-btc}} = behavioral-witness {{has-btc}}

-- BC[R] — behavioral-class operator (PDA.md I.2)
-- Returns the behavioral class tag for R via instance resolution
BC[_] : (R : Set) 
       → {G EK : Set} → {g-def-rel : G IsGrainOf R}
       → {ek-def-rel : EntityKey-def EK G R}
       → {{is-data : IsData g-def-rel ek-def-rel}} 
       → {{has-btc : HasBehavioralTypeClass R {G} {EK} {g-def-rel} {ek-def-rel}}}
       → BehavioralTypeClassTag
BC[ R ] {{has-btc}} = get-btc-tag (behavioral-witness {{has-btc}})

------------------------------------------------------------------------    
-- Usage Example
------------------------------------------------------------------------
module example-btc-witness where
    -- Example: A Customer type that is an Entity
    postulate
        CustomerId : Set
        CustomerName : Set
        
    record Customer : Set where
        field
            customer-id : CustomerId
            customer-name : CustomerName
    
    -- Define grain
    customer-grain : Customer → CustomerId
    customer-grain c = Customer.customer-id c
    
    postulate
        customer-grain-fg : CustomerId → Customer
        customer-grain-∘-fg≡id : customer-grain-fg ∘ customer-grain ≡ id
        customer-fg-∘-grain≡id : customer-grain ∘ customer-grain-fg ≡ id
        customer-grain-irreducible : IsIrreducibleGrain customer-grain
    
    customer-grain-def : CustomerId IsGrainOf Customer
    customer-grain-def = grain-def customer-grain customer-grain-fg 
                                   customer-grain-∘-fg≡id customer-fg-∘-grain≡id
                                   customer-grain-irreducible
    
    -- Define entity (Customer is its own entity type)
    customer-entity : Customer → Customer
    customer-entity = id
    
    postulate
        customer-entity-unique : ∀ {entity' : Customer → Customer} 
                               → IsSubjectOfInformation entity' 
                               → customer-entity ≡ entity'
    
    customer-entity-def : Customer IsEntityOf Customer
    customer-entity-def = entity-def customer-entity tt customer-entity-unique
    
    -- Define entity key grain (CustomerId is the grain of Customer)
    customer-ek-grain : Customer → CustomerId
    customer-ek-grain = customer-grain
    
    postulate
        customer-ek-grain-fg : CustomerId → Customer
        customer-ek-grain-∘-fg≡id : customer-ek-grain-fg ∘ customer-ek-grain ≡ id
        customer-ek-fg-∘-grain≡id : customer-ek-grain ∘ customer-ek-grain-fg ≡ id
        customer-ek-grain-irreducible : IsIrreducibleGrain customer-ek-grain
    
    customer-ek-grain-def : CustomerId IsGrainOf Customer
    customer-ek-grain-def = grain-def customer-ek-grain customer-ek-grain-fg 
                                          customer-ek-grain-∘-fg≡id customer-ek-fg-∘-grain≡id
                                          customer-ek-grain-irreducible
    
    -- Define entity key definition
    customer-entity-key-def : EntityKey-def CustomerId CustomerId Customer
    customer-entity-key-def = entitykey-def customer-grain-def 
                                             customer-entity-def 
                                             customer-ek-grain-def 
                                             id 
                                             (λ ek → ek , refl)
    
    -- Define IsData instance
    instance
        customer-is-data : IsData customer-grain-def customer-entity-key-def
        Constraints {{customer-is-data}} = cons-true
    
    -- Define the actual IsEntity instance
    instance
        customer-is-entity : IsEntity Customer {CustomerId} {CustomerId} {customer-grain-def} {customer-entity-key-def}
        grain-cond {{customer-is-entity}} = refl
    
    -- Create witness with the ACTUAL IsEntity instance
    -- This ensures Customer is REALLY an Entity (type-checked!)
    instance
        customer-has-btc : HasBehavioralTypeClass Customer
        behavioral-witness {{customer-has-btc}} = Entity-BTC customer-is-entity
    
    -- Now we can query the behavioral type class tag
    _ : BC[ Customer ] ≡ Entity-Tag
    _ = refl
    
    -- And we can get the full witness (which includes the IsEntity instance)
    _ : BC-witness[ Customer ] ≡ Entity-BTC customer-is-entity
    _ = refl
    
    -- Example: An Order type that is an Event
    postulate
        OrderId : Set
        OrderDate : Set
        default-order-date : OrderDate
        _≤-orderdate_ : Rel OrderDate 0ℓ
        orderdate-total-ord : TotalOrd _≤-orderdate_
        
    record Order : Set where
        field
            order-id : OrderId
            order-date : OrderDate
    
    order-grain : Order → (OrderId × OrderDate)
    order-grain o = (Order.order-id o , Order.order-date o)
    
    postulate
        order-grain-fg : (OrderId × OrderDate) → Order
        order-grain-∘-fg≡id : order-grain-fg ∘ order-grain ≡ id
        order-fg-∘-grain≡id : order-grain ∘ order-grain-fg ≡ id
        order-grain-irreducible : IsIrreducibleGrain order-grain
    
    order-grain-def : (OrderId × OrderDate) IsGrainOf Order
    order-grain-def = grain-def order-grain order-grain-fg 
                                order-grain-∘-fg≡id order-fg-∘-grain≡id
                                order-grain-irreducible
    
    -- Define entity (Order is its own entity type)
    order-entity : Order → Order
    order-entity = id
    
    postulate
        order-entity-unique : ∀ {entity' : Order → Order} 
                            → IsSubjectOfInformation entity' 
                            → order-entity ≡ entity'
    
    order-entity-def : Order IsEntityOf Order
    order-entity-def = entity-def order-entity tt order-entity-unique
    
    -- Define entity key grain (OrderId is the grain of Order)
    order-ek-grain : Order → OrderId
    order-ek-grain o = Order.order-id o
    
    postulate
        order-ek-grain-fg : OrderId → Order
        order-ek-grain-∘-fg≡id : order-ek-grain-fg ∘ order-ek-grain ≡ id
        order-ek-fg-∘-grain≡id : order-ek-grain ∘ order-ek-grain-fg ≡ id
        order-ek-grain-irreducible : IsIrreducibleGrain order-ek-grain
    
    order-ek-grain-def : OrderId IsGrainOf Order
    order-ek-grain-def = grain-def order-ek-grain order-ek-grain-fg 
                                       order-ek-grain-∘-fg≡id order-ek-fg-∘-grain≡id
                                       order-ek-grain-irreducible
    
    -- Define entity key definition
    -- EK = OrderId, G = OrderId × OrderDate, R = Order
    order-entity-key-def : EntityKey-def OrderId (OrderId × OrderDate) Order
    order-entity-key-def = entitykey-def order-grain-def 
                                         order-entity-def 
                                         order-ek-grain-def 
                                         proj₁ 
                                         (λ ek → (ek , default-order-date) , refl)
    
    instance
        order-is-data : IsData order-grain-def order-entity-key-def
        Constraints {{order-is-data}} = cons-true
    
    -- Define the actual IsEvent instance
    instance
        order-is-event : IsEvent {Order} {OrderId × OrderDate} {OrderId} {order-grain-def} {order-entity-key-def}
                                 {OrderDate} (λ o → Order.order-date o)
        _<to=_ {{order-is-event}} = _≤-orderdate_
        tot-ordering {{order-is-event}} = orderdate-total-ord
        grain-cond {{order-is-event}} = refl
    
    -- Create witness with the ACTUAL IsEvent instance
    instance
        order-has-btc : HasBehavioralTypeClass Order
        behavioral-witness {{order-has-btc}} = Event-BTC order-is-event
    
    -- Query the behavioral type class tag
    _ : BC[ Order ] ≡ Event-Tag
    _ = refl