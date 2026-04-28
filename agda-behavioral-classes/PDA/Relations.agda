module PDA.Relations where

open import PDA.Collections public

------------------------------------------------------------------------
-- §II.4 Collection Relations
------------------------------------------------------------------------

-- All 9 collection relations from PDD.md §II.4.
-- Relations are parameterized over the collection type C and
-- element types R₁, R₂ with their grain/EK structure.

------------------------------------------------------------------------
-- §II.4 Equality Relations
------------------------------------------------------------------------

-- =c : Collection equality (same elements, both-way containment)
-- c₁ =c c₂ ≡ (∀ e₁ ∈ c₁. ∃ e₂ ∈ c₂. e₁ = e₂) ∧ (∀ e₂ ∈ c₂. ∃ e₁ ∈ c₁. e₂ = e₁)
_=c_ : {C : Set → Set} {R G EK : Set}
     → {g-def-rel : G IsGrainOf R}
     → {ek-def-rel : EntityKey-def EK G R}
     → {{is-data : IsData g-def-rel ek-def-rel}}
     → {{is-data-coll : IsDataColl C}}
     → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
     → Rel (C R) 0ℓ
_=c_ {C} {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {{is-data-coll}} {_≟_} c₁ c₂ =
    (∀ (e₁ : R) → (_∈coll_) {_≟_ = _≟_} e₁ c₁
                 → ∃ λ (e₂ : R) → (_∈coll_) {_≟_ = _≟_} e₂ c₂ × e₁ ≡ e₂)
    ×
    (∀ (e₂ : R) → (_∈coll_) {_≟_ = _≟_} e₂ c₂
                 → ∃ λ (e₁ : R) → (_∈coll_) {_≟_ = _≟_} e₁ c₁ × e₂ ≡ e₁)

-- =g-coll : Grain equality (isomorphic sets via grain)
-- c₁ and c₂ are grain-equal iff their grain types are grain-equivalent
-- and there is a bijection on elements respecting the grain isomorphism.
-- Note: "=g-coll" distinguishes from type-level _≡g_ in GrainTheory.Relations.
-- Requires: GetG c₁ ≡g GetG c₂ (type-level grain equivalence)
-- and element-level grain correspondence via the isomorphism f.
_=g-coll_ : {C : Set → Set}
           → {R₁ R₂ : Set}
           → {G₁ G₂ EK₁ EK₂ : Set}
           → {g-def-rel₁ : G₁ IsGrainOf R₁}
           → {ek-def-rel₁ : EntityKey-def EK₁ G₁ R₁}
           → {g-def-rel₂ : G₂ IsGrainOf R₂}
           → {ek-def-rel₂ : EntityKey-def EK₂ G₂ R₂}
           → {{is-data₁ : IsData g-def-rel₁ ek-def-rel₁}}
           → {{is-data₂ : IsData g-def-rel₂ ek-def-rel₂}}
           → {{is-data-coll : IsDataColl C}}
           → {_≟₁_ : (g₁ g₂ : G₁) → Dec (g₁ ≡ g₂)}
           → {_≟₂_ : (g₁ g₂ : G₂) → Dec (g₁ ≡ g₂)}
           → REL (C R₁) (C R₂) 0ℓ
_=g-coll_ {C} {R₁} {R₂} {G₁} {G₂} {EK₁} {EK₂}
          {g-def-rel₁} {ek-def-rel₁} {g-def-rel₂} {ek-def-rel₂}
          {{is-data₁}} {{is-data₂}} {{is-data-coll}}
          {_≟₁_} {_≟₂_} c₁ c₂ =
    -- There exists a bijection f : G₁ → G₂ such that
    -- elements correspond via grain
    ∃ λ (f : G₁ → G₂) →
    ∃ λ (f⁻¹ : G₂ → G₁) →
        -- f is an isomorphism
        (∀ (g : G₁) → f⁻¹ (f g) ≡ g)
      × (∀ (g : G₂) → f (f⁻¹ g) ≡ g)
        -- forward: every element in c₁ has a grain-corresponding element in c₂
      × (∀ (e₁ : R₁) → (_∈coll_) {_≟_ = _≟₁_} e₁ c₁
                       → ∃ λ (e₂ : R₂) → (_∈coll_) {_≟_ = _≟₂_} e₂ c₂
                           × f (grain {{is-data₁}} e₁) ≡ grain {{is-data₂}} e₂)
        -- backward: every element in c₂ has a grain-corresponding element in c₁
      × (∀ (e₂ : R₂) → (_∈coll_) {_≟_ = _≟₂_} e₂ c₂
                       → ∃ λ (e₁ : R₁) → (_∈coll_) {_≟_ = _≟₁_} e₁ c₁
                           × grain {{is-data₁}} e₁ ≡ f⁻¹ (grain {{is-data₂}} e₂))

-- =ek : Entity-key equality
-- c₁ =ek c₂ ≡ sel-ek c₁ =g-coll sel-ek c₂
-- Since sel-ek (a PDA operation) is not yet available (AT-040R),
-- this is stated abstractly in terms of entity-key projections.
_=ek_ : {C : Set → Set}
      → {R₁ R₂ : Set}
      → {G₁ G₂ EK₁ EK₂ : Set}
      → {g-def-rel₁ : G₁ IsGrainOf R₁}
      → {ek-def-rel₁ : EntityKey-def EK₁ G₁ R₁}
      → {g-def-rel₂ : G₂ IsGrainOf R₂}
      → {ek-def-rel₂ : EntityKey-def EK₂ G₂ R₂}
      → {{is-data₁ : IsData g-def-rel₁ ek-def-rel₁}}
      → {{is-data₂ : IsData g-def-rel₂ ek-def-rel₂}}
      → {{is-data-coll : IsDataColl C}}
      → {_≟g₁_ : (g₁ g₂ : G₁) → Dec (g₁ ≡ g₂)}
      → {_≟g₂_ : (g₁ g₂ : G₂) → Dec (g₁ ≡ g₂)}
      → REL (C R₁) (C R₂) 0ℓ
_=ek_ {C} {R₁} {R₂} {G₁} {G₂} {EK₁} {EK₂}
      {g-def-rel₁} {ek-def-rel₁} {g-def-rel₂} {ek-def-rel₂}
      {{is-data₁}} {{is-data₂}} {{is-data-coll}}
      {_≟g₁_} {_≟g₂_} c₁ c₂ =
    -- Bijection on entity keys (analogous to =g-coll but on EK instead of G)
    ∃ λ (f : EK₁ → EK₂) →
    ∃ λ (f⁻¹ : EK₂ → EK₁) →
        (∀ (ek : EK₁) → f⁻¹ (f ek) ≡ ek)
      × (∀ (ek : EK₂) → f (f⁻¹ ek) ≡ ek)
      × (∀ (e₁ : R₁) → (_∈coll_) {_≟_ = _≟g₁_} e₁ c₁
                       → ∃ λ (e₂ : R₂) → (_∈coll_) {_≟_ = _≟g₂_} e₂ c₂
                           × f (entity-key {{is-data₁}} e₁) ≡ entity-key {{is-data₂}} e₂)
      × (∀ (e₂ : R₂) → (_∈coll_) {_≟_ = _≟g₂_} e₂ c₂
                       → ∃ λ (e₁ : R₁) → (_∈coll_) {_≟_ = _≟g₁_} e₁ c₁
                           × entity-key {{is-data₁}} e₁ ≡ f⁻¹ (entity-key {{is-data₂}} e₂))

-- =# : Cardinality equality
-- c₁ =# c₂ ≡ # c₁ = # c₂
_=#_ : {C : Set → Set} {R₁ R₂ : Set}
     → {{is-data-coll : IsDataColl C}}
     → REL (C R₁) (C R₂) 0ℓ
_=#_ c₁ c₂ = # c₁ ≡ # c₂

------------------------------------------------------------------------
-- §II.4 Subset Relations
------------------------------------------------------------------------

-- ⊆c : Collection subset — every element of c₁ is in c₂
-- ∀ e₁ ∈ c₁. ∃ e₂ ∈ c₂. e₁ = e₂
_⊆c_ : {C : Set → Set} {R G EK : Set}
     → {g-def-rel : G IsGrainOf R}
     → {ek-def-rel : EntityKey-def EK G R}
     → {{is-data : IsData g-def-rel ek-def-rel}}
     → {{is-data-coll : IsDataColl C}}
     → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
     → Rel (C R) 0ℓ
_⊆c_ {C} {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {{is-data-coll}} {_≟_} c₁ c₂ =
    ∀ (e₁ : R) → (_∈coll_) {_≟_ = _≟_} e₁ c₁
               → ∃ λ (e₂ : R) → (_∈coll_) {_≟_ = _≟_} e₂ c₂ × e₁ ≡ e₂

-- ⊂c : Collection proper subset
-- c₁ ⊂c c₂ ≡ c₁ ⊆c c₂ ∧ ¬(c₂ ⊆c c₁)
_⊂c_ : {C : Set → Set} {R G EK : Set}
     → {g-def-rel : G IsGrainOf R}
     → {ek-def-rel : EntityKey-def EK G R}
     → {{is-data : IsData g-def-rel ek-def-rel}}
     → {{is-data-coll : IsDataColl C}}
     → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
     → Rel (C R) 0ℓ
_⊂c_ {C} {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {{is-data-coll}} {_≟_} c₁ c₂ =
    (_⊆c_) {_≟_ = _≟_} c₁ c₂
    × ¬ ((_⊆c_) {_≟_ = _≟_} c₂ c₁)

-- ⊆g : Grain specialization
-- c₁ ⊆g c₂ ≡ ∃ P : GetT c₂ → Set. filter P c₂ =g-coll c₁
-- Since filter (a PDA operation) is not yet available (AT-040R),
-- we define this abstractly: c₁ is a specialization of c₂ iff
-- there exists a grain-preserving injection from c₁ into c₂.
_⊆g_ : {C : Set → Set}
      → {R₁ R₂ : Set}
      → {G₁ G₂ EK₁ EK₂ : Set}
      → {g-def-rel₁ : G₁ IsGrainOf R₁}
      → {ek-def-rel₁ : EntityKey-def EK₁ G₁ R₁}
      → {g-def-rel₂ : G₂ IsGrainOf R₂}
      → {ek-def-rel₂ : EntityKey-def EK₂ G₂ R₂}
      → {{is-data₁ : IsData g-def-rel₁ ek-def-rel₁}}
      → {{is-data₂ : IsData g-def-rel₂ ek-def-rel₂}}
      → {{is-data-coll : IsDataColl C}}
      → {_≟₁_ : (g₁ g₂ : G₁) → Dec (g₁ ≡ g₂)}
      → {_≟₂_ : (g₁ g₂ : G₂) → Dec (g₁ ≡ g₂)}
      → REL (C R₁) (C R₂) 0ℓ
_⊆g_ {C} {R₁} {R₂} {G₁} {G₂} {EK₁} {EK₂}
     {g-def-rel₁} {ek-def-rel₁} {g-def-rel₂} {ek-def-rel₂}
     {{is-data₁}} {{is-data₂}} {{is-data-coll}}
     {_≟₁_} {_≟₂_} c₁ c₂ =
    -- PDD.md: ∃ P : (GetT c₂) → Set. filter P c₂ =g-coll c₁
    -- Equivalent: there exists a grain isomorphism f : G₁ → G₂ and
    -- every grain in c₁ maps (via f) to a grain present in c₂
    ∃ λ (f : G₁ → G₂) →
    ∃ λ (f⁻¹ : G₂ → G₁) →
        (∀ (g : G₁) → f⁻¹ (f g) ≡ g)
      × (∀ (g : G₂) → f (f⁻¹ g) ≡ g)
      × (∀ (e₁ : R₁) → (_∈coll_) {_≟_ = _≟₁_} e₁ c₁
                       → ∃ λ (e₂ : R₂) → (_∈coll_) {_≟_ = _≟₂_} e₂ c₂
                           × f (grain {{is-data₁}} e₁) ≡ grain {{is-data₂}} e₂)

-- ⊆ek : Entity-key specialization
-- c₁ ⊆ek c₂ ≡ ∃ P : (GetT c₂) → Set. filter P c₂ =ek c₁
-- Analogous to ⊆g but using entity-key correspondence.
_⊆ek_ : {C : Set → Set}
       → {R₁ R₂ : Set}
       → {G₁ G₂ EK₁ EK₂ : Set}
       → {g-def-rel₁ : G₁ IsGrainOf R₁}
       → {ek-def-rel₁ : EntityKey-def EK₁ G₁ R₁}
       → {g-def-rel₂ : G₂ IsGrainOf R₂}
       → {ek-def-rel₂ : EntityKey-def EK₂ G₂ R₂}
       → {{is-data₁ : IsData g-def-rel₁ ek-def-rel₁}}
       → {{is-data₂ : IsData g-def-rel₂ ek-def-rel₂}}
       → {{is-data-coll : IsDataColl C}}
       → {_≟g₁_ : (g₁ g₂ : G₁) → Dec (g₁ ≡ g₂)}
       → {_≟g₂_ : (g₁ g₂ : G₂) → Dec (g₁ ≡ g₂)}
       → REL (C R₁) (C R₂) 0ℓ
_⊆ek_ {C} {R₁} {R₂} {G₁} {G₂} {EK₁} {EK₂}
      {g-def-rel₁} {ek-def-rel₁} {g-def-rel₂} {ek-def-rel₂}
      {{is-data₁}} {{is-data₂}} {{is-data-coll}}
      {_≟g₁_} {_≟g₂_} c₁ c₂ =
    ∃ λ (f : EK₁ → EK₂) →
    ∃ λ (f⁻¹ : EK₂ → EK₁) →
        (∀ (ek : EK₁) → f⁻¹ (f ek) ≡ ek)
      × (∀ (ek : EK₂) → f (f⁻¹ ek) ≡ ek)
      × (∀ (e₁ : R₁) → (_∈coll_) {_≟_ = _≟g₁_} e₁ c₁
                       → ∃ λ (e₂ : R₂) → (_∈coll_) {_≟_ = _≟g₂_} e₂ c₂
                           × f (entity-key {{is-data₁}} e₁) ≡ entity-key {{is-data₂}} e₂)

------------------------------------------------------------------------
-- §II.4 Generalization
------------------------------------------------------------------------

-- ⊇g : Grain generalization (n-ary, partition constraint)
-- c ⊇g {c₁, …, cₙ} ≡ (c₁ ⊆g c ∧ … ∧ cₙ ⊆g c) ∧ (#c₁ + … + #cₙ = #c)
-- For the binary case (n=1), this is just ⊆g with cardinality equality.
-- The n-ary case uses a list of collections.
_⊇g_ : {C : Set → Set}
      → {R₁ R₂ : Set}
      → {G₁ G₂ EK₁ EK₂ : Set}
      → {g-def-rel₁ : G₁ IsGrainOf R₁}
      → {ek-def-rel₁ : EntityKey-def EK₁ G₁ R₁}
      → {g-def-rel₂ : G₂ IsGrainOf R₂}
      → {ek-def-rel₂ : EntityKey-def EK₂ G₂ R₂}
      → {{is-data₁ : IsData g-def-rel₁ ek-def-rel₁}}
      → {{is-data₂ : IsData g-def-rel₂ ek-def-rel₂}}
      → {{is-data-coll : IsDataColl C}}
      → {_≟₁_ : (g₁ g₂ : G₁) → Dec (g₁ ≡ g₂)}
      → {_≟₂_ : (g₁ g₂ : G₂) → Dec (g₁ ≡ g₂)}
      → C R₁ → List (C R₂) → Set
_⊇g_ {C} {R₁} {R₂} {G₁} {G₂} {EK₁} {EK₂}
     {g-def-rel₁} {ek-def-rel₁} {g-def-rel₂} {ek-def-rel₂}
     {{is-data₁}} {{is-data₂}} {{is-data-coll}}
     {_≟₁_} {_≟₂_} c parts =
    -- All parts are specializations of c (foldr-based conjunction)
    foldr-list (λ cᵢ acc → (_⊆g_) {_≟₁_ = _≟₂_} {_≟₂_ = _≟₁_} cᵢ c × acc) ⊤ parts
    ×
    -- Partition constraint: cardinalities sum to the whole
    (foldl-list (λ acc cᵢ → acc + # cᵢ) 0 parts ≡ # c)

------------------------------------------------------------------------
-- §II.4 Implication Hierarchies
------------------------------------------------------------------------

-- =c ⟹ =g ⟹ =ek (stronger equality implies weaker)
postulate
    =c⇒=g : {C : Set → Set} {R G EK : Set}
           → {g-def-rel : G IsGrainOf R}
           → {ek-def-rel : EntityKey-def EK G R}
           → {{is-data : IsData g-def-rel ek-def-rel}}
           → {{is-data-coll : IsDataColl C}}
           → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
           → {_≟ek_ : (ek₁ ek₂ : EK) → Dec (ek₁ ≡ ek₂)}
           → {c₁ c₂ : C R}
           → (_=c_) {_≟_ = _≟_} c₁ c₂
           → (_=g-coll_) {_≟₁_ = _≟_} {_≟₂_ = _≟_} c₁ c₂

    =g⇒=ek : {C : Set → Set} {R₁ R₂ : Set}
            → {G₁ G₂ EK₁ EK₂ : Set}
            → {g-def-rel₁ : G₁ IsGrainOf R₁}
            → {ek-def-rel₁ : EntityKey-def EK₁ G₁ R₁}
            → {g-def-rel₂ : G₂ IsGrainOf R₂}
            → {ek-def-rel₂ : EntityKey-def EK₂ G₂ R₂}
            → {{is-data₁ : IsData g-def-rel₁ ek-def-rel₁}}
            → {{is-data₂ : IsData g-def-rel₂ ek-def-rel₂}}
            → {{is-data-coll : IsDataColl C}}
            → {_≟₁_ : (g₁ g₂ : G₁) → Dec (g₁ ≡ g₂)}
            → {_≟₂_ : (g₁ g₂ : G₂) → Dec (g₁ ≡ g₂)}
            → {c₁ : C R₁} → {c₂ : C R₂}
            → (_=g-coll_) {_≟₁_ = _≟₁_} {_≟₂_ = _≟₂_} c₁ c₂
            → (_=ek_) {_≟g₁_ = _≟₁_} {_≟g₂_ = _≟₂_} c₁ c₂

-- ⊆c ⟹ ⊆g ⟹ ⊆ek (stronger subset implies weaker)
postulate
    ⊆c⇒⊆g : {C : Set → Set} {R G EK : Set}
           → {g-def-rel : G IsGrainOf R}
           → {ek-def-rel : EntityKey-def EK G R}
           → {{is-data : IsData g-def-rel ek-def-rel}}
           → {{is-data-coll : IsDataColl C}}
           → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
           → {c₁ c₂ : C R}
           → (_⊆c_) {_≟_ = _≟_} c₁ c₂
           → (_⊆g_) {_≟₁_ = _≟_} {_≟₂_ = _≟_} c₁ c₂

    ⊆g⇒⊆ek : {C : Set → Set} {R₁ R₂ : Set}
            → {G₁ G₂ EK₁ EK₂ : Set}
            → {g-def-rel₁ : G₁ IsGrainOf R₁}
            → {ek-def-rel₁ : EntityKey-def EK₁ G₁ R₁}
            → {g-def-rel₂ : G₂ IsGrainOf R₂}
            → {ek-def-rel₂ : EntityKey-def EK₂ G₂ R₂}
            → {{is-data₁ : IsData g-def-rel₁ ek-def-rel₁}}
            → {{is-data₂ : IsData g-def-rel₂ ek-def-rel₂}}
            → {{is-data-coll : IsDataColl C}}
            → {_≟₁_ : (g₁ g₂ : G₁) → Dec (g₁ ≡ g₂)}
            → {_≟₂_ : (g₁ g₂ : G₂) → Dec (g₁ ≡ g₂)}
            → {c₁ : C R₁} → {c₂ : C R₂}
            → (_⊆g_) {_≟₁_ = _≟₁_} {_≟₂_ = _≟₂_} c₁ c₂
            → (_⊆ek_) {_≟g₁_ = _≟₁_} {_≟g₂_ = _≟₂_} c₁ c₂

------------------------------------------------------------------------
-- §II.4 Constraints
------------------------------------------------------------------------

-- Element constraint: P : R → Set, must hold for every element
ElementConstraint : {C : Set → Set} {R G EK : Set}
                  → {g-def-rel : G IsGrainOf R}
                  → {ek-def-rel : EntityKey-def EK G R}
                  → {{is-data : IsData g-def-rel ek-def-rel}}
                  → {{is-data-coll : IsDataColl C}}
                  → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                  → (R → Set) → C R → Set
ElementConstraint {R = R} {_≟_ = _≟_} P c =
    ∀ (r : R) → (_∈coll_) {_≟_ = _≟_} r c → P r

-- Collection constraint: a predicate over a single collection
CollectionConstraint : {C : Set → Set} {R : Set}
                     → (C R → Set) → C R → Set
CollectionConstraint P c = P c

-- Cross-collection constraint: a predicate relating two collections
CrossCollectionConstraint : {C : Set → Set} {R₁ R₂ : Set}
                          → (C R₁ → C R₂ → Set) → C R₁ → C R₂ → Set
CrossCollectionConstraint P c₁ c₂ = P c₁ c₂

------------------------------------------------------------------------
-- §II.4 Key Predicates
------------------------------------------------------------------------

-- Superkey: a projection that uniquely identifies elements
_IsSuperKeyOf_ : {C : Set → Set} {R G EK Key : Set}
               → {g-def-rel : G IsGrainOf R}
               → {ek-def-rel : EntityKey-def EK G R}
               → {{is-data : IsData g-def-rel ek-def-rel}}
               → {{is-data-coll : IsDataColl C}}
               → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
               → REL (Fields Key of R) (C R) 0ℓ
_IsSuperKeyOf_ {C} {R} {G} {EK} {Key} {g-def-rel} {ek-def-rel} {{is-data}} {{is-data-coll}} {_≟_} key coll =
    ∀ {r₁ r₂ : R}
    → (_∈coll_) {C} {R} {{is-data}} {_≟_} r₁ coll
    → (_∈coll_) {C} {R} {{is-data}} {_≟_} r₂ coll
    → (key r₁) ≡ (key r₂)
    → r₁ ≡ r₂

-- Key: a superkey that is also irreducible (no proper subset is a superkey)
_IsKeyOf_ : {C : Set → Set} {R G EK Key : Set}
          → {g-def-rel : G IsGrainOf R}
          → {ek-def-rel : EntityKey-def EK G R}
          → {{is-data : IsData g-def-rel ek-def-rel}}
          → {{is-data-coll : IsDataColl C}}
          → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
          → REL (Fields Key of R) (C R) (suc 0ℓ)
_IsKeyOf_ {C} {R} {G} {EK} {Key}
          {g-def-rel}
          {ek-def-rel}
          {{is-data}}
          {{is-data-coll}}
          {_≟_}
          key coll =
    (_IsSuperKeyOf_) {_≟_ = _≟_} key coll
    ×
    ∄ λ (Keyₛ : Set) → ∃ λ (keyₛ : Fields Keyₛ of R) → (_⊂fld_ {Keyₛ} {Key} {R} keyₛ key) × ((_IsSuperKeyOf_) {_≟_ = _≟_} keyₛ coll)
