module PDA.Collections where

open import GrainTheory.Relations public

------------------------------------------------------------------------
-- §II.1 Data Collection
------------------------------------------------------------------------

record IsDataColl (C : Set → Set) : Set₁ where
    field
        {{coll-is-functor}}     : RawFunctor C
        {{coll-is-applicative}} : RawApplicative C

        ------------------------------------------------------------
        -- §II.2.1 Primitives
        ------------------------------------------------------------
        empty-coll : {R : Set} → C R

        insert-coll : {R : Set} → R → C R → C R

        delete-coll : {R : Set} → R → C R → C R

        -- Right fold (catamorphism) — the primitive from which all
        -- derived operations can be constructed
        foldr : {R : Set} → {Acc : Set} → (R → Acc → Acc) → Acc → C R → Acc

        -- Derivable from foldr but kept primitive for efficiency
        -- (tail-recursive, constant stack space in strict evaluation)
        foldl : {R : Set} → {Acc : Set} → (Acc → R → Acc) → Acc → C R → Acc

        -- Derivable as: map f = foldr (insert-coll ∘ f) empty-coll
        -- Kept primitive for efficiency and RawFunctor alignment
        map : {R' : Set} → {R : Set} → (R → R') → C R → C R'

        -- Bulk construction: fromList = foldr insert-coll empty-coll
        fromList : {R : Set} → List R → C R

        -- Bulk observation: toList = foldr (_∷_) []
        toList : {R : Set} → C R → List R

    ------------------------------------------------------------
    -- §II.2.1 Derived Operations
    ------------------------------------------------------------

    -- Cardinality: # c = |{ r | r ∈ c }|
    #_ : {R : Set} → C R → Nat
    # coll = foldr (λ _ acc → acc + 1) 0 coll

    -- Grain lookup: find element by grain value
    grain-lookup : {R G EK : Set}
            → {g-def-rel : G IsGrainOf R}
            → {ek-def-rel : EntityKey-def EK G R}
            → {{is-data : IsData g-def-rel ek-def-rel}}
            → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
            → Grain → C R → Maybe R
    grain-lookup {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} target-grain coll =
        foldl (λ acc r →
            case acc of λ where
                (just r') → just r'
                nothing →
                    let current-grain = grain {{is-data}} r
                    in if decToBool (current-grain ≟ target-grain)
                       then just r
                       else nothing
        ) nothing coll

    -- Grain-based membership: r ∈_coll c iff grain-lookup (grain r) c ≡ just r
    _∈coll_ : {R G EK : Set}
            → {g-def-rel : G IsGrainOf R}
            → {ek-def-rel : EntityKey-def EK G R}
            → {{is-data : IsData g-def-rel ek-def-rel}}
            → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
            → REL R (C R) 0ℓ
    _∈coll_ {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} r coll =
        grain-lookup {_≟_ = _≟_} (grain r) coll ≡ just r
    infix 4 _∈coll_

    -- Grain-based union: c₁ ∪_coll c₂ = foldr insert-coll c₂ c₁
    _∪coll_ : {R : Set} → C R → C R → C R
    coll₁ ∪coll coll₂ = foldr insert-coll coll₂ coll₁
    infixl 6 _∪coll_

    -- Grain-based intersection
    _∩coll_ : {R G EK : Set}
            → {g-def-rel : G IsGrainOf R}
            → {ek-def-rel : EntityKey-def EK G R}
            → {{is-data : IsData g-def-rel ek-def-rel}}
            → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
            → C R → C R → C R
    _∩coll_ {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} coll₁ coll₂ =
        foldr (λ r acc →
            case grain-lookup {_≟_ = _≟_} (grain {{is-data}} r) coll₂ of λ where
                (just _) → insert-coll r acc
                nothing → acc
        ) empty-coll coll₁
    infixl 7 _∩coll_

    -- Grain-based difference
    _-coll_ : {R G EK : Set}
            → {g-def-rel : G IsGrainOf R}
            → {ek-def-rel : EntityKey-def EK G R}
            → {{is-data : IsData g-def-rel ek-def-rel}}
            → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
            → C R → C R → C R
    _-coll_ {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} coll₁ coll₂ =
        foldr (λ r acc →
            case grain-lookup {_≟_ = _≟_} (grain {{is-data}} r) coll₂ of λ where
                (just _) → acc
                nothing → insert-coll r acc
        ) empty-coll coll₁
    infixl 6 _-coll_

    ------------------------------------------------------------
    -- §II.1 Axiom 0 (empty collection)
    -- ∀ r. grain-lookup (grain r) empty-coll = nothing
    ------------------------------------------------------------
    Axiom-0 : {R G EK : Set}
            → {g-def-rel : G IsGrainOf R}
            → {ek-def-rel : EntityKey-def EK G R}
            → {{is-data : IsData g-def-rel ek-def-rel}}
            → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
            → Set
    Axiom-0 {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} =
        ∀ (r : R) → grain-lookup {_≟_ = _≟_} (grain r) empty-coll ≡ nothing

    ------------------------------------------------------------
    -- §II.1 Axiom 1 (grain-unique insertion)
    ------------------------------------------------------------

    -- Progress: collection grows when grain is absent
    Axiom-1-progress : {R G EK : Set}
                     → {g-def-rel : G IsGrainOf R}
                     → {ek-def-rel : EntityKey-def EK G R}
                     → {{is-data : IsData g-def-rel ek-def-rel}}
                     → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                     → Set
    Axiom-1-progress {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} =
        ∀ (r : R) → (coll : C R)
        → grain-lookup {_≟_ = _≟_} (grain r) coll ≡ nothing
        → # (insert-coll r coll) ≡ (# coll) + 1

    -- Safety: no-op when grain is already present
    Axiom-1-safety : {R G EK : Set}
                   → {g-def-rel : G IsGrainOf R}
                   → {ek-def-rel : EntityKey-def EK G R}
                   → {{is-data : IsData g-def-rel ek-def-rel}}
                   → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                   → Set
    Axiom-1-safety {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} =
        ∀ (r : R) → (coll : C R)
        → grain-lookup {_≟_ = _≟_} (grain r) coll ≢ nothing
        → insert-coll r coll ≡ coll

    ------------------------------------------------------------
    -- §II.1 Grain-uniqueness Theorem
    -- ∀ r₁, r₂ ∈ c. grain r₁ = grain r₂ → r₁ = r₂
    ------------------------------------------------------------
    Grain-uniqueness : {R G EK : Set}
                     → {g-def-rel : G IsGrainOf R}
                     → {ek-def-rel : EntityKey-def EK G R}
                     → {{is-data : IsData g-def-rel ek-def-rel}}
                     → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                     → Set
    Grain-uniqueness {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} =
        ∀ (r₁ r₂ : R) → (coll : C R)
        → (_∈coll_) {_≟_ = _≟_} r₁ coll
        → (_∈coll_) {_≟_ = _≟_} r₂ coll
        → grain {{is-data}} r₁ ≡ grain {{is-data}} r₂
        → r₁ ≡ r₂

    -- Corollary (element uniqueness): no element appears more than once.
    -- Follows from grain-uniqueness since grain is a function:
    -- r₁ = r₂ implies grain r₁ = grain r₂, so by grain-uniqueness
    -- they are the same occurrence.
    Element-uniqueness : {R G EK : Set}
                       → {g-def-rel : G IsGrainOf R}
                       → {ek-def-rel : EntityKey-def EK G R}
                       → {{is-data : IsData g-def-rel ek-def-rel}}
                       → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                       → Set
    Element-uniqueness {_≟_ = _≟_} = Grain-uniqueness {_≟_ = _≟_}

    ------------------------------------------------------------
    -- §II.2.1 Insert Invariant
    ------------------------------------------------------------

    -- 1. Retrievability: an inserted element can always be retrieved
    -- ∀ r, c. ∃ r'. grain-lookup (grain r) (insert-coll r c) = just r'
    Insert-retrievability : {R G EK : Set}
                          → {g-def-rel : G IsGrainOf R}
                          → {ek-def-rel : EntityKey-def EK G R}
                          → {{is-data : IsData g-def-rel ek-def-rel}}
                          → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                          → Set
    Insert-retrievability {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} =
        ∀ (r : R) → (coll : C R)
        → ∃ λ (r' : R) → grain-lookup {_≟_ = _≟_} (grain r) (insert-coll r coll) ≡ just r'

    -- 2. Idempotency: consecutive same-grain inserts collapse
    -- ∀ r, r', c. grain r' = grain r → insert-coll r' (insert-coll r c) = insert-coll r c
    Insert-idempotency : {R G EK : Set}
                        → {g-def-rel : G IsGrainOf R}
                        → {ek-def-rel : EntityKey-def EK G R}
                        → {{is-data : IsData g-def-rel ek-def-rel}}
                        → Set
    Insert-idempotency {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} =
        ∀ (r r' : R) → (coll : C R)
        → grain {{is-data}} r' ≡ grain {{is-data}} r
        → insert-coll r' (insert-coll r coll) ≡ insert-coll r coll

    -- 3. Commutativity: different-grain inserts commute
    -- ∀ r, r', c. grain r' ≠ grain r → insert-coll r' (insert-coll r c) = insert-coll r (insert-coll r' c)
    Insert-commutativity : {R G EK : Set}
                         → {g-def-rel : G IsGrainOf R}
                         → {ek-def-rel : EntityKey-def EK G R}
                         → {{is-data : IsData g-def-rel ek-def-rel}}
                         → Set
    Insert-commutativity {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} =
        ∀ (r r' : R) → (coll : C R)
        → grain {{is-data}} r' ≢ grain {{is-data}} r
        → insert-coll r' (insert-coll r coll) ≡ insert-coll r (insert-coll r' coll)

    ------------------------------------------------------------
    -- §II.2.1 Delete Invariant
    ------------------------------------------------------------

    -- 1. Progress: collection shrinks
    -- grain-lookup (grain r) (delete-coll r c) = nothing
    -- grain-lookup (grain r) c ≠ nothing → # (delete-coll r c) = # c ∸ 1
    Delete-progress : {R G EK : Set}
                    → {g-def-rel : G IsGrainOf R}
                    → {ek-def-rel : EntityKey-def EK G R}
                    → {{is-data : IsData g-def-rel ek-def-rel}}
                    → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                    → Set
    Delete-progress {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} =
        (∀ (r : R) → (coll : C R)
         → grain-lookup {_≟_ = _≟_} (grain r) (delete-coll r coll) ≡ nothing)
        ×
        (∀ (r : R) → (coll : C R)
         → grain-lookup {_≟_ = _≟_} (grain r) coll ≢ nothing
         → # (delete-coll r coll) ≡ (# coll) ∸ 1)

    -- 2. Safety: only specified grain affected
    -- grain r' = grain r → delete-coll r' (delete-coll r c) = delete-coll r c
    -- grain-lookup (grain r) c = nothing → delete-coll r c = c
    Delete-safety : {R G EK : Set}
                  → {g-def-rel : G IsGrainOf R}
                  → {ek-def-rel : EntityKey-def EK G R}
                  → {{is-data : IsData g-def-rel ek-def-rel}}
                  → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                  → Set
    Delete-safety {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} =
        (∀ (r r' : R) → (coll : C R)
         → grain {{is-data}} r' ≡ grain {{is-data}} r
         → delete-coll r' (delete-coll r coll) ≡ delete-coll r coll)
        ×
        (∀ (r : R) → (coll : C R)
         → grain-lookup {_≟_ = _≟_} (grain r) coll ≡ nothing
         → delete-coll r coll ≡ coll)

    -- 3. Commutativity: different-grain deletes commute
    -- ∀ r, r', c. grain r' ≠ grain r → delete-coll r' (delete-coll r c) = delete-coll r (delete-coll r' c)
    Delete-commutativity : {R G EK : Set}
                         → {g-def-rel : G IsGrainOf R}
                         → {ek-def-rel : EntityKey-def EK G R}
                         → {{is-data : IsData g-def-rel ek-def-rel}}
                         → Set
    Delete-commutativity {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} =
        ∀ (r r' : R) → (coll : C R)
        → grain {{is-data}} r' ≢ grain {{is-data}} r
        → delete-coll r' (delete-coll r coll) ≡ delete-coll r (delete-coll r' coll)

    ------------------------------------------------------------
    -- §II.2.1 Set Operation Properties
    ------------------------------------------------------------

    -- Agreement precondition (required for ∪_coll and ∩_coll commutativity)
    -- ∀ r₁ ∈ c₁, r₂ ∈ c₂. grain r₁ = grain r₂ → r₁ = r₂
    AgreementOnOverlap : {R G EK : Set}
                       → {g-def-rel : G IsGrainOf R}
                       → {ek-def-rel : EntityKey-def EK G R}
                       → {{is-data : IsData g-def-rel ek-def-rel}}
                       → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
                       → C R → C R → Set
    AgreementOnOverlap {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} c₁ c₂ =
        ∀ (r₁ r₂ : R)
        → (_∈coll_) {_≟_ = _≟_} r₁ c₁
        → (_∈coll_) {_≟_ = _≟_} r₂ c₂
        → grain {{is-data}} r₁ ≡ grain {{is-data}} r₂
        → r₁ ≡ r₂

    -- Algebraic properties (under agreement precondition)

    -- ∪_coll properties
    Union-comm : {R : Set} → C R → C R → Set
    Union-comm c₁ c₂ = (c₁ ∪coll c₂) ≡ (c₂ ∪coll c₁)

    Union-assoc : {R : Set} → C R → C R → C R → Set
    Union-assoc c₁ c₂ c₃ = ((c₁ ∪coll c₂) ∪coll c₃) ≡ (c₁ ∪coll (c₂ ∪coll c₃))

    Union-idemp : {R : Set} → C R → Set
    Union-idemp c = (c ∪coll c) ≡ c

    Union-identity : {R : Set} → C R → Set
    Union-identity c = (c ∪coll empty-coll) ≡ c

    -- ∩_coll properties
    module ∩-properties
        {R G EK : Set}
        {g-def-rel : G IsGrainOf R}
        {ek-def-rel : EntityKey-def EK G R}
        {{is-data : IsData g-def-rel ek-def-rel}}
        {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
        where

        Intersection-comm : C R → C R → Set
        Intersection-comm c₁ c₂ =
            (_∩coll_ {_≟_ = _≟_} c₁ c₂) ≡ (_∩coll_ {_≟_ = _≟_} c₂ c₁)

        Intersection-assoc : C R → C R → C R → Set
        Intersection-assoc c₁ c₂ c₃ =
            (_∩coll_ {_≟_ = _≟_} (_∩coll_ {_≟_ = _≟_} c₁ c₂) c₃)
            ≡ (_∩coll_ {_≟_ = _≟_} c₁ (_∩coll_ {_≟_ = _≟_} c₂ c₃))

        Intersection-idemp : C R → Set
        Intersection-idemp c = (_∩coll_ {_≟_ = _≟_} c c) ≡ c

        Intersection-annihilator : C R → Set
        Intersection-annihilator c = (_∩coll_ {_≟_ = _≟_} c empty-coll) ≡ empty-coll

    -- -_coll property
        Diff-self-empty : C R → Set
        Diff-self-empty c = (_-coll_ {_≟_ = _≟_} c c) ≡ empty-coll

    ------------------------------------------------------------
    -- Legacy (PDD/Pipeline.agda dependencies — removed in AT-040R)
    ------------------------------------------------------------

    -- Collection equality (used by BehavioralClasses.agda — relocate to PDA/Relations.agda in AT-050R)
    data _=coll_ : {R : Set} → Rel (C R) (suc 0ℓ) where
        refl-coll : {R : Set} → {coll : C R} → coll =coll coll
        trans-coll : {R : Set}  → {coll₁ coll₂ coll₃ : C R} → coll₁ =coll coll₂ → coll₂ =coll coll₃ → coll₁ =coll coll₃
        sym-coll : {R : Set} → {coll₁ coll₂ : C R} → coll₁ =coll coll₂ → coll₂ =coll coll₁

    singleton : {R : Set} → R → C R
    singleton r = insert-coll r empty-coll

    IsEmpty : {R : Set} → Pred (C R) 0ℓ
    IsEmpty {R} coll = toList coll ≡ []

    IsNonEmpty : {R : Set} → Pred (C R) 0ℓ
    IsNonEmpty coll = ¬ (IsEmpty coll)

    is-empty-bool : {R : Set} → C R → Bool
    is-empty-bool {R} coll = to-bool1 (IsEmpty {R} coll)

    toNonEmptyList : {R : Set} → (coll : C R) → IsNonEmpty coll → List⁺ R
    toNonEmptyList coll is-non-empty with inspect (toList coll)
    ... | it [] toList-coll≡[] =
        ⊥-elim (is-non-empty toList-coll≡[])
    ... | it (r ∷ rs) _ = r ∷⁺ rs

    choice-non-empty : {R : Set} → (coll : C R) → IsNonEmpty coll → R
    choice-non-empty {R} coll is-non-empty =
        let coll-list⁺ = toNonEmptyList coll is-non-empty
        in head⁺ coll-list⁺

    update : {R : Set} → R → C R → C R
    update r coll = insert-coll r (delete-coll r coll)

    filter-dc-b : {R : Set} → (pred : R → Bool) → C R → C R
    filter-dc-b {R} pred coll =
        if is-empty-bool coll
            then empty-coll
            else
                foldr (λ r acc → if pred r then insert-coll r acc else acc)
                      empty-coll coll

    filter-dc : {R : Set} → (pred : R → Set)
              → {pred-is-dec : (r : R) → Dec (pred r)} → C R → C R
    filter-dc {R} pred {pred-is-dec} =
        filter-dc-b (λ r → case (pred-is-dec r) of λ
                        { (yes _) → true
                        ; (no _) → false
                        }
                    )

    _⊆coll_ : {R G EK : Set}
            → {g-def-rel : G IsGrainOf R}
            → {ek-def-rel : EntityKey-def EK G R}
            → {{is-data : IsData g-def-rel ek-def-rel}}
            → {_≟_ : (g₁ g₂ : G) → Dec (g₁ ≡ g₂)}
            → Rel (C R) 0ℓ
    _⊆coll_ {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {_≟_} coll₁ coll₂ =
        ∀ {r : R} → (_∈coll_) {_≟_ = _≟_} r coll₁ → (_∈coll_) {_≟_ = _≟_} r coll₂
    infix 4 _⊆coll_

    _join_on_ : {R₁ R₂ : Set} → C R₁ → C R₂ → (R₁ → R₂ → Bool) → C (R₁ × R₂)
    _join_on_ {R₁} {R₂} coll₁ coll₂ join-pred =
        if is-empty-bool coll₁ ∨ is-empty-bool coll₂
        then empty-coll {R₁ × R₂}
        else
            foldr (λ r acc →
                        foldr (λ r' acc' →
                                        if (join-pred r r')
                                         then insert-coll (r , r')  acc'
                                         else acc'
                                ) acc coll₂
              ) (empty-coll {R₁ × R₂}) coll₁
    infixl 7 _join_on_

    _⊗coll_ : {R₁ R₂ : Set} → C R₁ → C R₂ → C (R₁ × R₂)
    _⊗coll_ coll₁ coll₂ = coll₁ join coll₂ on (λ _ _ → true)
    infixl 7 _⊗coll_

    group : {R G EK Ggrp EKgrp : Set}
          → {g-def-rel : G IsGrainOf R}
          → {ek-def-rel : EntityKey-def EK G R}
          → {g-def-grp-rel : Ggrp IsGrainOf (C R)}
          → {ek-def-grp-rel : EntityKey-def EKgrp Ggrp (C R)}
          → {{is-data : IsData g-def-rel ek-def-rel}}
          → {{is-data-grp : IsData g-def-grp-rel ek-def-grp-rel}}
          → {_≟_ : (g₁ g₂ : Ggrp) → Dec (g₁ ≡ g₂)}
          → (Fields (Grain {{is-data-grp}}) of R)
          → C R
          → C (C R)
    group {R} {G} {EK} {Ggrp} {EKgrp} {g-def-rel} {ek-def-rel} {g-def-grp-rel} {ek-def-grp-rel}
          {{is-data}} {{is-data-grp}} {_≟_} grp-proj coll =
        if is-empty-bool coll
        then (empty-coll {C R})
        else
            foldr (λ r acc → insertGroup r acc) (empty-coll {C R}) coll
            where
                insertGroup : R → C (C R) → C (C R)
                insertGroup r acc =
                    if is-empty-bool acc
                    then singleton (singleton r)
                    else
                        let grp = grp-proj r
                            relevant-group = grain-lookup {_≟_ = _≟_} grp acc
                        in case relevant-group of λ where
                          (just coll-val) → update (insert-coll r coll-val) acc
                          nothing → insert-coll (singleton r) acc

open IsDataColl {{...}} public


------------------------------------------------------------------------
-- §II.1 Type Extractors
------------------------------------------------------------------------

GetT[_] : {C : Set → Set} {R : Set} → (c : C R) → Set
GetT[_] {C} {R} c = R

GetG : {C : Set → Set} {R G EK : Set}
          → {g-def-rel : G IsGrainOf R}
          → {ek-def-rel : EntityKey-def EK G R}
          → {{is-data : IsData g-def-rel ek-def-rel}}
          → {{is-data-coll : IsDataColl C}}
          → (c : C R)
          → Set
GetG {C} {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {{is-data-coll}} c = G[ R ]

GetEK : {C : Set → Set} {R G EK : Set}
          → {g-def-rel : G IsGrainOf R}
          → {ek-def-rel : EntityKey-def EK G R}
          → {{is-data : IsData g-def-rel ek-def-rel}}
          → {{is-data-coll : IsDataColl C}}
          → (coll : C R)
          → Set
GetEK {C} {R} {G} {EK} {g-def-rel} {ek-def-rel} {{is-data}} {{is-data-coll}} coll = EK[ R ]

-- GetBC: requires a BehavioralClass data type — to be added with PDA/Relations.agda (AT-050R)
-- PDD.md signature: GetBC : C R → BehavioralClass

------------------------------------------------------------------------
-- §II.1 Comprehension and Deduplication
------------------------------------------------------------------------

-- Collection comprehension: { f r | r ∈ c }
-- Defined operationally as: foldr (insert-coll ∘ f) empty-coll c
-- Equivalent to map (kept primitive for efficiency).
-- When f is not injective on grains, insert-coll's safety axiom
-- silently drops duplicates (first-writer-wins).
comprehension : {C : Set → Set} {R S : Set}
              → {{is-data-coll : IsDataColl C}}
              → (R → S) → C R → C S
comprehension f c = map f c

-- Deduplication: the identity comprehension.
-- dedup c ≡ { r | r ∈ c } = map id c
-- Since c already satisfies grain-uniqueness, dedup c = c (no-op).
dedup : {C : Set → Set} {R : Set}
      → {{is-data-coll : IsDataColl C}}
      → C R → C R
dedup c = map id c
