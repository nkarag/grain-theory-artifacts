/-
  GrainTheory.Foundations.Realization — records, declarations, realizations

  arXiv v4 `def:type-denotation` (Denotation of a type under a declaration set),
  `def:structure-map` (Structure map), `rem:realization-and-change` (What a
  realization fixes, and what changes with it) and
  `thm:type-grain-vs-collection-key` (Type grain versus collection key), on
  flat records.

  The abstract layer (`SemanticGrainStructure`) has one `den`: one instance is
  one realization. The paper's revision of 21 Nov 2026 makes the denotation
  relative to a realization, an admissible choice of carriers and functions,
  and says that which functions are isomorphisms is settled by `Δ` alone and
  holds in every realization. A bijection of denotations in one realization is
  therefore no isomorphism, and the abstract axiom `equivIso`, which turned one
  into an `iso`, was unsound for that reading. It is removed. This module
  proves, on a concrete model, the step it stood for:

    injective in every admissible realization
      ⟺  every component of `R` lies in the closure of `K` under `Δ`
      ⟺  `R ≅ K` by structure maps,

  and `equivIso_unsound` is the paper's employee example, mechanized: a
  realization in which the projection onto the e-mail address is a bijection
  while no structure map runs back.

  The model. Fields `F`; declarations `Δ i = U → V` between finite field sets;
  a realization gives each field a carrier and each declaration a function
  from `U`-records to `V`-records. A record over all the fields is consistent
  when every declared function agrees with it; a `W`-record is valid when it is
  the `W`-part of a consistent one; `den ρ W` is the set of valid `W`-records,
  the `Δ`-constrained product. Structure maps on records are given as syntax
  (projections, pairings, declared determinations, composites) and evaluated
  in each realization, so that whether one exists is settled by `Δ` alone.
-/

import Mathlib.Tactic

namespace GrainTheory.Foundations.Realizations

/-! ## Declarations, records, realizations -/

/-- A declared determination `U → V` between field sets. -/
structure Decl (F : Type) where
  lhs : Finset F
  rhs : Finset F

variable {F : Type} {ι : Type}

/-- A `W`-record: a value for each field of `W`. -/
def Rec (V : F → Type) (W : Finset F) : Type := ∀ f : W, V f.1

/-- The `W`-part of a record over all the fields. -/
def res {V : F → Type} (r : ∀ f, V f) (W : Finset F) : Rec V W := fun f => r f.1

/-- Restriction of a `W`-record to `W' ⊆ W`: the field-set projection. -/
def restrict {V : F → Type} {W W' : Finset F} (h : W' ⊆ W) (a : Rec V W) : Rec V W' :=
  fun f => a ⟨f.1, h f.2⟩

@[simp] theorem restrict_res {V : F → Type} {W W' : Finset F} (h : W' ⊆ W) (r : ∀ f, V f) :
    restrict h (res r W) = res r W' := rfl

/-- A realization of `Δ`: a carrier for each field and a function for each
    declaration. -/
structure Realization (Δ : ι → Decl F) where
  V : F → Type
  d : ∀ i, Rec V (Δ i).lhs → Rec V (Δ i).rhs

variable {Δ : ι → Decl F}

/-- A record over all the fields is `Δ`-consistent when its `V`-part is
    `d_{U → V}` of its `U`-part, for every declaration. -/
def Consistent (ρ : Realization Δ) (r : ∀ f, ρ.V f) : Prop :=
  ∀ i, ρ.d i (res r (Δ i).lhs) = res r (Δ i).rhs

/-- Admissible: every carrier value occurs in some consistent record. -/
def Admissible (ρ : Realization Δ) : Prop :=
  ∀ f (v : ρ.V f), ∃ r, Consistent ρ r ∧ r f = v

/-- A `W`-record is `Δ`-valid when it is the `W`-part of a consistent record. -/
def Valid (ρ : Realization Δ) (W : Finset F) (a : Rec ρ.V W) : Prop :=
  ∃ r, Consistent ρ r ∧ res r W = a

/-- `den ρ W`: the valid `W`-records under the realization `ρ`. -/
def den (ρ : Realization Δ) (W : Finset F) : Type := {a : Rec ρ.V W // Valid ρ W a}

/-- The field-set projection `k : R ↠ K` on denotations, for `K ⊆ R`. -/
def proj (ρ : Realization Δ) {R K : Finset F} (h : K ⊆ R) (a : den ρ R) : den ρ K :=
  ⟨restrict h a.1, by obtain ⟨r, hc, hr⟩ := a.2; exact ⟨r, hc, by rw [← hr]; rfl⟩⟩

/-- "`k : R ↠ K`": the projection is onto, since both sides are restrictions of
    the same consistent records. -/
theorem proj_surjective (ρ : Realization Δ) {R K : Finset F} (h : K ⊆ R) :
    Function.Surjective (proj ρ h) := by
  rintro ⟨b, r, hc, rfl⟩
  exact ⟨⟨res r R, r, hc, rfl⟩, rfl⟩

/-! ## Attribute closure -/

/-- `f` lies in the closure of `K` under `Δ`. -/
inductive InCl (Δ : ι → Decl F) (K : Finset F) : F → Prop
  | base {f} : f ∈ K → InCl Δ K f
  | step (i : ι) {f} : (∀ g ∈ (Δ i).lhs, InCl Δ K g) → f ∈ (Δ i).rhs → InCl Δ K f

/-- The closure is transitive: what `B` determines, `A` determines when it
    determines `B`. -/
theorem InCl.trans {A B : Finset F} (hB : ∀ g ∈ B, InCl Δ A g) {f : F}
    (h : InCl Δ B f) : InCl Δ A f := by
  induction h with
  | base hf => exact hB _ hf
  | step i _ hf ih => exact .step i ih hf

variable [DecidableEq F]

/-! ## Structure maps on records

  The generators of `def:structure-map` on products: projections, pairings,
  declared determinations, closed under composition (an identity is the
  projection onto all the fields). A term is syntax: it means the same
  composite of generators in every realization, and `eval` reads it in one. -/

/-- A structure map from `W`-records to `W'`-records, as a composite of
    generators. -/
inductive SMap (Δ : ι → Decl F) : Finset F → Finset F → Type
  | proj {W W' : Finset F} : W' ⊆ W → SMap Δ W W'
  | pair {C A B : Finset F} : SMap Δ C A → SMap Δ C B → SMap Δ C (A ∪ B)
  | decl (i : ι) : SMap Δ (Δ i).lhs (Δ i).rhs
  | comp {A B C : Finset F} : SMap Δ A B → SMap Δ B C → SMap Δ A C

/-- A structure map read in the realization `ρ`. -/
def SMap.eval (ρ : Realization Δ) :
    {W W' : Finset F} → SMap Δ W W' → Rec ρ.V W → Rec ρ.V W'
  | _, _, .proj h, a => restrict h a
  | _, _, @SMap.pair _ _ _ _ _ A B s t, a => fun f =>
      if hA : f.1 ∈ A then s.eval ρ a ⟨f.1, hA⟩
      else t.eval ρ a ⟨f.1, (Finset.mem_union.1 f.2).resolve_left hA⟩
  | _, _, .decl i, a => ρ.d i a
  | _, _, .comp s t, a => t.eval ρ (s.eval ρ a)

/-- **A structure map follows the record.** On the `W`-part of a consistent
    record every structure map returns that record's `W'`-part: it can keep a
    column, copy it or follow a declaration, and nothing else. -/
theorem SMap.eval_res (ρ : Realization Δ) {r : ∀ f, ρ.V f} (hc : Consistent ρ r) :
    {W W' : Finset F} → (s : SMap Δ W W') → s.eval ρ (res r W) = res r W'
  | _, _, .proj _ => rfl
  | _, _, .pair s t => by
      funext f
      simp only [SMap.eval]
      split_ifs with hA
      · exact congrFun (s.eval_res ρ hc) ⟨f.1, hA⟩
      · exact congrFun (t.eval_res ρ hc) _
  | _, _, .decl i => hc i
  | _, _, .comp s t => by simp only [SMap.eval, s.eval_res ρ hc, t.eval_res ρ hc]

/-- A structure map takes valid records to valid records. -/
theorem SMap.eval_valid (ρ : Realization Δ) {W W' : Finset F} (s : SMap Δ W W')
    {a : Rec ρ.V W} (ha : Valid ρ W a) : Valid ρ W' (s.eval ρ a) := by
  obtain ⟨r, hc, rfl⟩ := ha
  exact ⟨r, hc, (s.eval_res ρ hc).symm⟩

/-- **Soundness.** A structure map from `W` to `W'` exists only if every field
    of `W'` lies in the closure of `W`. -/
theorem SMap.sound : {W W' : Finset F} → SMap Δ W W' → ∀ f ∈ W', InCl Δ W f
  | _, _, .proj h, _, hf => .base (h hf)
  | _, _, .pair s t, _, hf => (Finset.mem_union.1 hf).elim (s.sound _) (t.sound _)
  | _, _, .decl _, _, hf => .step _ (fun _ hg => .base hg) hf
  | _, _, .comp s t, _, hf => InCl.trans s.sound (t.sound _ hf)

/-- Pairing over a finite field set. -/
theorem SMap.pairAll {W : Finset F} :
    ∀ S : Finset F, (∀ g ∈ S, Nonempty (SMap Δ W {g})) → Nonempty (SMap Δ W S) := by
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨.proj (Finset.empty_subset _)⟩
  | insert a S _ ih =>
      intro h
      obtain ⟨sa⟩ := h a (Finset.mem_insert_self a S)
      obtain ⟨sS⟩ := ih (fun g hg => h g (Finset.mem_insert_of_mem hg))
      exact ⟨Finset.insert_eq a S ▸ SMap.pair sa sS⟩

/-- **Completeness.** Every field in the closure of `W` is reached from `W` by
    a structure map. -/
theorem SMap.of_inCl {W : Finset F} {f : F} (h : InCl Δ W f) : Nonempty (SMap Δ W {f}) := by
  induction h with
  | base hf => exact ⟨.proj (Finset.singleton_subset_iff.2 hf)⟩
  | @step i f _ hf ih =>
      obtain ⟨sl⟩ := SMap.pairAll _ ih
      exact ⟨.comp (.comp sl (.decl i)) (.proj (Finset.singleton_subset_iff.2 hf))⟩

/-- A structure map from `W` to `W'` exists exactly when `W'` lies in the
    closure of `W`. -/
theorem SMap.nonempty_iff {W W' : Finset F} :
    Nonempty (SMap Δ W W') ↔ ∀ f ∈ W', InCl Δ W f :=
  ⟨fun ⟨s⟩ => s.sound, fun h => SMap.pairAll W' (fun _ hg => SMap.of_inCl (h _ hg))⟩

/-! ## Isomorphism by structure maps -/

/-- **`R ≅ K` by structure maps** (`def:structure-map`): structure maps both
    ways, inverse to each other on the valid records of every admissible
    realization. -/
def StructIso (Δ : ι → Decl F) (R K : Finset F) : Prop :=
  ∃ (s : SMap Δ R K) (t : SMap Δ K R), ∀ ρ : Realization Δ, Admissible ρ →
    (∀ a : den ρ R, t.eval ρ (s.eval ρ a.1) = a.1) ∧
    (∀ b : den ρ K, s.eval ρ (t.eval ρ b.1) = b.1)

/-- Any two structure maps between `R` and `K`, one each way, are inverse to
    each other: on valid records both follow the record. So `R ≅ K` exactly
    when each lies in the closure of the other — whatever the realization. -/
theorem structIso_iff_mutual {R K : Finset F} :
    StructIso Δ R K ↔ (∀ f ∈ K, InCl Δ R f) ∧ (∀ f ∈ R, InCl Δ K f) := by
  constructor
  · rintro ⟨s, t, _⟩
    exact ⟨s.sound, t.sound⟩
  · rintro ⟨hK, hR⟩
    obtain ⟨s⟩ := SMap.nonempty_iff.2 hK
    obtain ⟨t⟩ := SMap.nonempty_iff.2 hR
    refine ⟨s, t, fun ρ _ => ⟨?_, ?_⟩⟩
    · rintro ⟨_, r, hc, rfl⟩
      simp only [s.eval_res ρ hc, t.eval_res ρ hc]
    · rintro ⟨_, r, hc, rfl⟩
      simp only [s.eval_res ρ hc, t.eval_res ρ hc]

/-- For a field-set projection, `R ≅ K` exactly when every component of `R`
    lies in the closure of `K`. -/
theorem structIso_iff_cl {R K : Finset F} (h : K ⊆ R) :
    StructIso Δ R K ↔ ∀ f ∈ R, InCl Δ K f := by
  rw [structIso_iff_mutual]
  exact ⟨And.right, fun hR => ⟨fun _ hf => .base (h hf), hR⟩⟩

/-- `R ≅ K` holds in every realization or in none: its witnesses are terms,
    and the realization is not consulted. -/
theorem structIso_realization_free {R K : Finset F} (hi : StructIso Δ R K)
    (ρ : Realization Δ) :
    ∃ (s : SMap Δ R K) (t : SMap Δ K R),
      (∀ a : den ρ R, t.eval ρ (s.eval ρ a.1) = a.1) ∧
      (∀ b : den ρ K, s.eval ρ (t.eval ρ b.1) = b.1) := by
  obtain ⟨hK, hR⟩ := structIso_iff_mutual.1 hi
  obtain ⟨s⟩ := SMap.nonempty_iff.2 hK
  obtain ⟨t⟩ := SMap.nonempty_iff.2 hR
  refine ⟨s, t, ?_, ?_⟩
  · rintro ⟨_, r, hc, rfl⟩
    simp only [s.eval_res ρ hc, t.eval_res ρ hc]
  · rintro ⟨_, r, hc, rfl⟩
    simp only [s.eval_res ρ hc, t.eval_res ρ hc]

/-! ## The separating realization

  The proof of `thm:type-grain-vs-collection-key`: "give every field in the
  closure of `K` one value and every field outside it two, take the record
  that is constant on the first value and the record that takes the second
  value outside the closure, and let each declared function return, on each
  record's determinant part, that record's target part, which is well defined
  because a determinant inside the closure has its target inside it as well." -/

section Separating

variable (Δ) (K : Finset F)

/-- One value (`false`) inside the closure of `K`, two outside it. -/
def SepV (f : F) : Type := {b : Bool // InCl Δ K f → b = false}

/-- The record constant on the first value. -/
def r₀ : ∀ f, SepV Δ K f := fun _ => ⟨false, fun _ => rfl⟩

open Classical in
/-- The record that takes the second value outside the closure. -/
noncomputable def r₁ : ∀ f, SepV Δ K f := fun f =>
  if h : InCl Δ K f then ⟨false, fun _ => rfl⟩ else ⟨true, fun h' => absurd h' h⟩

omit [DecidableEq F] in
theorem r₁_eq_r₀_iff (f : F) : r₁ Δ K f = r₀ Δ K f ↔ InCl Δ K f := by
  unfold r₁ r₀
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => Bool.noConfusion (congrArg Subtype.val e : true = false),
      fun h' => absurd h' h⟩

open Classical in
/-- Each declared function returns, on each record's determinant part, that
    record's target part. -/
noncomputable def sep : Realization Δ where
  V := SepV Δ K
  d i a := if a = res (r₁ Δ K) (Δ i).lhs then res (r₁ Δ K) (Δ i).rhs
    else res (r₀ Δ K) (Δ i).rhs

omit [DecidableEq F] in
theorem sep_consistent₁ : Consistent (sep Δ K) (r₁ Δ K) := fun i => by
  simp [sep]

omit [DecidableEq F] in
/-- Well defined: if the two records agree on a determinant, it lies inside the
    closure, so the target does too and the two records agree there as well. -/
theorem sep_consistent₀ : Consistent (sep Δ K) (r₀ Δ K) := fun i => by
  dsimp only [sep]
  split_ifs with h
  · have hl : ∀ g ∈ (Δ i).lhs, InCl Δ K g := fun g hg =>
      (r₁_eq_r₀_iff Δ K g).1 (congrFun h ⟨g, hg⟩).symm
    funext f
    exact (r₁_eq_r₀_iff Δ K f.1).2 (.step i hl f.2)
  · rfl

omit [DecidableEq F] in
theorem sep_admissible : Admissible (sep Δ K) := by
  rintro f ⟨b, hb⟩
  cases b with
  | false => exact ⟨r₀ Δ K, sep_consistent₀ Δ K, rfl⟩
  | true =>
      have hn : ¬ InCl Δ K f := fun h => Bool.noConfusion (hb h)
      refine ⟨r₁ Δ K, sep_consistent₁ Δ K, ?_⟩
      change r₁ Δ K f = _
      simp [r₁, hn]

end Separating

/-! ## Type grain versus collection key -/

/-- `k` is a superkey of the collection `c`: injective on its elements. A
    collection is drawn from one realization: a set of valid records of it. -/
def SuperkeyOn {ρ : Realization Δ} {R K : Finset F} (h : K ⊆ R) (c : Set (den ρ R)) :
    Prop :=
  Set.InjOn (proj ρ h) c

omit [DecidableEq F] in
/-- (3) ⇒ (1). An isomorphism is injective in every realization. -/
theorem injective_of_cl {R K : Finset F} (h : K ⊆ R) (hR : ∀ f ∈ R, InCl Δ K f)
    (ρ : Realization Δ) : Function.Injective (proj ρ h) := by
  classical
  obtain ⟨t⟩ := SMap.nonempty_iff.2 hR
  rintro ⟨_, ra, hca, rfl⟩ ⟨_, rb, hcb, rfl⟩ hk
  have hk' : res ra K = res rb K := congrArg Subtype.val hk
  apply Subtype.ext
  change res ra R = res rb R
  rw [← t.eval_res ρ hca, ← t.eval_res ρ hcb, hk']

omit [DecidableEq F] in
/-- (1) ⇒ (3). A component of `R` outside the closure of `K` gives an admissible
    realization holding two valid `R`-records that agree on `K`. -/
theorem not_injective_of_not_inCl {R K : Finset F} (h : K ⊆ R) {f : F} (hf : f ∈ R)
    (hn : ¬ InCl Δ K f) :
    ∃ ρ : Realization Δ, Admissible ρ ∧ ¬ Function.Injective (proj ρ h) := by
  refine ⟨sep Δ K, sep_admissible Δ K, fun hinj => hn ?_⟩
  have e := hinj (a₁ := ⟨res (r₀ Δ K) R, r₀ Δ K, sep_consistent₀ Δ K, rfl⟩)
    (a₂ := ⟨res (r₁ Δ K) R, r₁ Δ K, sep_consistent₁ Δ K, rfl⟩)
    (Subtype.ext (funext fun g => ((r₁_eq_r₀_iff Δ K g.1).2 (.base g.2)).symm))
  exact (r₁_eq_r₀_iff Δ K f).1 (congrFun (congrArg Subtype.val e) ⟨f, hf⟩).symm

omit [DecidableEq F] in
/-- **Injective in every admissible realization ⟺ the closure step.** -/
theorem injective_all_iff_cl {R K : Finset F} (h : K ⊆ R) :
    (∀ ρ : Realization Δ, Admissible ρ → Function.Injective (proj ρ h)) ↔
      ∀ f ∈ R, InCl Δ K f := by
  refine ⟨fun hinj f hf => ?_, fun hR ρ _ => injective_of_cl h hR ρ⟩
  by_contra hn
  obtain ⟨ρ, hρ, hni⟩ := not_injective_of_not_inCl h hf hn
  exact hni (hinj ρ hρ)

/-- **arXiv v4 `thm:type-grain-vs-collection-key` (Type grain versus collection
    key).** For a field-set projection `k : R ↠ K` the following are
    equivalent:

    (1) `k` is injective on `den R` in every admissible realization;
    (2) `k` is a superkey of every collection, each drawn from one admissible
        realization;
    (3) `k` is an isomorphism `R ≅ K` by structure maps;

    and each holds exactly when every component of `R` lies in the closure of
    `K` under `Δ`. -/
theorem type_grain_vs_collection_key {R K : Finset F} (h : K ⊆ R) :
    ((∀ ρ : Realization Δ, Admissible ρ → Function.Injective (proj ρ h)) ↔
      ∀ ρ : Realization Δ, Admissible ρ → ∀ c : Set (den ρ R), SuperkeyOn h c)
    ∧ ((∀ ρ : Realization Δ, Admissible ρ → Function.Injective (proj ρ h)) ↔
      StructIso Δ R K)
    ∧ (StructIso Δ R K ↔ ∀ f ∈ R, InCl Δ K f) :=
  ⟨⟨fun hi ρ hρ _ => (hi ρ hρ).injOn, fun hs ρ hρ => Set.injOn_univ.1 (hs ρ hρ Set.univ)⟩,
   (injective_all_iff_cl h).trans (structIso_iff_cl h).symm,
   structIso_iff_cl h⟩

/-- **The "moreover" clause.** `K` is a grain of `R` among field-set
    projections exactly when `k` satisfies the conditions and no proper
    sub-projection does: the irreducibility clause of `def:grain` read on
    `K`. -/
def IsFieldGrain (Δ : ι → Decl F) (K R : Finset F) : Prop :=
  K ⊆ R ∧ StructIso Δ R K ∧ ∀ K' ⊂ K, ¬ StructIso Δ R K'

theorem isFieldGrain_iff {K R : Finset F} (h : K ⊆ R) :
    IsFieldGrain Δ K R ↔
      (∀ ρ : Realization Δ, Admissible ρ → Function.Injective (proj ρ h)) ∧
      ∀ (K' : Finset F) (h' : K' ⊂ K),
        ¬ ∀ ρ : Realization Δ, Admissible ρ →
          Function.Injective (proj ρ (h'.subset.trans h)) := by
  unfold IsFieldGrain
  simp only [(type_grain_vs_collection_key (Δ := Δ) _).2.1, h, true_and]

/-! ## One realization at a time

  `rem:realization-and-change`: "An update therefore moves from one
  realization to another… The two records `(7, d(7))` and `(7, d'(7))` are
  never elements of one collection, since no realization contains both." -/

omit [DecidableEq F] in
/-- Two valid records of one realization that agree on a declaration's
    determinant agree on its target. A bag holding a record before an update
    and the same entity's record after it is drawn from no realization. -/
theorem agree_on_target {ρ : Realization Δ} {R : Finset F} (i : ι)
    (hl : (Δ i).lhs ⊆ R) (hr : (Δ i).rhs ⊆ R) (a b : den ρ R)
    (hab : restrict hl a.1 = restrict hl b.1) : restrict hr a.1 = restrict hr b.1 := by
  obtain ⟨_, ra, hca, rfl⟩ := a
  obtain ⟨_, rb, hcb, rfl⟩ := b
  simp only [restrict_res] at hab ⊢
  rw [← hca i, ← hcb i, hab]

/-! ## Why `equivIso` had to go

  `def:structure-map`: "Let `Employee = EmployeeId × EmailAddr` with the single
  declaration `{EmployeeId} → {EmailAddr}`. The projection onto `EmailAddr` may
  well be one-to-one on the data, every employee having an address of their
  own. It is still not an isomorphism: no generator runs from `EmailAddr` back
  to `EmployeeId`." Field `0` is `EmployeeId`, field `1` is `EmailAddr`. -/

namespace Employee

/-- `{EmployeeId} → {EmailAddr}`. -/
def Δe : Unit → Decl (Fin 2) := fun _ => ⟨{0}, {1}⟩

/-- Each employee's address is their identifier: one-to-one on the data. -/
def ρe : Realization Δe where
  V _ := Bool
  d _ a := fun _ => a ⟨0, Finset.mem_singleton_self 0⟩

theorem consistent_iff (r : ∀ _ : Fin 2, Bool) : Consistent ρe r ↔ r 1 = r 0 := by
  constructor
  · intro h
    exact (congrFun (h ()) ⟨1, Finset.mem_singleton_self 1⟩).symm
  · intro h _
    funext f
    obtain ⟨f, hf⟩ := f
    have e : f = 1 := Finset.mem_singleton.1 hf
    subst e
    exact h.symm

theorem ρe_admissible : Admissible ρe := fun _ v =>
  ⟨fun _ => v, (consistent_iff _).2 rfl, rfl⟩

/-- In this realization the projection `Employee ↠ EmailAddr` is a bijection… -/
theorem proj_bijective :
    Function.Bijective (proj ρe (show ({1} : Finset (Fin 2)) ⊆ {0, 1} by decide)) := by
  refine ⟨?_, proj_surjective _ _⟩
  rintro ⟨_, ra, hca, rfl⟩ ⟨_, rb, hcb, rfl⟩ hk
  have h1 : ra 1 = rb 1 := congrFun (congrArg Subtype.val hk) ⟨1, Finset.mem_singleton_self 1⟩
  have h0 : ra 0 = rb 0 := by
    rw [← (consistent_iff ra).1 hca, ← (consistent_iff rb).1 hcb, h1]
  apply Subtype.ext
  funext f
  obtain ⟨f, hf⟩ := f
  fin_cases f
  · exact h0
  · exact h1

/-- …but `EmailAddr` does not determine `EmployeeId`. -/
theorem not_inCl : ¬ InCl Δe {1} 0 := by
  intro h
  cases h with
  | base h => exact absurd (Finset.mem_singleton.1 h) (by decide)
  | step _ _ hf =>
      exact absurd (Finset.mem_singleton.1 (show (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) from hf))
        (by decide)

/-- **`equivIso` is unsound for the paper's reading.** An admissible
    realization in which the denotations of `Employee` and `EmailAddr` are in
    bijection, by a structure map even, while `Employee ≇ EmailAddr`. -/
theorem equivIso_unsound :
    ∃ ρ : Realization Δe, Admissible ρ ∧ Nonempty (den ρ {0, 1} ≃ den ρ {1}) ∧
      ¬ StructIso Δe {0, 1} {1} :=
  ⟨ρe, ρe_admissible, ⟨Equiv.ofBijective _ proj_bijective⟩, fun hi =>
    not_inCl ((structIso_iff_cl (by decide)).1 hi 0 (by decide))⟩

end Employee

end GrainTheory.Foundations.Realizations
