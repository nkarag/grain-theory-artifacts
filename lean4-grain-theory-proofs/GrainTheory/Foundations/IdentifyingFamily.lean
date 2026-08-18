/-
  GrainTheory.Foundations.IdentifyingFamily — Grain as a Minimal Identifying Family

  arXiv extended version, §4.4 (Grain as a Minimal Identifying Family):
  - Definition 4.4 (Identifying family)
  - Proposition 4.5 (Identifying families on product types)

  Grain generalizes the relational *candidate key*. On a flat relation a
  candidate key is a minimal set of attributes whose values jointly identify
  each row. The same idea lifts to any algebraic data type once "attribute"
  is read as *observation* — a projection out of the type.

  This is the element-level view, so it lives on the semantic layer
  (`SemanticGrainStructure`, which supplies `den : D → Type`).

  **Why this section exists.** Reviewer R2 observed that irreducibility, read
  on carriers, cannot separate `CustomerId` from `CustomerId × CustomerName`:
  the two are isomorphic, and no isomorphism-invariant property distinguishes
  them. The identifying-family view relocates minimality from the *carrier*
  to the *index set* — which observations you keep — where the carrier
  isomorphism has no purchase. `{custId} ⊊ {custId, name}` as families,
  and `{custId}` already identifies, so the padded family is redundant.

  Categorically the family is a jointly-monic cone; we keep the DB-first
  vocabulary. The paper flags the full cone reformulation as future work, and
  nothing in the development below is load-bearing for the rest of the
  theory — it is a bridge, mechanized to show the two readings agree.
-/

import GrainTheory.DependencyTheory.Factorization
import GrainTheory.Foundations.GrainDef

universe u v

namespace GrainTheory.Foundations

open GrainStructure SemanticGrainStructure

variable {D : Type u} [SemanticGrainStructure.{u, v} D]

/-! ## Definition 4.4: Identifying family -/

/-- An **observation family** on `R`: an index set `I` together with, for
    each index, a target type and a projection out of `R`.

    The observations of a product type are its fields, but the notion is
    deliberately wider: a *declared* projection is an observation like any
    other — an entity map `entity : R ↠ E`, or the snapshot date of a
    partitioned collection. That is what makes **external grains** come "for
    free" rather than needing a separate case. -/
structure ObsFamily (D : Type u) [SemanticGrainStructure.{u, v} D]
    (R : D) (I : Type v) where
  /-- The target type of each observation. -/
  target : I → D
  /-- The observation itself: a projection out of `R`. -/
  proj : ∀ i : I, den R → den (target i)

/-- **Definition 4.4 (Identifying family).** A subfamily `S ⊆ I` is
    *identifying* when agreeing on every observation in `S` forces equality:
    `(∀ i ∈ S, pᵢ r = pᵢ r') → r = r'`.

    On a relation this says exactly that `S` is a **superkey**. -/
def ObsFamily.Identifying {R : D} {I : Type v}
    (F : ObsFamily D R I) (S : I → Prop) : Prop :=
  ∀ r r' : den R, (∀ i : I, S i → F.proj i r = F.proj i r') → r = r'

/-- A **minimal identifying family**: identifying, and no proper subfamily
    is. On a relation this is a **candidate key**.

    Minimality is on the *index set*, not the carrier — the point of the
    whole construction. -/
def ObsFamily.MinimalIdentifying {R : D} {I : Type v}
    (F : ObsFamily D R I) (S : I → Prop) : Prop :=
  F.Identifying S ∧
  ∀ S' : I → Prop, (∀ i, S' i → S i) → (∃ i, S i ∧ ¬ S' i) → ¬ F.Identifying S'

/-! ## Basic facts -/

/-- Identifying is upward closed: enlarging a family cannot break
    identification. In relational terms, a superset of a superkey is a
    superkey — Armstrong's augmentation, at the family level. -/
theorem ObsFamily.Identifying.mono {R : D} {I : Type v}
    {F : ObsFamily D R I} {S S' : I → Prop}
    (h : F.Identifying S) (h_sub : ∀ i, S i → S' i) : F.Identifying S' :=
  fun r r' h_agree => h r r' (fun i hi => h_agree i (h_sub i hi))

/-- The full family of observations of `R` is identifying as soon as *some*
    subfamily is. -/
theorem ObsFamily.identifying_univ {R : D} {I : Type v}
    {F : ObsFamily D R I} {S : I → Prop} (h : F.Identifying S) :
    F.Identifying (fun _ => True) :=
  h.mono (fun _ _ => trivial)

/-! ## The combined map and its image

  A family `S` induces the combined map `⟨pᵢ⟩_{i ∈ S}`. Identification is
  exactly injectivity of that map, and `G[R]` is presented as its image.

  We work with the injectivity formulation directly: `den` gives us actual
  Lean types, so "the image of the combined map" is `Set.range`, and the
  bijection `R ≃ image` is `Equiv.ofInjective`. -/

/-- The combined map of a subfamily, as a function into the dependent product
    of the observation targets restricted to `S`. -/
def ObsFamily.combined {R : D} {I : Type v}
    (F : ObsFamily D R I) (S : I → Prop) :
    den R → (∀ i : {i : I // S i}, den (F.target i.val)) :=
  fun r i => F.proj i.val r

/-- **Identification is injectivity of the combined map.**

    This is the step that makes the isomorphism clause of Definition 3.1
    *free* under the family reading: an injective map is a bijection onto its
    image, so `G[R] ≅ R` falls out and index-set minimality is left as the
    only real content. -/
theorem ObsFamily.identifying_iff_injective {R : D} {I : Type v}
    (F : ObsFamily D R I) (S : I → Prop) :
    F.Identifying S ↔ Function.Injective (F.combined S) := by
  constructor
  · intro h r r' h_eq
    exact h r r' (fun i hi => congrFun h_eq ⟨i, hi⟩)
  · intro h r r' h_agree
    exact h (funext fun i => h_agree i.val i.property)

/-- The image of the combined map of an identifying family is in bijection
    with `R` — the isomorphism clause, obtained for free. -/
noncomputable def ObsFamily.imageEquiv {R : D} {I : Type v}
    (F : ObsFamily D R I) (S : I → Prop) (h : F.Identifying S) :
    den R ≃ Set.range (F.combined S) :=
  Equiv.ofInjective _ ((F.identifying_iff_injective S).mp h)

/-! ## Proposition 4.5: Identifying families on product types

  On a product type whose observations are its fields, a family is
  identifying iff it is a superkey, and a *minimal* one is a candidate key
  whose combined-map image is the grain of Definition 3.1.

  The two halves of Definition 3.1 land as follows.

  * **Isomorphism.** Free: `imageEquiv` above.
  * **Irreducibility.** This is where the reading is chosen. Index-set
    minimality (`MinimalIdentifying`) is a statement about *which
    observations are kept*; structural irreducibility (`IsIrreducible`) is a
    statement about *components of the carrier*. On a product type whose
    observations are exactly its fields the two coincide, because a
    subfamily of fields and a structural subtype are the same thing. We
    record that correspondence as the bridge below.

  The bridge is stated as a hypothesis rather than derived, because relating
  an index set of observations to the component structure of `D` requires a
  concrete model of `D` — which the abstract axiomatization deliberately does
  not fix (see the "no concrete model" limitation). What is mechanized is
  that *given* the correspondence, the family view and Definition 3.1 select
  the same grain. -/

/-- The bridge between the two readings of minimality on a product type:
    subfamilies of the field observations correspond to structural subtypes
    of the combined image, and identification corresponds to isomorphism
    with `R`. -/
structure FieldPresentation {R : D} {I : Type v}
    (F : ObsFamily D R I) (S : I → Prop) (G : D) : Prop where
  /-- `G` presents the family `S`: its carrier is the image of the combined
      map, so `G ≅ R` exactly when `S` identifies. -/
  presents : F.Identifying S → iso G R
  /-- Structural subtypes of `G` are the sub-families of `S`: a structural
      subtype `T ⊑ G` that still identifies `R` reflects to a sub-family
      `S' ⊆ S` that still identifies, and if that sub-family turns out to be
      all of `S` then `T` is all of `G`. -/
  reflects : ∀ T : D, ssub T G → iso T R →
    ∃ S' : I → Prop, (∀ i, S' i → S i) ∧ F.Identifying S' ∧
      ((∀ i, S i → S' i) → ssub G T)
  /-- Conversely, a sub-family that still identifies is realized by a
      structural subtype. -/
  realizes : ∀ S' : I → Prop, (∀ i, S' i → S i) → (∃ i, S i ∧ ¬ S' i) →
    ∃ T : D, ssub T G ∧ ¬ ssub G T ∧ (F.Identifying S' → iso T R)

/-- **Proposition 4.5 (Identifying families on product types).**

    If `S` is a *minimal* identifying family and `G` presents it, then `G`
    satisfies Definition 3.1 for `R`: `G` is a grain of `R`.

    In words: a candidate key, presented as the image of its combined map,
    *is* the grain. -/
theorem minimalIdentifying_isGrainOf {R : D} {I : Type v}
    {F : ObsFamily D R I} {S : I → Prop} {G : D}
    (h_min : F.MinimalIdentifying S) (h_pres : FieldPresentation F S G) :
    IsGrainOf G R := by
  refine ⟨h_pres.presents h_min.1, fun T h_ssub h_iso => ?_⟩
  -- A structural subtype of G isomorphic to R reflects to an identifying
  -- sub-family S'. Minimality of S forbids S' from being proper, so S' is
  -- all of S — and then T is all of G.
  obtain ⟨S', h_sub, h_ident, h_full⟩ := h_pres.reflects T h_ssub h_iso
  refine h_full (fun i hi => ?_)
  by_contra h_not
  exact h_min.2 S' h_sub ⟨i, hi, h_not⟩ h_ident

/-- **Converse direction.** If `G` is a grain of `R` and presents the family
    `S`, then `S` is minimal identifying: no proper sub-family identifies.

    Together with `minimalIdentifying_isGrainOf`, this is the equivalence
    Proposition 4.5 asserts — the two definitions of grain, structural and
    family-theoretic, pick out the same object. -/
theorem isGrainOf_minimalIdentifying {R : D} {I : Type v}
    {F : ObsFamily D R I} {S : I → Prop} {G : D}
    (h_ident : F.Identifying S)
    (h_grain : IsGrainOf G R) (h_pres : FieldPresentation F S G) :
    F.MinimalIdentifying S := by
  refine ⟨h_ident, fun S' h_sub h_witness h_ident' => ?_⟩
  -- A proper identifying sub-family is realized by a proper structural
  -- subtype T ⊏ G with T ≅ R, contradicting irreducibility of G.
  obtain ⟨T, h_ssub, h_nssub, h_iso⟩ := h_pres.realizes S' h_sub h_witness
  exact h_nssub (h_grain.2 T h_ssub (h_iso h_ident'))

/-! ## Why the carrier reading could not do this

  The following makes the reviewer's objection precise inside the
  formalization. Irreducibility is *not* invariant under isomorphism, so it
  cannot be a property of the carrier alone; conversely, any property that
  *is* isomorphism-invariant is useless for selecting a grain, since all
  candidate grains of `R` are isomorphic to one another.

  `multiple_grains_iso` is exactly that observation: every grain of `R` is
  isomorphic to every other. So an iso-invariant `P` holding of one grain
  holds of all types isomorphic to `R` — including padded ones. -/

/-- Any isomorphism-invariant property that holds of some grain of `R` holds
    of **every** type isomorphic to `R`, padded candidates included.

    This is why minimality must live on the index set (or on components), and
    why the pre-revision `⊆_typ`-based irreducibility clause selected
    nothing. -/
theorem iso_invariant_cannot_select {R G T : D}
    (P : D → Prop) (h_inv : ∀ A B : D, iso A B → P A → P B)
    (h_grain : IsGrainOf G R) (h_P : P G) (h_T : iso T R) : P T :=
  h_inv G T (iso_trans _ _ _ h_grain.1 (iso_symm _ _ h_T)) h_P

end GrainTheory.Foundations
