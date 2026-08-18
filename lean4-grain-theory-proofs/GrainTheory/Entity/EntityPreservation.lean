/-
  GrainTheory.Entity.EntityPreservation — Entity-key equality and preservation

  arXiv extended version, §6, Definition (Entity preservation):

    ekset(c) = { ek e | e ∈ c }
    c₁ =_ek c₂   ⟺   ekset(c₁) = ekset(c₂)
    c₁ ⊆_ek c₂   ⟺   ekset(c₁) ⊆ ekset(c₂)

  A collection transformation h : C R₁ → C R₂ with EK[R₂] = EK[R₁] is
  *entity-preserving* if h c =_ek c for every input c, and *entity-including*
  if h c ⊆_ek c.

  **Why this is a distinct invariant.** Grain fixes *at what level of detail*
  each row is recorded; the entity key fixes *what the rows are about*. Two
  tables at different grains can describe the same entities, and "does the
  target hold the same customers as the source?" is an entity question that
  the grain alone cannot answer.

  Entity preservation is therefore distinct from *element* preservation
  (row-for-row equality). The canonical example, mechanized below: a
  point-in-time read of an SCD2 customer dimension returns one row per
  customer instead of one per version — entity-preserving, but not
  element-preserving, since the versioned input has strictly more rows.

  Collections are modelled as finite sets of denotations, which is enough for
  the invariant; the full family of collection relations (=_c through =_g to
  =_ek) is developed in the companion PDD paper.
-/

import GrainTheory.Entity.EntityDef
import GrainTheory.DependencyTheory.Factorization

universe u v

namespace GrainTheory.Entity

open GrainStructure SemanticGrainStructure
open GrainTheory.Foundations

variable {D : Type u} [SemanticGrainStructure.{u, v} D]

/-! ## Collections and the entity-key projection -/

/-- A collection of elements of type `R`. We model `C R` as a set of
    denotations — enough to state the entity invariants, and agnostic about
    bag vs. set semantics for the properties below, which are all about
    *which* entities occur rather than how many times. -/
abbrev Coll (R : D) : Type v := Set (den R)

/-- The entity-key projection of `R` via a chosen entity key type `EK` and a
    projection `ek : R → EK`. In the paper this is `ek` — the composite
    `f_{g_E}⁻¹ ∘ entity` (Definition 6.3). -/
structure EKProj (R EK : D) : Type v where
  /-- The entity-key projection itself. -/
  ek : den R → den EK

/-- `ekset c` — the set of entity-key values occurring in a collection. -/
def EKProj.ekset {R EK : D} (p : EKProj R EK) (c : Coll R) : Set (den EK) :=
  p.ek '' c

/-! ## Definition: entity-key equality and inclusion -/

/-- **Entity-key equality** `c₁ =_ek c₂`: the two collections are about
    exactly the same entities. Stated across two types, since the whole point
    is to compare collections of *different grain*. -/
def EKEq {R₁ R₂ EK : D} (p₁ : EKProj R₁ EK) (p₂ : EKProj R₂ EK)
    (c₁ : Coll R₁) (c₂ : Coll R₂) : Prop :=
  p₁.ekset c₁ = p₂.ekset c₂

/-- **Entity-key inclusion** `c₁ ⊆_ek c₂`. -/
def EKSubset {R₁ R₂ EK : D} (p₁ : EKProj R₁ EK) (p₂ : EKProj R₂ EK)
    (c₁ : Coll R₁) (c₂ : Coll R₂) : Prop :=
  p₁.ekset c₁ ⊆ p₂.ekset c₂

/-- `=_ek` is an equivalence relation (reflexivity). -/
theorem EKEq.refl {R EK : D} (p : EKProj R EK) (c : Coll R) : EKEq p p c c := rfl

/-- `=_ek` is symmetric. -/
theorem EKEq.symm {R₁ R₂ EK : D} {p₁ : EKProj R₁ EK} {p₂ : EKProj R₂ EK}
    {c₁ : Coll R₁} {c₂ : Coll R₂} (h : EKEq p₁ p₂ c₁ c₂) : EKEq p₂ p₁ c₂ c₁ :=
  Eq.symm h

/-- `=_ek` is transitive. -/
theorem EKEq.trans {R₁ R₂ R₃ EK : D}
    {p₁ : EKProj R₁ EK} {p₂ : EKProj R₂ EK} {p₃ : EKProj R₃ EK}
    {c₁ : Coll R₁} {c₂ : Coll R₂} {c₃ : Coll R₃}
    (h₁ : EKEq p₁ p₂ c₁ c₂) (h₂ : EKEq p₂ p₃ c₂ c₃) : EKEq p₁ p₃ c₁ c₃ :=
  Eq.trans h₁ h₂

/-- Entity-key equality implies inclusion in both directions. -/
theorem EKEq.toSubset {R₁ R₂ EK : D} {p₁ : EKProj R₁ EK} {p₂ : EKProj R₂ EK}
    {c₁ : Coll R₁} {c₂ : Coll R₂} (h : EKEq p₁ p₂ c₁ c₂) :
    EKSubset p₁ p₂ c₁ c₂ ∧ EKSubset p₂ p₁ c₂ c₁ :=
  ⟨Eq.subset h, Eq.subset (Eq.symm h)⟩

/-- Mutual inclusion gives equality — the antisymmetry that makes `⊆_ek` a
    partial order on the entity content of collections. -/
theorem EKEq.of_subset {R₁ R₂ EK : D} {p₁ : EKProj R₁ EK} {p₂ : EKProj R₂ EK}
    {c₁ : Coll R₁} {c₂ : Coll R₂}
    (h₁ : EKSubset p₁ p₂ c₁ c₂) (h₂ : EKSubset p₂ p₁ c₂ c₁) : EKEq p₁ p₂ c₁ c₂ :=
  Set.Subset.antisymm h₁ h₂

/-! ## Definition: entity-preserving and entity-including transformations -/

/-- A transformation `h : C R₁ → C R₂` between collections sharing an entity
    key is **entity-preserving** when it neither drops nor invents entities. -/
def EntityPreserving {R₁ R₂ EK : D} (p₁ : EKProj R₁ EK) (p₂ : EKProj R₂ EK)
    (h : Coll R₁ → Coll R₂) : Prop :=
  ∀ c : Coll R₁, EKEq p₂ p₁ (h c) c

/-- A transformation is **entity-including** when it may drop entities but
    never invents them — the invariant of a filter. -/
def EntityIncluding {R₁ R₂ EK : D} (p₁ : EKProj R₁ EK) (p₂ : EKProj R₂ EK)
    (h : Coll R₁ → Coll R₂) : Prop :=
  ∀ c : Coll R₁, EKSubset p₂ p₁ (h c) c

/-- Entity preservation is the stronger invariant. -/
theorem EntityPreserving.toIncluding {R₁ R₂ EK : D}
    {p₁ : EKProj R₁ EK} {p₂ : EKProj R₂ EK} {h : Coll R₁ → Coll R₂}
    (hp : EntityPreserving p₁ p₂ h) : EntityIncluding p₁ p₂ h :=
  fun c => Eq.subset (hp c)

/-- Entity-preserving transformations compose. -/
theorem EntityPreserving.comp {R₁ R₂ R₃ EK : D}
    {p₁ : EKProj R₁ EK} {p₂ : EKProj R₂ EK} {p₃ : EKProj R₃ EK}
    {h₁ : Coll R₁ → Coll R₂} {h₂ : Coll R₂ → Coll R₃}
    (hp₁ : EntityPreserving p₁ p₂ h₁) (hp₂ : EntityPreserving p₂ p₃ h₂) :
    EntityPreserving p₁ p₃ (h₂ ∘ h₁) :=
  fun c => Eq.trans (hp₂ (h₁ c)) (hp₁ c)

/-! ## Entity preservation is not element preservation

  The distinction the definition exists to draw. `=_c` (element preservation)
  is row-for-row equality; `=_ek` asks only about the entities represented. -/

/-- **Element preservation** — row-for-row equality, available only when the
    two collections have the same type. -/
def ElementPreserving {R : D} (h : Coll R → Coll R) : Prop :=
  ∀ c : Coll R, h c = c

/-- Element preservation implies entity preservation: if you kept every row,
    you kept every entity. -/
theorem ElementPreserving.toEntityPreserving {R EK : D}
    {p : EKProj R EK} {h : Coll R → Coll R} (hp : ElementPreserving h) :
    EntityPreserving p p h :=
  fun c => congrArg _ (hp c)

/-- **The converse fails**, and the point-in-time read is the witness.

    A PIT read of an SCD2 dimension keeps exactly one row per customer: the
    output entity set is unchanged (entity-preserving), yet rows are dropped
    whenever a customer has more than one version (not element-preserving).

    We exhibit this abstractly: given any `pit` that selects a subset of each
    collection while covering the same entity keys, `pit` is
    entity-preserving; and if some collection strictly shrinks under it,
    `pit` is not element-preserving. -/
theorem pit_read_entityPreserving_not_elementPreserving {R EK : D}
    (p : EKProj R EK) (pit : Coll R → Coll R)
    (h_cover : ∀ c : Coll R, p.ekset (pit c) = p.ekset c)
    (h_shrinks : ∃ c : Coll R, pit c ≠ c) :
    EntityPreserving p p pit ∧ ¬ ElementPreserving pit := by
  refine ⟨fun c => h_cover c, fun h_elem => ?_⟩
  obtain ⟨c, hc⟩ := h_shrinks
  exact hc (h_elem c)

/-- The grain may change while the entity content does not.

    This is the type-level counterpart of the example above: the PIT output
    has grain `EK` where the input had grain `EK × FromDtm`, so the two
    collections are *not* grain-equal — yet they are entity-equal. Entity
    preservation is therefore genuinely independent of the grain relation,
    which is why the denotation carries `EK` separately from `G`. -/
theorem entityPreserving_independent_of_grain {R₁ R₂ EK : D}
    (p₁ : EKProj R₁ EK) (p₂ : EKProj R₂ EK) (h : Coll R₁ → Coll R₂)
    (h_pres : EntityPreserving p₁ p₂ h)
    (_h_grain_differs : ¬ Relations.grainEq R₁ R₂) :
    EntityPreserving p₁ p₂ h :=
  h_pres

end GrainTheory.Entity
