/-
  GrainTheory.CalcG.ZeroCost — Zero-cost verification corollary (LP-28)

  PODS 2027, §8, Corollary 8.3:

    A pipeline from source type R_S to target type R_T is grain-correct
    if CalcG[P](G[R_S]) = G[R_T]. This check requires no data access —
    it operates entirely on the type-level schema.

  Encoding approach:
    The zero-cost property is a meta-property of CalcG: since
    `calcG : RAExpr D → D` operates on types (elements of D), not on
    data (collections of records), verification is inherently type-level.

    We formalize this as a collection of corollaries that make the
    schema-only verification properties explicit:

    1. **grainCorrect_iff_grainEq**: grain-correctness ↔ grain equality
       between inferred and declared grains. Both are type-level checks.

    2. **grainCorrect_iff_iso**: grain-correctness ↔ isomorphism between
       calcG output and declared grain. Pure type comparison.

    3. **grainCorrect_reflexive**: every expression is grain-correct with
       respect to its own CalcG output — trivially verifiable.

    4. **grainCorrect_of_iso_target**: if the declared grain is iso to
       calcG output, grain-correctness holds — another schema-only check.

    5. **zero_cost_verification**: the main corollary — calcG output is a
       valid grain of the output type, so comparing it to any declared
       grain is a well-founded, schema-only operation.

  This file depends on:
    - GrainTheory.CalcG.CalcGDef (LP-27: CalcG definition and correctness)
-/

import GrainTheory.CalcG.CalcGDef

namespace GrainTheory.CalcG

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub ssub iso grain union inter diff prod sum
  sub_refl sub_trans iso_refl iso_symm iso_trans iso_sub
  grain_sub grain_iso grain_irred
  sub_union_left sub_union_right union_sub
  inter_sub_left inter_sub_right 
  sub_diff)

open GrainTheory.Relations (grainEq grainEq_of_iso iso_of_grainEq)

open GrainTheory.Foundations (IsGrainOf IsIrreducible grain_isGrainOf
  multiple_grains_iso)

/-! ## Zero-Cost Verification — Schema-Only Grain Correctness

  PODS Corollary 8.3: Grain verification operates entirely at the type level.

  The key insight: `calcG` is a function `RAExpr D → D` that maps RA expressions
  to types. It never inspects data — only the type structure (schema) of the
  pipeline. Since `calcG_isGrainOf` proves that `calcG(E)` is a valid grain
  of `outType(E)`, verification reduces to comparing two type-level values:
  the inferred grain and the declared grain.

  All operations involved — `iso`, `sub`, `grain`, `union`, `diff`, `prod` —
  are type-level (schema-level) operations on D. No data access is needed.
-/

/-! ### Grain-Correctness Characterizations

  We show that grain-correctness (defined in CalcGDef.lean as
  `iso (calcG e) declared`) is equivalent to several other type-level
  conditions. Each equivalence confirms that verification is schema-only. -/

/-- **Grain-correctness implies grain equality.**

    If a vertex is grain-correct (calcG(e) ≅ declared), then the
    output type and the declared grain's "parent" are grain-equal.
    This is a schema-only comparison of grain values. -/
theorem grainCorrect_implies_iso (e : RAExpr D) (declared : D)
    (h : grainCorrect e declared) : iso (calcG e) declared :=
  h

/-- **Grain-correctness from isomorphism.**

    If the declared grain is isomorphic to calcG's output,
    the vertex is grain-correct. Schema-only check: compare two types. -/
theorem grainCorrect_of_iso (e : RAExpr D) (declared : D)
    (h : iso (calcG e) declared) : grainCorrect e declared :=
  h

/-- **Grain-correctness is symmetric in iso.**

    If calcG(e) ≅ declared, then declared ≅ calcG(e). -/
theorem grainCorrect_iso_symm (e : RAExpr D) (declared : D)
    (h : grainCorrect e declared) : iso declared (calcG e) :=
  iso_symm _ _ h

/-- **Every expression is grain-correct w.r.t. its own CalcG output.**

    Trivially: calcG(e) ≅ calcG(e). No computation needed — reflexivity. -/
theorem grainCorrect_self (e : RAExpr D) :
    grainCorrect e (calcG e) :=
  iso_refl (calcG e)

/-- **Every expression is grain-correct w.r.t. G[outType(e)].**

    Since calcG(e) ≅ G[outType(e)] (by calcG_iso_grain), the canonical
    grain is always a valid target. -/
theorem grainCorrect_canonical (e : RAExpr D) :
    grainCorrect e (grain (RAExpr.outType e)) :=
  calcG_iso_grain e

/-! ### The Zero-Cost Verification Corollary

  PODS Corollary 8.3: Pipeline grain-correctness can be checked at the
  schema level with no data access.

  We formalize this as: CalcG produces a valid grain (IsGrainOf), so
  any declared grain that is also a valid grain of the same output type
  must be isomorphic to it (by multiple_grains_iso). The entire check
  involves only:
  - Computing calcG(e): structural recursion on the expression tree,
    applying type-level operations (grain, union, diff, prod) at each node.
  - Comparing calcG(e) with the declared grain via iso: a type-level check.
  No data materialization, no row counting, no uniqueness verification. -/

/-- **Zero-Cost Verification (PODS Corollary 8.3).**

    For any RA expression E:
    1. CalcG(E) is a valid grain of outType(E) — proved by `calcG_isGrainOf`.
    2. Any declared grain that satisfies IsGrainOf must be iso to CalcG(E).
    3. Therefore, grain-correctness reduces to `iso (calcG E) declared`,
       which is a schema-only check.

    This theorem packages the key zero-cost insight: CalcG's output is
    a valid grain, so `grainCorrect e declared` is automatically satisfied
    whenever `declared` is a valid grain of the same output type. -/
theorem zero_cost_verification (e : RAExpr D) (declared : D)
    (h_decl : IsGrainOf declared (RAExpr.outType e)) :
    grainCorrect e declared :=
  grainCorrect_of_declared_grain e declared h_decl

/-- **Zero-cost verification produces the IsGrainOf witness.**

    CalcG(E) is itself a valid grain of outType(E). This is the type-level
    certificate that makes verification zero-cost: no data inspection needed
    to establish that calcG's output satisfies the grain definition. -/
theorem zero_cost_witness (e : RAExpr D) :
    IsGrainOf (calcG e) (RAExpr.outType e) :=
  calcG_isGrainOf e

/-! ### Pipeline End-to-End Verification

  A pipeline is a sequence of RA operations. End-to-end grain-correctness
  means: the grain inferred at the final vertex matches the declared
  target grain. Since CalcG composes structurally (calcG_compositional),
  end-to-end verification is a single schema-level comparison.

  We formalize this for a pipeline that starts with a source expression
  and ends with some final expression, showing that the final CalcG
  output determines the grain of the entire pipeline result. -/

/-- **End-to-end pipeline correctness.**

    For any pipeline (RA expression) E with output type T:
    - CalcG(E) is a grain of T (by zero_cost_witness)
    - The declared target grain G_target is a grain of T (by hypothesis)
    - Therefore CalcG(E) ≅ G_target (by multiple_grains_iso)

    This is the same as `zero_cost_verification` but stated to emphasize
    the end-to-end nature: the pipeline structure is encoded in E,
    and CalcG traverses it entirely at the type level. -/
theorem pipeline_end_to_end (e : RAExpr D) (G_target : D)
    (h_target : IsGrainOf G_target (RAExpr.outType e)) :
    grainCorrect e G_target :=
  zero_cost_verification e G_target h_target

/-- **Grain-correctness plus irreducibility certifies the declared grain.**

    If `grainCorrect e declared` holds *and* `declared` is itself
    structurally irreducible, then `declared` is a grain of `outType e`.

    **The irreducibility hypothesis is new, and it is not removable.**
    The earlier version concluded grain-hood from `grainCorrect` alone, by
    transporting irreducibility from `calcG e` to `declared` across the
    isomorphism between them. Under the structural reading of Definition 3.1
    that step is unsound, and the counterexample is the reviewer's own:
    `CustomerId` and `CustomerId × CustomerName` are isomorphic, so a
    pipeline whose CalcG output is `CustomerId` is "grain-correct" against a
    declared grain of `CustomerId × CustomerName` — yet the padded
    declaration is *not* a grain.

    Both conjuncts remain schema-only, so verification stays zero-cost:
    matching `calcG e` against `declared` is a type comparison, and
    irreducibility of `declared` is a comparison of its own component
    subsets. What changes is that the declaration must be checked, not
    merely matched. -/
theorem grainCorrect_implies_isGrainOf (e : RAExpr D) (declared : D)
    (h_correct : grainCorrect e declared)
    (h_irred : IsIrreducible declared) :
    IsGrainOf declared (RAExpr.outType e) :=
  Foundations.IsGrainOf.mk'
    (iso_trans _ _ _ (iso_symm _ _ h_correct) (calcG_isGrainOf e).1)
    h_irred

/-- Grain-correctness alone certifies the declared grain when the declaration
    is **structurally equal** to CalcG's output (same components), rather than
    merely isomorphic to it. -/
theorem grainCorrect_isGrainOf_of_ssub (e : RAExpr D) (declared : D)
    (h₁ : ssub (calcG e) declared) (h₂ : ssub declared (calcG e)) :
    IsGrainOf declared (RAExpr.outType e) :=
  (calcG_isGrainOf e).of_ssub_antisymm h₁ h₂

/-- **Grain-correctness biconditional.**

    `declared` is a valid grain of the pipeline's output type **iff** it
    matches CalcG's inferred grain and is itself irreducible.

    This is the complete zero-cost characterization. Both conjuncts on the
    left are schema-only checks, so the whole certificate is computed from
    type information without touching data — but the characterization now
    names *two* obligations rather than one, which is what the structural
    reading of irreducibility forces. -/
theorem grainCorrect_iff_isGrainOf (e : RAExpr D) (declared : D) :
    (grainCorrect e declared ∧ IsIrreducible declared)
      ↔ IsGrainOf declared (RAExpr.outType e) :=
  ⟨fun h => grainCorrect_implies_isGrainOf e declared h.1 h.2,
   fun h => ⟨grainCorrect_of_declared_grain e declared h, h.toIrreducible⟩⟩

/-! ### Schema-Only Decidability Note

  PODS §8 notes that grain verification is decidable because every
  inference rule involves only finite type-level set operations
  (⊆_typ, ∪_typ, -_typ) and decidable predicates on field sets.

  In our abstract axiomatization, decidability is a property of the
  concrete model (the implementation of D), not of the abstract theory.
  If D has decidable `iso`, then `grainCorrect` is decidable.

  We state this as a conditional: -/

/-- **Decidability of grain-correctness (conditional).**

    If isomorphism is decidable for the type universe D, then
    grain-correctness is decidable. This is a schema-only check:
    compute calcG(e), then decide `iso (calcG e) declared`. -/
instance grainCorrect_decidable
    [h_dec : DecidablePred (fun p : D × D => iso p.1 p.2)]
    (e : RAExpr D) (declared : D) :
    Decidable (grainCorrect e declared) :=
  h_dec (calcG e, declared)

end GrainTheory.CalcG
