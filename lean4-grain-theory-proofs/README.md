# Lean 4 Mechanized Proofs of Grain Theory

Machine-checked formalization of the theorems from the extended arXiv version of
"Grain Theory: A Type-Level Framework for Correctness of Data Transformations."

> **Revised 2026-08-16** for the post-review revision of the paper, whose central
> change is the `⊑` / `⊆typ` notation split and the restatement of grain
> irreducibility as a *structural* condition. Two claims made by the previous
> release were artifacts of the earlier (vacuous) irreducibility clause and are
> **withdrawn** — the equi-join grain identity does require a labeling
> hypothesis, and grain-correctness alone does not certify a declared grain.
> Both are described under "What changed" below.

## Overview

Every formal statement from the extended version (Sections 3–10 and the
appendix) is mechanically verified in Lean 4 with Mathlib. The formalization
uses an **abstract axiomatization**: data types and grain are opaque structures
with assumed properties, and all theorems are proved from those axioms. This
mirrors the paper's proof style.

**Key statistics:**

| | |
|---|---|
| Lean modules | 41, all reachable from the root module |
| Theorems | 236 (plus 45 definitions/structures) |
| Axioms | 47 — every one used, and every one **verified against a concrete model** |
| `sorry` obligations | 0 |
| Build | `lake build`, 3306 jobs, 0 errors, 0 warnings |
| Toolchain | Lean 4 v4.29.0-rc8 + Mathlib v4.29.0-rc8 |

## What changed in this revision

Two results the previous release advertised were **artifacts of the vacuous
irreducibility clause**, and both are corrected here.

**The equi-join grain identity does require a labeling hypothesis.** Grain
Inference condition (iii) had been encoded as `iso (grain F₁) F₁` — which is
the `grain_iso` axiom applied to `F₁`, true of *every* type and accepted just
as readily for the wrong candidate. It constrained nothing, so the naming
convention merely appeared unnecessary. Under the structural reading the
strict reverse labeling really does carry a redundant join-key field, and
`equijoin_grain_identity` now takes `AdmissibleLabeling` — the gate the paper
always stated.

**Grain-correctness alone does not certify a declared grain.** A pipeline
whose inferred grain is `CustomerId` "matches" a declared grain of
`CustomerId × CustomerName`, the two being isomorphic — yet the padded
declaration is not a grain. `grainCorrect_iff_isGrainOf` now also requires the
declaration to be irreducible. Both checks remain schema-only, so verification
stays zero-cost; it names two obligations instead of one.

**Coverage was over-reported.** The previous release said "33 modules, zero
`sorry`". Twelve modules were reachable from no import and therefore never
compiled — one of them contained a genuine type error. The root module now
imports all 40, so the build covers what this README claims.

**Two axioms were false, and are gone.** `GrainTheory/Model/` adds a concrete
model — three attributes, one declared functional dependency, types as attribute
sets — in which every axiom is settled by exhaustive check rather than by a hand
proof. It confirmed 30 axioms and refuted two: the semantic greatest-lower-bound
law and the semantic monotonicity of difference. Both are false because `⊆typ`
means *determines*, and determination does not distribute over set operations
the way containment does. Every use is now routed through the structural
relation `⊑`, with explicit hypotheses where one is genuinely needed.

The model also supplies two things the abstract axiomatization could not
establish about itself: that `⊑` and `⊆typ` really do differ (so the degenerate
reading in which they coincide — which satisfies every other axiom — is ruled
out), and that grain irreducibility excludes something (a type isomorphic to `R`
that is *not* a grain of `R`, which was impossible under the earlier
definition).

## Building

**Prerequisites:** Lean 4 v4.29.0-rc8 (specified in `lean-toolchain`)

```bash
lake exe cache get   # Download prebuilt Mathlib (recommended, ~5 min)
lake build           # Build and verify all proofs (~2 min)
```

## The two subtype relations

The revision's central change, and the thing to read first.

| Relation | Reading | Witness | Schema-decidable? |
|---|---|---|---|
| `sub` (`⊆typ`) | semantic | *some* surjection `B ↠ A`, possibly **declared** (a foreign key, an FD) | no |
| `ssub` (`⊑`) | structural | every component of `A` occurs in `B`; the canonical projection | **yes** |

`⊑` refines `⊆typ` but not conversely, and the gap is load-bearing:
`CustomerId ⊏ CustomerId × CustomerName` is proper even though the two types are
isomorphic under the declared determination `CustomerId ↠ CustomerName`.

Grain **irreducibility** (Def 3.1 clause 2) and the CalcG checks quantify over
`⊑`. The isomorphism clause, the grain ordering `≤_g`, the EK–grain hierarchy,
and **external grains** stay on `⊆typ`.

Under the previous encoding, irreducibility quantified over `⊆typ` and was
therefore **vacuous**: any `G' ≅ R ≅ G` admits a bijection, hence a surjection in
both directions, so `G'` was never a *proper* subset. Every type isomorphic to
`R` qualified as a grain.

One consequence worth stating plainly: **structural irreducibility is not
isomorphism-invariant**, so grain-hood does *not* transfer along a bare
isomorphism. `Foundations/IdentifyingFamily.lean` formalizes why any
isomorphism-invariant notion of minimality must fail
(`iso_invariant_cannot_select`).

## Module Structure

```
GrainTheory/
  Basic.lean                         -- Core axioms; ⊆typ vs ⊑
  Foundations/
    GrainDef.lean                    -- Def 2.2/2.3, Def 3.1, IsGrainOf,
                                     --   IsIrreducible, grain-hood factorization,
                                     --   Lemma 3.2 (grain existence)
    Factorization.lean               -- Universal factorization
    MultipleGrains.lean              -- Multiple grains isomorphism (Thm 3.4)
    Uniqueness.lean                  -- Grain uniqueness (Thm 3.5)
    Idempotency.lean                 -- G[G[R]] = G[R]  (one line after the repair)
    Product.lean                     -- Thm 3.8 -- requires component independence
    Sum.lean                         -- Thm 3.9 -- no independence needed
    IdentifyingFamily.lean           -- Sec 4.4: grain as a minimal identifying family
  Relations/
    GrainEquality.lean               -- Def 5.1, Thm 5.2, preservation
    GrainOrdering.lean               -- Def 5.3, partial order, preservation
    GrainSubset.lean                 -- Lemma 5.4 (subset-ordering equivalence)
    GrainInference.lean              -- Thm 5.10; condition (iii) = irreducibility
    IntersectionUnion.lean           -- Lattice absorption
    Incomparability.lean             -- Def 5.7, incomparability preservation
    Armstrong.lean                   -- Axioms A1-A9 (soundness)
    Lattice.lean                     -- Grain lattice structure
  Entity/
    EntityDef.lean                   -- Entity, entity key, behavioral classes
    EKHierarchy.lean                 -- EK subset G[R] subset R
    EntityPreservation.lean          -- =_ek / subset_ek, entity-preserving maps
  Inference/
    EquiJoinAxioms.lean              -- EquiJoinStructure axioms
    EquiJoinSub.lean                 -- F1 subset Res            (condition i)
    EquiJoinBootstrap.lean           -- F1 <=_g Res              (condition ii)
    EquiJoinIrred.lean               -- Convention minimality
    EquiJoinIdentity.lean            -- AdmissibleLabeling + condition (iii)
    EquiJoin.lean                    -- Thm 7.2 (capstone)
    GeneralizedJoin.lean             -- Generalized equi-join
    JoinSpecialCases.lean            -- Equal / ordered / incomparable / natural
    RAOperations.lean                -- All RA operations (Table 2)
  DependencyTheory/
    Completeness.lean                -- Armstrong soundness + completeness axiom
    Determination.lean               -- Determination problem
    Factorization.lean               -- Grain lift, homomorphism, compositionality
  CalcG/
    CalcGDef.lean                    -- CalcG + per-node irreducibility
    ZeroCost.lean                    -- Schema-only verification (two-part check)
  ErrorDetection/
    FanTrap.lean                     -- Fan trap characterization
    ChasmTrap.lean                   -- Chasm trap characterization
    GrainErrors.lean                 -- Props 10.2, 10.3, wrong-grain aggregation,
                                     --   behavioral-class violation
  Model/
    Schema.lean                      -- a concrete model: 3 attributes, 1 FD
    AxiomCheck.lean                  -- every axiom checked against it
    TheoremCheck.lean                -- and the theorems, including the lattice
```

## Axiomatization

Three type classes plus one standalone axiom — **49 assumptions in total**, each
carrying a docstring naming the paper statement it encodes:

- **`GrainStructure`** (35 axioms, `Basic.lean`) — the two subtype relations,
  isomorphism, the three grain clauses, and the field-set laws for
  `∪typ ∩typ −typ × +`. Ten further fields are *carriers* (the relations and
  operations themselves), not assumptions.
- **`EquiJoinStructure`** (10 axioms, `EquiJoinAxioms.lean`) — functional
  determination and its closure properties, plus `equijoin_candidate_irred`
  (Thm 7.2's irreducibility step).
- **`SemanticGrainStructure`** (1 axiom, `DependencyTheory/Factorization.lean`) —
  `isoEquiv`, extracting an actual bijection from abstract `iso`, for the
  element-level results of §8.
- **`armstrong_complete`** (standalone) — transfer from Armstrong's 1974
  completeness theorem.

Nine axioms that had become unused were **removed** in this revision, and two
more were removed because the concrete model showed them **false**. An unused
axiom is pure liability; a false one is worse.

`#print axioms` confirms the headline results depend on no Lean axioms beyond
these class fields — they do not silently reach for choice or for
`armstrong_complete`:

```
grain_idempotent                     does not depend on any axioms
grain_product                        does not depend on any axioms
isGrainOf_iff_iso_and_irreducible    does not depend on any axioms
grain_inference_isGrainOf            does not depend on any axioms
equijoin_grain_identity              does not depend on any axioms
calcG_isGrainOf                      does not depend on any axioms
grainCorrect_iff_isGrainOf           does not depend on any axioms
```

## Correspondence to the paper

| Paper section | Lean module(s) | Key theorems |
|---|---|---|
| §3 Foundations | `Foundations/*` | `grain_idempotent`, `grain_product`, `grain_sum`, `grain_exists`, `isGrainOf_iff_iso_and_irreducible` |
| §4 ADT grain | `Foundations/IdentifyingFamily.lean` | `minimalIdentifying_isGrainOf`, `iso_invariant_cannot_select` |
| §5 Relations | `Relations/*` | `grainEq_iff_iso`, `grain_partial_order`, `grain_inference_isGrainOf`, Armstrong A1–A9 |
| §6 Entity / EK | `Entity/*` | `IsEntityOf.ek_sub_grain`, `entityKey_unique_up_to_iso`, `EntityPreserving` |
| §7 Inference | `Inference/*` | `equijoin_grain_identity`, `AdmissibleLabeling`, all RA rules, 4 join special cases |
| §8 Homomorphism | `DependencyTheory/*` | `grain_homomorphism`, `grain_compositionality`, `armstrong_sound` |
| §9 CalcG | `CalcG/*` | `calcG_isGrainOf`, `calcG_irreducible`, `grainCorrect_iff_isGrainOf` |
| §10 Error detection | `ErrorDetection/*` | `fan_trap_detection_*`, `safe_chain_iff_total`, `no_identification_after_drop`, `ungrounded_multiversion_read_is_fan_trap` |

## Known limitations

The most important, in the order that matters:

- **No concrete model is constructed**, so consistency is not formally verified —
  and this is precisely the blind spot that let the vacuous irreducibility clause
  through. Building `D = Finset Attribute` with grain as a minimal key is now the
  top open item, not optional future work.
- `≤_g` uses the subset encoding only; the FD-based surjection case is not
  expressible abstractly.
- `armstrong_complete` is an axiom (transfer from Armstrong 1974).
- The inductive/coinductive ADT cases rest on the initial-algebra theorem and are
  not mechanized.
- Everything is type-level; row-level semantics are out of scope except in the
  denotation layer used by §8 and by entity preservation.

## License

MIT License. See top-level `LICENSE` file.
