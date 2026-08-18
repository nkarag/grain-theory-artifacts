/-
  GrainTheory.CalcG.CalcGDef — CalcG definition and correctness (LP-27)

  PODS 2027, §8, Definition 8.1 and Theorem 8.2:

    CalcG is the grain inference algorithm that traverses a pipeline DAG
    in topological order, applying the corresponding RA inference rule at
    each vertex to compute the grain of the result.

    **Correctness:** For any RA expression E, CalcG(E) correctly computes
    the grain of the result — i.e., the inferred grain matches the
    semantic grain obtained by applying the inference rules.

  Encoding approach:
    We define an inductive type `RAExpr` for relational algebra expressions
    over an abstract type universe D. Each constructor carries the hypotheses
    needed by the corresponding inference rule (schema constraints, subset
    relations, etc.). The function `calcG` computes the inferred grain by
    structural recursion, and `calcG_correct` proves by structural induction
    that the result is isomorphic to the grain of the output type.

  This file depends on:
    - GrainTheory.Inference.RAOperations (LP-24: all RA rules proven)
    - GrainTheory.Inference.EquiJoin (LP-21: equi-join grain inference)
-/

import GrainTheory.Inference.RAOperations
import GrainTheory.Inference.EquiJoin

namespace GrainTheory.CalcG

variable {D : Type*} [EquiJoinStructure D]

open GrainStructure (sub ssub indep iso grain union inter diff prod sum
  sub_refl sub_trans iso_refl iso_symm iso_trans iso_sub
  grain_sub grain_iso grain_irred
  sub_union_left sub_union_right union_sub
  inter_sub_left inter_sub_right sub_inter
  sub_diff)

open EquiJoinStructure (determines determines_iso_of_sub)

open GrainTheory.Relations (grainEq grainEq_of_iso)

open GrainTheory.Foundations (IsGrainOf IsIrreducible grain_isGrainOf
  grain_irreducible multiple_grains_iso)

/-! ## RA Expression Type

  An inductive type representing relational algebra expressions.
  Each constructor carries:
  1. The sub-expression(s) it operates on
  2. The output type `Res`
  3. The schema hypotheses required by the corresponding inference rule

  **Design choice:** We include the schema constraints as fields in the
  inductive type (bundled approach). This means an `RAExpr` is only
  constructible when the schema constraints hold, which simplifies the
  correctness proof — each constructor's hypotheses exactly match what
  the corresponding inference rule theorem requires.

  The type `D` of the expression is the output type of that expression.
-/

/-- A relational algebra expression over the type universe D.
    Each constructor represents an RA operation applied to sub-expressions.

    `Source R` is a base relation with given type R.
    All other constructors take sub-expression(s) and produce a result type
    with appropriate schema constraints. -/
inductive RAExpr (D : Type*) [EquiJoinStructure D] : Type _ where
  /-- Base case: a source relation with type R. -/
  | Source (R : D) : RAExpr D
  /-- Selection σ_θ: filters rows, type unchanged.
      Res ≅ R (output iso to input). -/
  | Selection (e : RAExpr D) (R Res : D) (h_iso : iso Res R) : RAExpr D
  /-- Projection π_S: project onto S, when the grain survives.
      `S ⊑ R` and `G[R] ⊑ S` — both structural, as the appendix states them:
      the projection keeps a sub-set of R's columns, and every grain
      *component* is among those kept.
      The structural test is the schema-decidable one CalcG performs
      (arXiv Table 2); it is sound but conservative, so a projection that
      keeps the grain only via an alternative key is not constructible here
      (`grain_projection` covers that case with the exact condition). -/
  | Projection (e : RAExpr D) (R S : D)
      (h_SR : ssub S R) (h_GS : ssub (grain R) S) : RAExpr D
  /-- Extension ε: add computed column D = f(R).
      Res ≅ R × D_ext, and R × D_ext ≅ R (D is functionally determined). -/
  | Extension (e : RAExpr D) (R D_ext Res : D)
      (h_res : iso Res (prod R D_ext)) (h_det : iso (prod R D_ext) R) : RAExpr D
  /-- Rename ρ_{a→b}: rename attributes, type isomorphic.
      Res ≅ R. -/
  | Rename (e : RAExpr D) (R Res : D) (h_iso : iso Res R) : RAExpr D
  /-- Grouping γ_{G_c, agg}: group by G_c with aggregation.
      G_c is a grain of Res by construction. -/
  | Grouping (e : RAExpr D) (_R : D) (G_c Res : D)
      (h_grain : IsGrainOf G_c Res) : RAExpr D
  /-- Set operations ∪, ∩, −: union-compatible inputs.
      Res ≅ R (same type). -/
  | SetOp (e₁ e₂ : RAExpr D) (R Res : D) (h_iso : iso Res R) : RAExpr D
  /-- Theta join ⋈_θ: cross product filtered by θ.
      Res type is R₁ × R₂. Requires the inputs to be **independent** — no
      determination declared across them — which is the hypothesis of the
      Grain of Product Types theorem (arXiv Thm 3.8). Without it the product
      of grains is reducible and the rule over-reports. -/
  | ThetaJoin (e₁ e₂ : RAExpr D) (R₁ R₂ : D) (h_indep : indep R₁ R₂) : RAExpr D
  /-- Semi-join ⋉: returns rows from R₁ matching R₂.
      Res ≅ R₁ (type unchanged). -/
  | SemiJoin (e₁ e₂ : RAExpr D) (R₁ _R₂ Res : D) (h_iso : iso Res R₁) : RAExpr D
  /-- Anti-join ▷: returns rows from R₁ not matching R₂.
      Res ≅ R₁ (type unchanged). -/
  | AntiJoin (e₁ e₂ : RAExpr D) (R₁ _R₂ Res : D) (h_iso : iso Res R₁) : RAExpr D
  /-- Equi-join ⋈_{Jk}: join on join key Jk.
      Carries schema constraints: Jk ⊆ R₁, Jk ⊆ R₂,
      Res ↔ (R₁ \ Jk) × (R₂ \ Jk) × Jk (mutual containment). -/
  | EquiJoin (e₁ e₂ : RAExpr D) (R₁ R₂ Jk Res : D)
      (h_jk_r1 : ssub Jk R₁) (h_jk_r2 : ssub Jk R₂)
      (h_res_sub : sub Res (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk))
      (h_res_sup : sub (prod (prod (diff R₁ Jk) (diff R₂ Jk)) Jk) Res)
      (h_adm : Inference.AdmissibleLabeling R₁ R₂ Jk) : RAExpr D

/-! ## Output Type Function

  Maps each RA expression to its output type (the type of data it produces).
  This is the semantic type of the expression's result. -/

/-- The output (result) type of an RA expression. -/
def RAExpr.outType {D : Type*} [EquiJoinStructure D] : RAExpr D → D
  | .Source R => R
  | .Selection _ _ Res _ => Res
  | .Projection _ _ S _ _ => S
  | .Extension _ _ _ Res _ _ => Res
  | .Rename _ _ Res _ => Res
  | .Grouping _ _ _ Res _ => Res
  | .SetOp _ _ _ Res _ => Res
  | .ThetaJoin _ _ R₁ R₂ _ => prod R₁ R₂
  | .SemiJoin _ _ _ _ Res _ => Res
  | .AntiJoin _ _ _ _ Res _ => Res
  | .EquiJoin _ _ _ _ _ Res _ _ _ _ _ => Res

/-! ## CalcG Function

  Computes the inferred grain of an RA expression by structural recursion.
  At each node, CalcG applies the formula from the corresponding RA
  inference rule to the grain(s) of its input(s).

  This mirrors PODS Definition 8.1: CalcG traverses the expression tree
  (the DAG's topological order corresponds to structural recursion),
  applying the inference rule at each vertex. -/

/-- **CalcG (PODS Definition 8.1).**

    Computes the inferred grain of an RA expression by structural recursion.
    Each case applies the grain formula from the corresponding inference rule:

    - Source: grain is given (base annotation)
    - Selection, SetOp, SemiJoin, AntiJoin: grain unchanged (type-preserved ops)
    - Projection: grain unchanged when grain fields survive
    - Extension: grain unchanged (determined column adds no information)
    - Rename: grain unchanged (structural identity)
    - Grouping: grain is the grouping key G_c
    - ThetaJoin: grain is the product of input grains
    - EquiJoin: grain is G[R₁] ∪_typ (G[R₂] -_typ Jk) -/
def calcG {D : Type*} [EquiJoinStructure D] : RAExpr D → D
  -- Base case: source relation
  | .Source R => grain R
  -- Type-unchanged operations: grain of input
  | .Selection _e R _ _ => grain R
  | .Projection _e R _ _ _ => grain R
  | .Extension _e R _ _ _ _ => grain R
  | .Rename _e R _ _ => grain R
  -- Grouping: grain is G_c
  | .Grouping _ _ G_c _ _ => G_c
  -- Set operations: grain of (either) input
  | .SetOp _e₁ _ R _ _ => grain R
  -- Theta join: product of grains
  | .ThetaJoin _ _ R₁ R₂ _ => prod (grain R₁) (grain R₂)
  -- Semi-join / Anti-join: grain of R₁
  | .SemiJoin _ _ R₁ _ _ _ => grain R₁
  | .AntiJoin _ _ R₁ _ _ _ => grain R₁
  -- Equi-join: CalcG formula
  | .EquiJoin _ _ R₁ R₂ Jk _ _ _ _ _ _ =>
      union (grain R₁) (diff (grain R₂) Jk)

/-! ## CalcG Correctness Theorem

  **PODS Theorem 8.2:** CalcG correctly computes the grain of the result
  of any RA expression.

  We prove this in two forms:
  1. `calcG_iso_grain`: CalcG(E) ≅ G[outType(E)] — the inferred grain is
     isomorphic to the actual grain of the output type.
  2. `calcG_isGrainOf`: IsGrainOf (CalcG(E)) (outType(E)) — stronger:
     the inferred grain satisfies the grain definition (iso + irreducible).

  The proof is by structural induction on the expression. Each case
  reduces to the corresponding inference rule theorem from LP-24 or LP-21.
-/

/-- **CalcG Correctness — Grain Isomorphism (PODS Theorem 8.2, weak form).**

    For any RA expression E:
      calcG(E) ≅ G[outType(E)]

    i.e., the grain inferred by CalcG is isomorphic to the actual grain
    of the expression's output type.

    Proof by structural induction on E. Each case applies the corresponding
    RA inference rule theorem. -/
theorem calcG_iso_grain : ∀ (e : RAExpr D), iso (calcG e) (grain (RAExpr.outType e))
  -- Base case: Source R → calcG = G[R] ≅ G[R]
  | .Source R => iso_refl (grain R)
  -- Selection: calcG = G[R], outType = Res, Res ≅ R
  -- By grain_selection: G[Res] ≅ G[R], so G[R] ≅ G[Res]
  | .Selection _ R Res h_iso =>
    iso_symm _ _ (Inference.grain_selection R Res h_iso)
  -- Projection: calcG = G[R], outType = S
  -- By grain_projection: G[S] ≅ G[R], so G[R] ≅ G[S]
  | .Projection _ R S h_SR h_GS =>
    iso_symm _ _ (Inference.grain_projection_structural R S h_SR h_GS)
  -- Extension: calcG = G[R], outType = Res
  -- By grain_extension: G[Res] ≅ G[R], so G[R] ≅ G[Res]
  | .Extension _ R D_ext Res h_res h_det =>
    iso_symm _ _ (Inference.grain_extension R D_ext Res h_res h_det)
  -- Rename: calcG = G[R], outType = Res
  -- By grain_rename: G[Res] ≅ G[R] (grainEq Res R), so G[R] ≅ G[Res]
  | .Rename _ R Res h_iso =>
    iso_symm _ _ (Inference.grain_rename R Res h_iso)
  -- Grouping: calcG = G_c, outType = Res
  -- By grain_grouping: G[Res] ≅ G_c, so G_c ≅ G[Res]
  | .Grouping _ _R G_c Res h_grain =>
    iso_symm _ _ (Inference.grain_grouping G_c Res h_grain)
  -- Set operations: calcG = G[R], outType = Res
  -- By grain_set_ops: G[Res] ≅ G[R], so G[R] ≅ G[Res]
  | .SetOp _ _ R Res h_iso =>
    iso_symm _ _ (Inference.grain_set_ops R Res h_iso)
  -- Theta join: calcG = G[R₁] × G[R₂], outType = R₁ × R₂
  -- By grain_theta_join: G[R₁ × R₂] ≅ G[R₁] × G[R₂]
  | .ThetaJoin _ _ R₁ R₂ h_indep =>
    iso_symm _ _ (Inference.grain_theta_join R₁ R₂ h_indep)
  -- Semi-join: calcG = G[R₁], outType = Res
  -- By grain_semijoin: G[Res] ≅ G[R₁], so G[R₁] ≅ G[Res]
  | .SemiJoin _ _ R₁ _R₂ Res h_iso =>
    iso_symm _ _ (Inference.grain_semijoin R₁ Res h_iso)
  -- Anti-join: calcG = G[R₁], outType = Res
  -- By grain_antijoin: G[Res] ≅ G[R₁], so G[R₁] ≅ G[Res]
  | .AntiJoin _ _ R₁ _R₂ Res h_iso =>
    iso_symm _ _ (Inference.grain_antijoin R₁ Res h_iso)
  -- Equi-join: calcG = G[R₁] ∪ (G[R₂] \ Jk), outType = Res
  -- By equijoin_grain_identity: IsGrainOf F₁ Res → F₁ ≅ Res
  -- Then F₁ ≅ Res → G[F₁] ≅ G[Res] (grainEq_of_iso)
  -- And F₁ has G[F₁] ≅ F₁ (from equijoin_candidate_idempotent)
  -- So F₁ ≅ G[F₁] ≅ G[Res]
  | .EquiJoin _ _ R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup h_adm => by
    set F₁ := union (grain R₁) (diff (grain R₂) Jk)
    have h_identity : IsGrainOf F₁ Res :=
      Inference.equijoin_grain_identity R₁ R₂ Jk Res h_jk_r1 h_jk_r2 h_res_sub h_res_sup h_adm
    -- F₁ ≅ Res
    have h_F1_Res : iso F₁ Res := h_identity.1
    -- G[F₁] ≅ G[Res] (PODS Thm 4.2)
    have h_gF1_gRes : iso (grain F₁) (grain Res) :=
      grainEq_of_iso h_F1_Res
    -- G[F₁] ≅ F₁ (equi-join candidate idempotent)
    have h_idem : iso (grain F₁) F₁ :=
      Inference.equijoin_candidate_idempotent R₁ R₂ Jk h_adm
    -- F₁ ≅ G[F₁] ≅ G[Res]
    exact iso_trans _ _ _ (iso_symm _ _ h_idem) h_gF1_gRes

/-- **CalcG output is structurally irreducible.**

    Proved by case analysis on the expression: at every RA node, the grain
    CalcG produces is irreducible *for a reason specific to that operation*.

    This replaces the earlier argument, which derived irreducibility of
    `calcG e` by transporting it across the isomorphism
    `calcG e ≅ G[outType e]`. That transport is unsound once irreducibility
    is structural — an isomorphism carries no information about components.
    The obligation therefore has to be discharged node by node, and two nodes
    genuinely need a side condition to discharge it:

    - **ThetaJoin** needs the inputs to be independent (arXiv Thm 3.8);
    - **EquiJoin** needs an admissible labeling (arXiv Thm 7.2).

    Both are now carried by the corresponding `RAExpr` constructors, so an
    ill-conditioned pipeline is not constructible. This is the mechanized
    form of the claim that CalcG's checks are schema-decidable: each side
    condition is a comparison of component sets. -/
theorem calcG_irreducible : ∀ (e : RAExpr D), IsIrreducible (calcG e)
  -- Source: the declared grain of the base relation is irreducible.
  | .Source R => grain_irreducible R
  -- Type-preserving operations: the grain is the input's grain.
  | .Selection _ R _ _ => grain_irreducible R
  | .Projection _ R _ _ _ => grain_irreducible R
  | .Extension _ R _ _ _ _ => grain_irreducible R
  | .Rename _ R _ _ => grain_irreducible R
  | .SetOp _ _ R _ _ => grain_irreducible R
  | .SemiJoin _ _ R₁ _ _ _ => grain_irreducible R₁
  | .AntiJoin _ _ R₁ _ _ _ => grain_irreducible R₁
  -- Grouping: the grouping key is a grain of the result by construction.
  | .Grouping _ _ _ _ h_grain => h_grain.toIrreducible
  -- Theta join: product of independent irreducible grains (Thm 3.8).
  | .ThetaJoin _ _ R₁ R₂ h_indep =>
    (Foundations.prod_grain_isGrainOf R₁ R₂ h_indep).toIrreducible
  -- Equi-join: the candidate is irreducible under an admissible labeling
  -- (Thm 7.2). This is informational independence (Def 6.2).
  | .EquiJoin _ _ R₁ R₂ Jk _ _ _ _ _ h_adm =>
    Inference.equijoin_candidate_irreducible R₁ R₂ Jk h_adm

/-- **CalcG Correctness — Grain Identity (arXiv Theorem 9.2, strong form).**

    For any RA expression E:
      IsGrainOf (calcG E) (outType E)

    i.e. CalcG(E) is a grain of the output type: it satisfies both the
    isomorphism clause and structural irreducibility.

    The isomorphism comes from `calcG_iso_grain`; irreducibility from
    `calcG_irreducible`. Grain-hood factors into exactly these two
    (`isGrainOf_iff_iso_and_irreducible`), so the two halves compose
    directly. -/
theorem calcG_isGrainOf (e : RAExpr D) :
    IsGrainOf (calcG e) (RAExpr.outType e) :=
  Foundations.IsGrainOf.mk'
    (iso_trans _ _ _ (calcG_iso_grain e) (grain_iso (RAExpr.outType e)))
    (calcG_irreducible e)

/-! ## Sequential Composition

  PODS §8 states that for sequential composition, CalcG is function composition:
    CalcG[op₁ ; op₂](G_in) = CalcG[op₂](CalcG[op₁](G_in))

  In our structural recursion encoding, this is built into the definition:
  sub-expressions are processed first (by structural recursion), and their
  grains feed into the parent expression. This theorem makes the compositional
  property explicit.
-/

/-- **Sequential Composition.**

    CalcG naturally composes: the grain of a compound expression depends only
    on the grains of its sub-expressions' output types, which are computed
    recursively. This is a direct consequence of the structural recursion
    definition.

    Formally: for any expression E with output type T, CalcG(E) ≅ G[T].
    This means CalcG's output is independent of the internal structure of
    sub-expressions — only their output types matter. -/
theorem calcG_compositional (e : RAExpr D) :
    iso (calcG e) (grain (RAExpr.outType e)) :=
  calcG_iso_grain e

/-! ## Grain Correctness of Pipelines

  A pipeline vertex is grain-correct if the inferred grain matches the
  declared grain annotation. A pipeline is grain-correct if every vertex is.

  CalcG enables zero-cost verification: checking grain-correctness requires
  only schema information (type-level operations), no data access.
-/

/-- A vertex is grain-correct when its CalcG-inferred grain matches
    the declared grain annotation. -/
def grainCorrect (e : RAExpr D) (declared : D) : Prop :=
  iso (calcG e) declared

/-- The grain-correctness check is well-founded: CalcG produces a valid
    grain, so comparing it to the declared grain is meaningful.

    If the declared grain is also a valid grain (IsGrainOf declared outType),
    then grain-correctness is equivalent to the two grains being isomorphic.

    PODS justification: two grains of the same type are always isomorphic
    (Theorem 3.3 — multiple_grains_iso). -/
theorem grainCorrect_of_declared_grain (e : RAExpr D) (declared : D)
    (h_decl : IsGrainOf declared (RAExpr.outType e)) :
    grainCorrect e declared := by
  unfold grainCorrect
  -- calcG(e) is a grain of outType(e)
  have h_calc := calcG_isGrainOf e
  -- Two grains of the same type are isomorphic
  exact multiple_grains_iso h_calc h_decl

end GrainTheory.CalcG
