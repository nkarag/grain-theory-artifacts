/-
  GrainTheory.Foundations.Idempotency — Grain operator idempotency

  arXiv Theorem 3.7: G[G[R]] ≅ G[R] for all data types R.

  **Simplified by the structural repair.** The earlier proof ran the paper's
  contradiction argument by hand: G[G[R]] ⊆_typ G[R], G[G[R]] ≅ R, then
  irreducibility of G[R] and antisymmetry. That argument needed G[G[R]] to be
  a *subset* of G[R] — which, under the structural reading, is not something
  the axioms supply (the grain operator may pick an external grain).

  Since grain-hood now factors as "isomorphic + irreducible"
  (`isGrainOf_iff_iso_and_irreducible`), idempotency is instead an immediate
  instance of Multiple Grains Isomorphism: G[G[R]] and G[R] are *both* grains
  of G[R] — the first by the grain axioms, the second because G[R] is
  irreducible, hence a grain of itself. No containment argument is needed.
-/

import GrainTheory.Foundations.GrainDef
import GrainTheory.Foundations.MultipleGrains

namespace GrainTheory.Foundations

variable {D : Type*} [GrainStructure D]

open GrainStructure

/-- arXiv Theorem 3.7: Grain operator idempotency. G[G[R]] ≅ G[R].

  Proof: G[R] is irreducible (`grain_irreducible`), hence a grain of itself.
  G[G[R]] is a grain of G[R] by the grain axioms. Two grains of the same type
  are isomorphic (`multiple_grains_iso`). -/
theorem grain_idempotent (R : D) : iso (grain (grain R)) (grain R) :=
  multiple_grains_iso (grain_isGrainOf (grain R)) (grain_irreducible R).self_grain

/-- The grain of the grain is itself a grain of R.

  Isomorphism by transitivity; irreducibility is inherited directly, since
  under the structural reading irreducibility is a property of the type
  itself and does not have to be re-derived relative to R. -/
theorem grain_grain_isGrainOf (R : D) : IsGrainOf (grain (grain R)) R :=
  IsGrainOf.mk'
    (iso_trans _ _ _ (grain_iso (grain R)) (grain_iso R))
    (grain_irreducible (grain R))

end GrainTheory.Foundations
