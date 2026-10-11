/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252ComplexPhaseEliminationIdeal
import Biunimodular.F11.H252ComplexRootCount
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

/-- The root lifts give distinct points of the original ten-equation scheme:
their actual tenth coordinates recover the root. -/
def h252ComplexPhaseRootEmbedding :
    h252KComplex.rootSet ℂ ↪ (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ) := by
  classical
  have lift (k : h252KComplex.rootSet ℂ) :
      ∃ g : H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ,
        g (h252ComplexPhaseKCoordinate X) = k.val := by
    apply h252ComplexPhaseKCoordinate_root_lift
    simpa only [Polynomial.IsRoot, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using
      Polynomial.aeval_eq_zero_of_mem_rootSet k.property
  refine ⟨fun k => (lift k).choose, ?_⟩
  intro k l h
  apply Subtype.ext
  calc
    k.val = (lift k).choose (h252ComplexPhaseKCoordinate X) := (lift k).choose_spec.symm
    _ = (lift l).choose (h252ComplexPhaseKCoordinate X) := congrArg
      (fun g : H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ => g (h252ComplexPhaseKCoordinate X)) h
    _ = l.val := (lift l).choose_spec

/-- A family of 252 pairwise distinct complex points of the original scheme.
Exhaustion of the scheme requires the separate reverse RUR identities. -/
theorem h252ComplexPhase_has_252_distinct_points :
    ∃ f : Fin 252 → (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ), Function.Injective f := by
  classical
  have hc : Fintype.card (h252KComplex.rootSet ℂ) = 252 := by
    rw [← Nat.card_eq_fintype_card]
    exact h252KComplex_rootSet_card
  let e := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨fun i => h252ComplexPhaseRootEmbedding (e i),
    h252ComplexPhaseRootEmbedding.injective.comp e.injective⟩

end
end Biunimodular.F11
