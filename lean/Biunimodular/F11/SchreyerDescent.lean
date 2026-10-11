/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.SchreyerLeadingRelation
import Mathlib.LinearAlgebra.Span.Basic

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

variable {σ K : Type*} [Field K] {n : ℕ}

def polynomialRelationMap (g : Fin n → MvPolynomial σ K) :
    (Fin n → MvPolynomial σ K) →ₗ[MvPolynomial σ K] MvPolynomial σ K where
  toFun v := ∑ i, v i * g i
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Once every nonzero relation admits a critical-pair reduction that
strictly decreases its Schreyer key, the finite critical relations generate
the entire kernel. The argument terminates by the proved monomial order. -/
theorem schreyer_relations_generate_of_descent {ι : Type*}
    (m : MonomialOrder σ) (g : Fin n → MvPolynomial σ K)
    (s : ι → Fin n → MvPolynomial σ K)
    (hs : ∀ j, (∑ i, s j i * g i) = 0)
    (hreduce : ∀ v : Fin n → MvPolynomial σ K,
      v ≠ 0 → (∑ i, v i * g i) = 0 →
      ∃ (j : ι) (q : MvPolynomial σ K),
        schreyerDegree m g (v - q • s j) < schreyerDegree m g v) :
    LinearMap.ker (polynomialRelationMap g) =
      Submodule.span (MvPolynomial σ K) (Set.range s) := by
  classical
  have hle : Submodule.span (MvPolynomial σ K) (Set.range s) ≤
      LinearMap.ker (polynomialRelationMap g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hs j
  apply le_antisymm ?_ hle
  intro v hv
  let wf := (wellFounded_lt : WellFounded
    (fun a b : WithBot (m.syn ×ₗ ℕ) => a < b)).onFun (f := schreyerDegree m g)
  have hmem : ∀ v : Fin n → MvPolynomial σ K,
      (∑ i, v i * g i) = 0 →
      v ∈ Submodule.span (MvPolynomial σ K) (Set.range s) := by
    intro v
    induction v using wf.induction with
    | h v ih =>
      intro hv
      by_cases hz : v = 0
      · exact hz ▸ Submodule.zero_mem _
      obtain ⟨j, q, hlt⟩ := hreduce v hz hv
      have hq : q • s j ∈ Submodule.span (MvPolynomial σ K) (Set.range s) :=
        Submodule.smul_mem _ q (Submodule.subset_span ⟨j, rfl⟩)
      have hr : (∑ i, (v - q • s j) i * g i) = 0 := by
        have hk := hle hq
        change polynomialRelationMap g (q • s j) = 0 at hk
        change polynomialRelationMap g v = 0 at hv
        change polynomialRelationMap g (v - q • s j) = 0
        simp [hv, hk]
      have hsm := ih _ hlt hr
      simpa using Submodule.add_mem _ hsm hq
  exact hmem v hv

end
end Biunimodular.F11
