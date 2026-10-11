/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceHomogeneousIdeal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem polynomial_sub_constant_mem (P : Ideal (MvPolynomial (Fin 6) ℂ))
    (hX : ∀ j, MvPolynomial.X j ∈ P) (p : MvPolynomial (Fin 6) ℂ) :
    p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ P := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using P.add_mem hp hq
  | mul_X p i hp =>
    simpa using P.mul_mem_left p (hX i)

/-- A projective prime in the standard total-degree grading excludes a
coordinate variable. This connects relevance to the concrete boundary lemma. -/
theorem fixedSliceProjectiveSpectrum_relevant
    (x : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 6) ℂ)) :
    ∃ j : Fin 6, (MvPolynomial.X j : MvPolynomial (Fin 6) ℂ) ∉
      x.asHomogeneousIdeal.toIdeal := by
  classical
  by_contra! hX
  apply x.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn p hp
  have hzero : MvPolynomial.constantCoeff p = 0 := by
    have hc : p.coeff 0 = 0 := by
      apply MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hp
      simpa using ne_of_lt hn
    exact hc
  have h := polynomial_sub_constant_mem x.asHomogeneousIdeal.toIdeal hX p
  simpa [hzero] using h

/-- The actual projective zero locus of the five quadrics. -/
def fixedSliceProjectiveZeroLocus :
    Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 6) ℂ)) :=
  ProjectiveSpectrum.zeroLocus _ (fixedSliceHomogeneousIdeal : Set _)

theorem fixedSliceProjectiveZeroLocus_isClosed : IsClosed fixedSliceProjectiveZeroLocus :=
  ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- Every point of the actual projective zero locus belongs to the single
zero-th-coordinate affine chart. -/
theorem fixedSliceProjectiveZeroLocus_subset_chart :
    fixedSliceProjectiveZeroLocus ⊆
      ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 6) ℂ)
        (MvPolynomial.X 0) := by
  intro x hx
  exact fixedSliceGradedHomogeneousIdeal_prime_chart x.asHomogeneousIdeal
    x.isPrime hx (fixedSliceProjectiveSpectrum_relevant x)

theorem fixedSliceProjectiveZeroLocus_boundary_empty :
    fixedSliceProjectiveZeroLocus ∩
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 6) ℂ)
        {MvPolynomial.X 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact fixedSliceProjectiveZeroLocus_subset_chart hx.1 (hx.2 (by simp))

end
end Biunimodular.F11
