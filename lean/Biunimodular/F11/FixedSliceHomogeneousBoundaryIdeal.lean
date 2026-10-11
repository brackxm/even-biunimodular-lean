/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceBoundaryReduction
import Mathlib.RingTheory.Nullstellensatz

set_option autoImplicit false

namespace Biunimodular.F11
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K]

def fixedSliceFourierLinearForm (F : Even6 K →ₗ[K] Even6 K) (j : Fin 6) :
    MvPolynomial (Fin 6) K :=
  ∑ i : Fin 6, C (F (Pi.single i 1) j) * X i

theorem fixedSliceFourierLinearForm_eval (F : Even6 K →ₗ[K] Even6 K)
    (h : Even6 K) (j : Fin 6) :
    aeval h (fixedSliceFourierLinearForm F j) = F h j := by
  classical
  have hrep : h = ∑ i : Fin 6, h i • Pi.single i 1 := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hf : F h j = ∑ i : Fin 6, h i * F (Pi.single i 1) j := by
    conv_lhs => rw [hrep]
    simp [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf]
  simp [fixedSliceFourierLinearForm, mul_comm]

def fixedSliceHomogeneousQuadric (F : Even6 K →ₗ[K] Even6 K) (j : Fin 6) :
    MvPolynomial (Fin 6) K :=
  X j * fixedSliceFourierLinearForm F j - X 0 * fixedSliceFourierLinearForm F 0

theorem fixedSliceHomogeneousQuadric_eval (F : Even6 K →ₗ[K] Even6 K)
    (h : Even6 K) (j : Fin 6) :
    aeval h (fixedSliceHomogeneousQuadric F j) =
      fourierCoordProduct F h j - fourierCoordProduct F h 0 := by
  simp only [fixedSliceHomogeneousQuadric, map_sub, map_mul, aeval_X,
    fixedSliceFourierLinearForm_eval, fourierCoordProduct]

/-- The boundary adds the zero-th coordinate to the actual homogeneous equations. -/
def fixedSliceHomogeneousBoundaryIdeal (F : Even6 K →ₗ[K] Even6 K) :
    Ideal (MvPolynomial (Fin 6) K) :=
  Ideal.span (insert (X 0) (Set.range (fixedSliceHomogeneousQuadric F)))

theorem fixedSliceHomogeneousBoundary_zeroLocus (F : Even6 K →ₗ[K] Even6 K)
    (hu : NoDisjointFourierSupport F) :
    MvPolynomial.zeroLocus K (fixedSliceHomogeneousBoundaryIdeal F) = {0} := by
  classical
  ext h
  rw [fixedSliceHomogeneousBoundaryIdeal, MvPolynomial.zeroLocus_span]
  constructor
  · intro hh
    have hzero : h 0 = 0 := by simpa using hh (X 0) (by simp)
    have heq : FixedSliceEq F h := by
      intro j
      apply sub_eq_zero.mp
      simpa only [fixedSliceHomogeneousQuadric_eval] using
        hh (fixedSliceHomogeneousQuadric F j) (by simp)
    have hnz : h = 0 := by
      by_contra hnz
      exact (fixedSlice_nowhere_coordinate_zero hu hnz heq).1 0 hzero
    exact Set.mem_singleton_iff.mpr hnz
  · intro hh
    rw [Set.mem_singleton_iff.mp hh]
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | ⟨j, rfl⟩
    · simp
    · rw [fixedSliceHomogeneousQuadric_eval]
      simp [fourierCoordProduct]

variable [IsAlgClosed K]

/-- Nullstellensatz turns the pointwise boundary exclusion into ideal membership. -/
theorem fixedSliceHomogeneousBoundary_variable_pow_mem
    (F : Even6 K →ₗ[K] Even6 K) (hu : NoDisjointFourierSupport F) (j : Fin 6) :
    ∃ n : ℕ, (X j : MvPolynomial (Fin 6) K)^n ∈ fixedSliceHomogeneousBoundaryIdeal F := by
  have hvan : (X j : MvPolynomial (Fin 6) K) ∈ MvPolynomial.vanishingIdeal K
      (MvPolynomial.zeroLocus K (fixedSliceHomogeneousBoundaryIdeal F)) := by
    intro h hh
    rw [fixedSliceHomogeneousBoundary_zeroLocus F hu] at hh
    rw [Set.mem_singleton_iff.mp hh]
    simp
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hvan
  exact Ideal.mem_radical_iff.mp hvan

/-- Every relevant prime over the homogeneous slice equations lies in the
zero-th-coordinate affine chart. This excludes boundary primes as well as points. -/
theorem fixedSliceHomogeneous_prime_chart
    (F : Even6 K →ₗ[K] Even6 K) (hu : NoDisjointFourierSupport F)
    (P : Ideal (MvPolynomial (Fin 6) K)) (hP : P.IsPrime)
    (heq : ∀ j : Fin 6, fixedSliceHomogeneousQuadric F j ∈ P)
    (hrelevant : ∃ j : Fin 6, (X j : MvPolynomial (Fin 6) K) ∉ P) :
    (X 0 : MvPolynomial (Fin 6) K) ∉ P := by
  intro hzero
  have hle : fixedSliceHomogeneousBoundaryIdeal F ≤ P := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | ⟨j, rfl⟩
    · exact hzero
    · exact heq j
  obtain ⟨j, hj⟩ := hrelevant
  obtain ⟨n, hn⟩ := fixedSliceHomogeneousBoundary_variable_pow_mem F hu j
  exact hj (hP.mem_of_pow_mem n (hle hn))

end
end Biunimodular.F11
