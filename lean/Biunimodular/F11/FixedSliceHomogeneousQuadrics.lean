/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceHomogeneousBoundaryIdeal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.List.OfFn

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

theorem fixedSliceFourierLinearForm_isHomogeneous (F : Even6 K →ₗ[K] Even6 K)
    (j : Fin 6) : (fixedSliceFourierLinearForm F j).IsHomogeneous 1 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem fixedSliceHomogeneousQuadric_isHomogeneous (F : Even6 K →ₗ[K] Even6 K)
    (j : Fin 6) : (fixedSliceHomogeneousQuadric F j).IsHomogeneous 2 := by
  exact ((MvPolynomial.isHomogeneous_X K j).mul
    (fixedSliceFourierLinearForm_isHomogeneous F j)).sub
      ((MvPolynomial.isHomogeneous_X K 0).mul (fixedSliceFourierLinearForm_isHomogeneous F 0))

theorem fixedSliceHomogeneousQuadric_zero (F : Even6 K →ₗ[K] Even6 K) :
    fixedSliceHomogeneousQuadric F 0 = 0 := by
  simp [fixedSliceHomogeneousQuadric]

/-- The five genuine homogeneous equations, omitting the tautological zero-th equation. -/
def fixedSliceHomogeneousGenerators (F : Even6 K →ₗ[K] Even6 K) :
    List (MvPolynomial (Fin 6) K) :=
  List.ofFn (fun j : Fin 5 => fixedSliceHomogeneousQuadric F j.succ)

theorem fixedSliceHomogeneousGenerators_length (F : Even6 K →ₗ[K] Even6 K) :
    (fixedSliceHomogeneousGenerators F).length = 5 := by
  simp [fixedSliceHomogeneousGenerators]

theorem fixedSliceHomogeneousGenerators_isHomogeneous (F : Even6 K →ₗ[K] Even6 K) :
    ∀ p ∈ fixedSliceHomogeneousGenerators F, p.IsHomogeneous 2 := by
  intro p hp
  simp only [fixedSliceHomogeneousGenerators, List.mem_ofFn] at hp
  obtain ⟨j, rfl⟩ := hp
  exact fixedSliceHomogeneousQuadric_isHomogeneous F j.succ

end
end Biunimodular.F11
