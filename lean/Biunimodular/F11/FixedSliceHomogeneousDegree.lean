/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11HomogeneousQuadrics

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

theorem fixedSliceFourier_diagonal_ne_zero (F : Even6 K →ₗ[K] Even6 K)
    (hu : NoDisjointFourierSupport F) (j : Fin 6) : F (Pi.single j 1) j ≠ 0 := by
  classical
  have hnz : (Pi.single j 1 : Even6 K) ≠ 0 := by
    intro h
    have he := congrFun h j
    simp at he
  intro hz
  apply hu (Pi.single j 1) hnz
  intro i
  by_cases hi : i = j
  · subst i
    exact Or.inr hz
  · left
    simp [hi]

theorem fixedSliceHomogeneousQuadric_ne_zero (F : Even6 K →ₗ[K] Even6 K)
    (hu : NoDisjointFourierSupport F) (j : Fin 6) (hj : j ≠ 0) :
    fixedSliceHomogeneousQuadric F j ≠ 0 := by
  classical
  intro hz
  have he := congrArg (MvPolynomial.aeval (Pi.single j 1 : Even6 K)) hz
  rw [fixedSliceHomogeneousQuadric_eval] at he
  apply fixedSliceFourier_diagonal_ne_zero F hu j
  simpa [fourierCoordProduct, Pi.single_apply, hj] using he

theorem fixedSliceHomogeneousQuadric_totalDegree (F : Even6 K →ₗ[K] Even6 K)
    (hu : NoDisjointFourierSupport F) (j : Fin 6) (hj : j ≠ 0) :
    (fixedSliceHomogeneousQuadric F j).totalDegree = 2 :=
  (fixedSliceHomogeneousQuadric_isHomogeneous F j).totalDegree
    (fixedSliceHomogeneousQuadric_ne_zero F hu j hj)

/-- All five concrete equations have degree exactly two, including nonvanishing. -/
theorem even11FixedSliceHomogeneousGenerators_totalDegree :
    ∀ p ∈ even11FixedSliceHomogeneousGenerators, p.totalDegree = 2 := by
  intro p hp
  simp only [even11FixedSliceHomogeneousGenerators, fixedSliceHomogeneousGenerators,
    List.mem_ofFn] at hp
  obtain ⟨j, rfl⟩ := hp
  exact fixedSliceHomogeneousQuadric_totalDegree _
    even11_normalized_noDisjointFourierSupport_certified j.succ (Fin.succ_ne_zero j)

end
end Biunimodular.F11
