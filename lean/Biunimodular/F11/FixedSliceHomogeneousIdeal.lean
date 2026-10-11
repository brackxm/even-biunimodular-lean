/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11HomogeneousQuadrics
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

def fixedSliceHomogeneousIdeal : Ideal (MvPolynomial (Fin 6) ℂ) :=
  Ideal.span {p | p ∈ even11FixedSliceHomogeneousGenerators}

theorem fixedSliceHomogeneousIdeal_isHomogeneous :
    fixedSliceHomogeneousIdeal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 6) ℂ) := by
  apply Ideal.homogeneous_span
  intro p hp
  exact ⟨2, even11FixedSliceHomogeneousGenerators_quadratic p hp⟩

/-- The actual five-quadric ideal, as a homogeneous ideal for total degree. -/
def fixedSliceGradedHomogeneousIdeal :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 6) ℂ) :=
  ⟨fixedSliceHomogeneousIdeal, fixedSliceHomogeneousIdeal_isHomogeneous⟩

theorem fixedSliceHomogeneousQuadric_mem_ideal (j : Fin 6) :
    fixedSliceHomogeneousQuadric even11FourierNormalized j ∈ fixedSliceHomogeneousIdeal := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [fixedSliceHomogeneousQuadric_zero]
    exact Ideal.zero_mem _
  · apply Ideal.subset_span
    simp only [even11FixedSliceHomogeneousGenerators, fixedSliceHomogeneousGenerators,
      List.mem_ofFn]
    exact ⟨i, rfl⟩

/-- Every relevant homogeneous prime over the actual graded ideal is in
the zero-th-coordinate chart. -/
theorem fixedSliceGradedHomogeneousIdeal_prime_chart
    (P : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 6) ℂ))
    (hP : P.toIdeal.IsPrime) (hI : fixedSliceHomogeneousIdeal ≤ P.toIdeal)
    (hrelevant : ∃ j : Fin 6, (MvPolynomial.X j : MvPolynomial (Fin 6) ℂ) ∉ P.toIdeal) :
    (MvPolynomial.X 0 : MvPolynomial (Fin 6) ℂ) ∉ P.toIdeal :=
  even11FixedSliceHomogeneous_prime_chart P.toIdeal hP
    (fun j => hI (fixedSliceHomogeneousQuadric_mem_ideal j)) hrelevant

end
end Biunimodular.F11
