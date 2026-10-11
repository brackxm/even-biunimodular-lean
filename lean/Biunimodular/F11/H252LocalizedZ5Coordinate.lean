/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RurInverseGeneratorSemantics
import Biunimodular.F11.IntegerCoefficientDegree
import Biunimodular.F11.TorusFiberCoordinateCriterion
import Biunimodular.F11.H252SchemeDimensionCriterion

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
noncomputable section
open Polynomial

def h252LocalizedZ5Coordinate : ℂ[X] →ₐ[ℂ] H252LocalizedTorusAlgebra :=
  Polynomial.aeval (h252LocalizedTorusVar 4)

def h252Z5ComplexPolynomial : ℂ[X] :=
  integerCoefficientEval X h252TorusEliminantCoeffs11

theorem h252Z5ComplexPolynomial_nonzero_degree :
    h252Z5ComplexPolynomial ≠ 0 ∧ h252Z5ComplexPolynomial.natDegree = 252 := by
  have hlist : h252TorusEliminantCoeffs11.take 252 ++ [6436343] =
      h252TorusEliminantCoeffs11 := by native_decide
  have hlen : (h252TorusEliminantCoeffs11.take 252).length = 252 := by native_decide
  have h := integerCoefficientPolynomial_append_degree (R := ℂ)
    (h252TorusEliminantCoeffs11.take 252) 6436343 (by norm_num)
  simpa only [hlist, hlen, h252Z5ComplexPolynomial] using h

/-- The original saturated certificate annihilates z5 in the actual quotient,
not just at its complex points. -/
theorem h252LocalizedZ5Coordinate_eliminant_zero :
    h252LocalizedZ5Coordinate h252Z5ComplexPolynomial = 0 := by
  let z := h252LocalizedTorusVar
  have hs : h252TorusS (z 0) (z 1) (z 2) (z 3) (z 5) (z 4) = 0 := by
    simpa only [rurInverseGenerator6_eval] using rurInverseGenerator6_quotient_zero
  have hD : z 5 * h252TorusD (z 0) (z 1) (z 2) (z 3) (z 4) = 1 :=
    sub_eq_zero.mp hs
  have h := h252UniversalTorusIdentity (z 0) (z 1) (z 2) (z 3) (z 5) (z 4)
  have h1 := rurInverseGenerator1_quotient_zero
  have h2 := rurInverseGenerator2_quotient_zero
  have h3 := rurInverseGenerator3_quotient_zero
  have h4 := rurInverseGenerator4_quotient_zero
  have h5 := rurInverseGenerator5_quotient_zero
  rw [rurInverseGenerator1_eval] at h1
  change h252TorusF1 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 at h1
  rw [rurInverseGenerator2_eval] at h2
  change h252TorusF2 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 at h2
  rw [rurInverseGenerator3_eval] at h3
  change h252TorusF3 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 at h3
  rw [rurInverseGenerator4_eval] at h4
  change h252TorusF4 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 at h4
  rw [rurInverseGenerator5_eval] at h5
  change h252TorusF5 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 at h5
  simp only [h252UniversalTorusIdentityLeft, h252UniversalTorusIdentityRight,
    h1, h2, h3, h4, h5, mul_zero, add_zero] at h
  have he : integerCoefficientEval (z 4) h252TorusEliminantCoeffs11 = 0 := by
    calc
      _ = 1 * integerCoefficientEval (z 4) h252TorusEliminantCoeffs11 := by ring
      _ = (z 5 * h252TorusD (z 0) (z 1) (z 2) (z 3) (z 4)) *
          integerCoefficientEval (z 4) h252TorusEliminantCoeffs11 := by rw [hD]
      _ = z 5 * (h252TorusD (z 0) (z 1) (z 2) (z 3) (z 4) *
          integerCoefficientEval (z 4) h252TorusEliminantCoeffs11) := by ring
      _ = 0 := by rw [h, mul_zero]
  change (Polynomial.aeval (z 4) : ℂ[X] →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom
    (integerCoefficientEval X h252TorusEliminantCoeffs11) = 0
  rw [integerCoefficientEval_map]
  have hX : (Polynomial.aeval (z 4) : ℂ[X] →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom X =
      z 4 := Polynomial.aeval_X (z 4)
  simpa only [hX] using he

/-- Once the fiber certificates generate every coordinate from z5, the
existing dimension criterion also generates the RUR coordinate. -/
theorem h252LocalizedTorusCoordinate_surjective_of_z5
    (hs : Function.Surjective h252LocalizedZ5Coordinate) :
    Function.Surjective h252LocalizedTorusCoordinate := by
  let := coordinate_finite_of_surjective_annihilator h252LocalizedZ5Coordinate
    h252Z5ComplexPolynomial h252Z5ComplexPolynomial_nonzero_degree.1
    h252LocalizedZ5Coordinate_eliminant_zero hs
  apply h252LocalizedTorusCoordinate_surjective_of_dimension
  simpa only [h252Z5ComplexPolynomial_nonzero_degree.2] using
    coordinate_finrank_le_of_surjective_annihilator h252LocalizedZ5Coordinate
      h252Z5ComplexPolynomial h252Z5ComplexPolynomial_nonzero_degree.1
      h252LocalizedZ5Coordinate_eliminant_zero hs

end
end Biunimodular.F11
