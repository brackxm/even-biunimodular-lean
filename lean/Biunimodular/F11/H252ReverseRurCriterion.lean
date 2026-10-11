/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252LocalizedTorusEliminationIdeal
import Biunimodular.F11.UnivariateCoordinateSurjectivity

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
noncomputable section
open Polynomial

def h252RurNumeratorCoefficients : Fin 6 → List ℤ :=
  ![h252RurN1Coeffs, h252RurN2Coeffs, h252RurN3Coeffs,
    h252RurN4Coeffs, h252RurN5Coeffs, h252RurN6Coeffs]

theorem h252RurComplexPolynomial_derivative :
    derivative h252RurComplexPolynomial = integerCoefficientEval (X : ℂ[X]) h252RurDCoeffs := by
  rw [h252RurComplexPolynomial, integerCoefficientPolynomial_derivative,
    h252RurD_derivative_coefficients]

/-- Six reverse ideal-membership certificates suffice for generation of
the entire localized algebra. Separability supplies an inverse denominator
inside the quotient, so nilpotents are included in this conclusion. -/
theorem h252LocalizedTorusCoordinate_surjective_of_reverse_rur
    (hreverse : ∀ i : Fin 6,
      h252LocalizedTorusCoordinate (integerCoefficientEval (X : ℂ[X]) h252RurDCoeffs) *
        h252LocalizedTorusVar i.castSucc =
      h252LocalizedTorusCoordinate
        (integerCoefficientEval (X : ℂ[X]) (h252RurNumeratorCoefficients i))) :
    Function.Surjective h252LocalizedTorusCoordinate := by
  obtain ⟨B, E, hBE⟩ := (Polynomial.separable_def' _).mp h252RurComplexPolynomial_separable
  rw [h252RurComplexPolynomial_derivative] at hBE
  apply coordinate_surjective_of_variables_in_range h252LocalizedTorusIdeal
  intro i
  have hv (j : Fin 6) : h252LocalizedTorusVar j.castSucc ∈ h252LocalizedTorusCoordinate.range :=
    coordinate_mem_range_of_reverse_rur h252LocalizedTorusCoordinate h252RurComplexPolynomial
      (integerCoefficientEval (X : ℂ[X]) h252RurDCoeffs) B E
      (integerCoefficientEval (X : ℂ[X]) (h252RurNumeratorCoefficients j))
      (h252LocalizedTorusVar j.castSucc) h252LocalizedTorusCoordinate_eliminant_zero hBE
      (hreverse j)
  fin_cases i
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 3
  · exact hv 4
  · exact hv 5
  · exact ⟨X, Polynomial.aeval_X _⟩

end
end Biunimodular.F11
