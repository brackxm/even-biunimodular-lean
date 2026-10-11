/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurTorusRootLift
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

abbrev H252LocalizedTorusPolynomialRing := MvPolynomial (Fin 7) ℂ

def h252LocalizedTorusGenerators : Fin 7 → H252LocalizedTorusPolynomialRing :=
  let z := (MvPolynomial.X : Fin 7 → H252LocalizedTorusPolynomialRing)
  ![h252TorusF1 (z 0) (z 1) (z 2) (z 3) (z 4),
    h252TorusF2 (z 0) (z 1) (z 2) (z 3) (z 4),
    h252TorusF3 (z 0) (z 1) (z 2) (z 3) (z 4),
    h252TorusF4 (z 0) (z 1) (z 2) (z 3) (z 4),
    h252TorusF5 (z 0) (z 1) (z 2) (z 3) (z 4),
    h252TorusS (z 0) (z 1) (z 2) (z 3) (z 5) (z 4),
    (z 4) ^ 2 - 2 * (z 6) * (z 4) - 1]

def h252LocalizedTorusIdeal : Ideal H252LocalizedTorusPolynomialRing :=
  Ideal.span (Set.range h252LocalizedTorusGenerators)

abbrev H252LocalizedTorusAlgebra :=
  H252LocalizedTorusPolynomialRing ⧸ h252LocalizedTorusIdeal

def h252LocalizedTorusVar (i : Fin 7) : H252LocalizedTorusAlgebra :=
  Ideal.Quotient.mkₐ ℂ h252LocalizedTorusIdeal (MvPolynomial.X i)

def h252LocalizedTorusCoordinate : Polynomial ℂ →ₐ[ℂ] H252LocalizedTorusAlgebra :=
  Polynomial.aeval (h252LocalizedTorusVar 6)

def h252RurTorusPoint (x : ℂ) : Fin 7 → ℂ :=
  ![integerCoefficientEval x h252RurN1Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN2Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN3Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN4Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN5Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN6Coeffs / h252RurDenominator x, x]

theorem h252RurTorusPoint_generators_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) (i : Fin 7) :
    MvPolynomial.aeval (h252RurTorusPoint x) (h252LocalizedTorusGenerators i) = 0 := by
  fin_cases i
  · simpa [h252LocalizedTorusGenerators, h252RurTorusPoint, h252RurDenominator,
      h252TorusF1] using h252RurF1_zero x hx
  · simpa [h252LocalizedTorusGenerators, h252RurTorusPoint, h252RurDenominator,
      h252TorusF2] using h252RurF2_zero x hx
  · simpa [h252LocalizedTorusGenerators, h252RurTorusPoint, h252RurDenominator,
      h252TorusF3] using h252RurF3_zero x hx
  · simpa [h252LocalizedTorusGenerators, h252RurTorusPoint, h252RurDenominator,
      h252TorusF4] using h252RurF4_zero x hx
  · simpa [h252LocalizedTorusGenerators, h252RurTorusPoint, h252RurDenominator,
      h252TorusF5] using h252RurF5_zero x hx
  · simpa [h252LocalizedTorusGenerators, h252RurTorusPoint, h252RurDenominator,
      h252TorusS, h252TorusD, mul_assoc] using h252RurSaturation_zero x hx
  · simpa [h252LocalizedTorusGenerators, h252RurTorusPoint, h252RurDenominator]
      using h252RurCoordinate_zero x hx

theorem h252RurTorusPoint_ideal_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    h252LocalizedTorusIdeal ≤
      RingHom.ker (MvPolynomial.aeval (h252RurTorusPoint x)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨i, rfl⟩
  exact RingHom.mem_ker.mpr (h252RurTorusPoint_generators_zero x hx i)

def h252RurTorusPointEvaluation (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) : H252LocalizedTorusAlgebra →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ h252LocalizedTorusIdeal
    (MvPolynomial.aeval (h252RurTorusPoint x))
    (fun _p hp ↦ RingHom.mem_ker.mp (h252RurTorusPoint_ideal_zero x hx hp))

theorem h252RurTorusPointEvaluation_coordinate (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    h252RurTorusPointEvaluation x hx (h252LocalizedTorusCoordinate Polynomial.X) = x := by
  simp only [h252LocalizedTorusCoordinate, Polynomial.aeval_X]
  simp [h252RurTorusPointEvaluation, h252LocalizedTorusVar,
    h252RurTorusPoint]

end

end Biunimodular.F11
