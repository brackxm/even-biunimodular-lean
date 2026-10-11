/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Biunimodular.F11.P150PolynomialData11

set_option autoImplicit false
namespace Biunimodular.F11

def integerCoefficientRescale (s : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: as => a :: integerCoefficientScale s (integerCoefficientRescale s as)

theorem integerCoefficientRescale_eval {R : Type*} [CommRing R]
    (s : ℤ) (x : R) (a : List ℤ) :
    integerCoefficientEval x (integerCoefficientRescale s a) =
      integerCoefficientEval ((s : R) * x) a := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    rw [integerCoefficientRescale]
    simp only [integerCoefficientEval, integerCoefficientEval_scale, ih]
    ring

theorem polynomialOfCoefficientsZ_eq_integerCoefficient (a : List ℤ) :
    polynomialOfCoefficientsZ a = integerCoefficientEval (Polynomial.X : Polynomial ℤ) a := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    change Polynomial.C a + Polynomial.X * polynomialOfCoefficientsZ as =
      (a : Polynomial ℤ) + Polynomial.X * integerCoefficientEval Polynomial.X as
    have hCa : (Polynomial.C a : Polynomial ℤ) = a := by simp
    rw [hCa, ih]

end Biunimodular.F11
