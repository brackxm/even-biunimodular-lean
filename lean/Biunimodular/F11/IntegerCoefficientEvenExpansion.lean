/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomialMap

set_option autoImplicit false
namespace Biunimodular.F11

def integerCoefficientEvenExpansion : List ℤ → List ℤ
  | [] => []
  | a :: as => a :: 0 :: integerCoefficientEvenExpansion as

theorem integerCoefficientEvenExpansion_eval {R : Type*} [CommRing R]
    (x : R) (a : List ℤ) :
    integerCoefficientEval x (integerCoefficientEvenExpansion a) =
      integerCoefficientEval (x ^ 2) a := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [integerCoefficientEvenExpansion, integerCoefficientEval,
      Int.cast_zero, zero_add, ih]
    ring

end Biunimodular.F11
