/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomialMap

set_option autoImplicit false
namespace Biunimodular.F11

def integerCoefficientZeroCheck (cs : List ℤ) : Bool := cs.all (· == 0)

theorem integerCoefficientZeroCheck_sound {R : Type*} [CommRing R]
    (cs : List ℤ) (h : integerCoefficientZeroCheck cs = true) (x : R) :
    integerCoefficientEval x cs = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c = 0 ∧ integerCoefficientZeroCheck cs = true := by
      simpa only [integerCoefficientZeroCheck, List.all_cons, Bool.and_eq_true,
        beq_iff_eq] using h
    simp only [integerCoefficientEval, hc.1, Int.cast_zero, zero_add, ih hc.2, mul_zero]

end Biunimodular.F11
