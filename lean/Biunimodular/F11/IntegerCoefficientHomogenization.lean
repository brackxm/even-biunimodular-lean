/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientDifferential

set_option autoImplicit false

namespace Biunimodular.F11

def integerCoefficientScaledMonomial (c : ℤ) : ℕ → List ℤ
  | 0 => [c]
  | n + 1 => 0 :: integerCoefficientScaledMonomial (2 * c) n

def integerCoefficientHomogenize : List ℤ → List ℤ
  | [] => []
  | c :: cs => integerCoefficientAdd
      (integerCoefficientScaledMonomial c cs.length)
      (integerCoefficientMul [-1, 0, 1] (integerCoefficientHomogenize cs))

theorem integerCoefficientEval_scaledMonomial {R : Type*} [CommRing R]
    (c : ℤ) (n : ℕ) (z : R) :
    integerCoefficientEval z (integerCoefficientScaledMonomial c n) =
      c * (2 * z) ^ n := by
  induction n generalizing c with
  | zero => simp [integerCoefficientScaledMonomial, integerCoefficientEval]
  | succ n ih =>
    simp [integerCoefficientScaledMonomial, integerCoefficientEval, ih, pow_succ]
    ring

/-- Clearing the relation `z^2 - 1 = 2*z*x` preserves the polynomial
identity in any commutative ring, including nonreduced coordinate rings. -/
theorem integerCoefficientHomogenize_eval {R : Type*} [CommRing R]
    (c : ℤ) (cs : List ℤ) (z x : R) (hrel : z ^ 2 - 1 = 2 * z * x) :
    integerCoefficientEval z (integerCoefficientHomogenize (c :: cs)) =
      (2 * z) ^ cs.length * integerCoefficientEval x (c :: cs) := by
  induction cs generalizing c with
  | nil =>
    rw [integerCoefficientHomogenize, integerCoefficientEval_add,
      integerCoefficientEval_scaledMonomial, integerCoefficientEval_mul]
    simp [integerCoefficientHomogenize, integerCoefficientEval]
  | cons d ds ih =>
    rw [integerCoefficientHomogenize, integerCoefficientEval_add,
      integerCoefficientEval_scaledMonomial, integerCoefficientEval_mul, ih d]
    simp only [integerCoefficientEval, List.length_cons]
    norm_num
    have hrel' : -1 + z * z = 2 * z * x := by
      calc
        -1 + z * z = z ^ 2 - 1 := by ring
        _ = 2 * z * x := hrel
    rw [hrel', pow_succ]
    ring

end Biunimodular.F11
