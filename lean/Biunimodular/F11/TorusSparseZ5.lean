/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RurInverseSparsePolynomial

set_option autoImplicit false
namespace Biunimodular.F11
variable {R : Type*} [CommRing R]
private theorem rurInverseSparseEval_cons_z5 (t : RurInverseTerm7)
    (ts : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (t :: ts) z1 z2 z3 z4 w z5 x =
      rurInverseSparseTermEval t z1 z2 z3 z4 w z5 x +
        rurInverseSparseEval ts z1 z2 z3 z4 w z5 x := rfl

def rurInverseSparseOfZ5Aux : List ℤ → ℕ → List RurInverseTerm7
  | [], _ => []
  | c :: cs, e =>
    if c = 0 then rurInverseSparseOfZ5Aux cs (e + 1)
    else ⟨c, ⟨0, 0, 0, 0, 0, e, 0⟩⟩ :: rurInverseSparseOfZ5Aux cs (e + 1)

def rurInverseSparseOfZ5 (cs : List ℤ) : List RurInverseTerm7 := rurInverseSparseOfZ5Aux cs 0

theorem rurInverseSparseEval_ofZ5Aux (cs : List ℤ) (e : ℕ)
    (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseOfZ5Aux cs e) z1 z2 z3 z4 w z5 x =
      z5 ^ e * integerCoefficientEval z5 cs := by
  induction cs generalizing e with
  | nil => simp [rurInverseSparseOfZ5Aux, integerCoefficientEval]
  | cons c cs ih =>
    by_cases hc : c = 0
    · rw [rurInverseSparseOfZ5Aux, ite_eq_left hc, ih]
      simp only [integerCoefficientEval, hc, Int.cast_zero, zero_add, pow_succ]
      ring
    · rw [rurInverseSparseOfZ5Aux, ite_eq_right hc, rurInverseSparseEval_cons_z5, ih]
      simp only [rurInverseSparseTermEval, integerCoefficientEval, pow_zero, mul_one]
      rw [pow_succ]
      ring

theorem rurInverseSparseEval_ofZ5 (cs : List ℤ) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseOfZ5 cs) z1 z2 z3 z4 w z5 x =
      integerCoefficientEval z5 cs := by
  rw [rurInverseSparseOfZ5, rurInverseSparseEval_ofZ5Aux, pow_zero, one_mul]

end Biunimodular.F11
