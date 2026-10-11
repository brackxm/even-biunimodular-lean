/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Frobenius7

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Step36 : coordinateMod5Factor1r35 ^ 5 - coordinateMod5Factor1r36 =
    integerCoefficientEval X coordinateMod5Factor1q36Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r35Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r36Coeffs)) (integerCoefficientMul coordinateMod5Factor1q36Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r35, coordinateMod5Factor1r36] using h
theorem coordinateMod5Factor1Frob36 : coordinateMod5Factor1 ∣ frobeniusIter 5 36 - coordinateMod5Factor1r36 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob35
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q36Coeffs, by rw [coordinateMod5Factor1Step36]; ring⟩
theorem coordinateMod5Factor1Step37 : coordinateMod5Factor1r36 ^ 5 - coordinateMod5Factor1r37 =
    integerCoefficientEval X coordinateMod5Factor1q37Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r36Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r37Coeffs)) (integerCoefficientMul coordinateMod5Factor1q37Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r36, coordinateMod5Factor1r37] using h
theorem coordinateMod5Factor1Frob37 : coordinateMod5Factor1 ∣ frobeniusIter 5 37 - coordinateMod5Factor1r37 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob36
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q37Coeffs, by rw [coordinateMod5Factor1Step37]; ring⟩
theorem coordinateMod5Factor1Step38 : coordinateMod5Factor1r37 ^ 5 - coordinateMod5Factor1r38 =
    integerCoefficientEval X coordinateMod5Factor1q38Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r37Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r38Coeffs)) (integerCoefficientMul coordinateMod5Factor1q38Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r37, coordinateMod5Factor1r38] using h
theorem coordinateMod5Factor1Frob38 : coordinateMod5Factor1 ∣ frobeniusIter 5 38 - coordinateMod5Factor1r38 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob37
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q38Coeffs, by rw [coordinateMod5Factor1Step38]; ring⟩
theorem coordinateMod5Factor1Step39 : coordinateMod5Factor1r38 ^ 5 - coordinateMod5Factor1r39 =
    integerCoefficientEval X coordinateMod5Factor1q39Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r38Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r39Coeffs)) (integerCoefficientMul coordinateMod5Factor1q39Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r38, coordinateMod5Factor1r39] using h
theorem coordinateMod5Factor1Frob39 : coordinateMod5Factor1 ∣ frobeniusIter 5 39 - coordinateMod5Factor1r39 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob38
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q39Coeffs, by rw [coordinateMod5Factor1Step39]; ring⟩
theorem coordinateMod5Factor1Step40 : coordinateMod5Factor1r39 ^ 5 - coordinateMod5Factor1r40 =
    integerCoefficientEval X coordinateMod5Factor1q40Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r39Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r40Coeffs)) (integerCoefficientMul coordinateMod5Factor1q40Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r39, coordinateMod5Factor1r40] using h
theorem coordinateMod5Factor1Frob40 : coordinateMod5Factor1 ∣ frobeniusIter 5 40 - coordinateMod5Factor1r40 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob39
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q40Coeffs, by rw [coordinateMod5Factor1Step40]; ring⟩
end
end Biunimodular.F11
