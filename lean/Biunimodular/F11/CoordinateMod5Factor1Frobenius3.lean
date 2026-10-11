/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Frobenius2

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Step11 : coordinateMod5Factor1r10 ^ 5 - coordinateMod5Factor1r11 =
    integerCoefficientEval X coordinateMod5Factor1q11Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r10Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r11Coeffs)) (integerCoefficientMul coordinateMod5Factor1q11Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r10, coordinateMod5Factor1r11] using h
theorem coordinateMod5Factor1Frob11 : coordinateMod5Factor1 ∣ frobeniusIter 5 11 - coordinateMod5Factor1r11 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob10
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q11Coeffs, by rw [coordinateMod5Factor1Step11]; ring⟩
theorem coordinateMod5Factor1Step12 : coordinateMod5Factor1r11 ^ 5 - coordinateMod5Factor1r12 =
    integerCoefficientEval X coordinateMod5Factor1q12Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r11Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r12Coeffs)) (integerCoefficientMul coordinateMod5Factor1q12Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r11, coordinateMod5Factor1r12] using h
theorem coordinateMod5Factor1Frob12 : coordinateMod5Factor1 ∣ frobeniusIter 5 12 - coordinateMod5Factor1r12 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob11
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q12Coeffs, by rw [coordinateMod5Factor1Step12]; ring⟩
theorem coordinateMod5Factor1Step13 : coordinateMod5Factor1r12 ^ 5 - coordinateMod5Factor1r13 =
    integerCoefficientEval X coordinateMod5Factor1q13Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r12Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r13Coeffs)) (integerCoefficientMul coordinateMod5Factor1q13Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r12, coordinateMod5Factor1r13] using h
theorem coordinateMod5Factor1Frob13 : coordinateMod5Factor1 ∣ frobeniusIter 5 13 - coordinateMod5Factor1r13 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob12
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q13Coeffs, by rw [coordinateMod5Factor1Step13]; ring⟩
theorem coordinateMod5Factor1Step14 : coordinateMod5Factor1r13 ^ 5 - coordinateMod5Factor1r14 =
    integerCoefficientEval X coordinateMod5Factor1q14Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r13Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r14Coeffs)) (integerCoefficientMul coordinateMod5Factor1q14Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r13, coordinateMod5Factor1r14] using h
theorem coordinateMod5Factor1Frob14 : coordinateMod5Factor1 ∣ frobeniusIter 5 14 - coordinateMod5Factor1r14 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob13
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q14Coeffs, by rw [coordinateMod5Factor1Step14]; ring⟩
theorem coordinateMod5Factor1Step15 : coordinateMod5Factor1r14 ^ 5 - coordinateMod5Factor1r15 =
    integerCoefficientEval X coordinateMod5Factor1q15Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r14Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r15Coeffs)) (integerCoefficientMul coordinateMod5Factor1q15Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r14, coordinateMod5Factor1r15] using h
theorem coordinateMod5Factor1Frob15 : coordinateMod5Factor1 ∣ frobeniusIter 5 15 - coordinateMod5Factor1r15 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob14
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q15Coeffs, by rw [coordinateMod5Factor1Step15]; ring⟩
end
end Biunimodular.F11
