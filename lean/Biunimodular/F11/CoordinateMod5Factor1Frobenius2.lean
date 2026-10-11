/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Step6 : coordinateMod5Factor1r5 ^ 5 - coordinateMod5Factor1r6 =
    integerCoefficientEval X coordinateMod5Factor1q6Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r5Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r6Coeffs)) (integerCoefficientMul coordinateMod5Factor1q6Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r5, coordinateMod5Factor1r6] using h
theorem coordinateMod5Factor1Frob6 : coordinateMod5Factor1 ∣ frobeniusIter 5 6 - coordinateMod5Factor1r6 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob5
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q6Coeffs, by rw [coordinateMod5Factor1Step6]; ring⟩
theorem coordinateMod5Factor1Step7 : coordinateMod5Factor1r6 ^ 5 - coordinateMod5Factor1r7 =
    integerCoefficientEval X coordinateMod5Factor1q7Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r6Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r7Coeffs)) (integerCoefficientMul coordinateMod5Factor1q7Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r6, coordinateMod5Factor1r7] using h
theorem coordinateMod5Factor1Frob7 : coordinateMod5Factor1 ∣ frobeniusIter 5 7 - coordinateMod5Factor1r7 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob6
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q7Coeffs, by rw [coordinateMod5Factor1Step7]; ring⟩
theorem coordinateMod5Factor1Step8 : coordinateMod5Factor1r7 ^ 5 - coordinateMod5Factor1r8 =
    integerCoefficientEval X coordinateMod5Factor1q8Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r7Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r8Coeffs)) (integerCoefficientMul coordinateMod5Factor1q8Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r7, coordinateMod5Factor1r8] using h
theorem coordinateMod5Factor1Frob8 : coordinateMod5Factor1 ∣ frobeniusIter 5 8 - coordinateMod5Factor1r8 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob7
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q8Coeffs, by rw [coordinateMod5Factor1Step8]; ring⟩
theorem coordinateMod5Factor1Step9 : coordinateMod5Factor1r8 ^ 5 - coordinateMod5Factor1r9 =
    integerCoefficientEval X coordinateMod5Factor1q9Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r8Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r9Coeffs)) (integerCoefficientMul coordinateMod5Factor1q9Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r8, coordinateMod5Factor1r9] using h
theorem coordinateMod5Factor1Frob9 : coordinateMod5Factor1 ∣ frobeniusIter 5 9 - coordinateMod5Factor1r9 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob8
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q9Coeffs, by rw [coordinateMod5Factor1Step9]; ring⟩
theorem coordinateMod5Factor1Step10 : coordinateMod5Factor1r9 ^ 5 - coordinateMod5Factor1r10 =
    integerCoefficientEval X coordinateMod5Factor1q10Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r9Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r10Coeffs)) (integerCoefficientMul coordinateMod5Factor1q10Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r9, coordinateMod5Factor1r10] using h
theorem coordinateMod5Factor1Frob10 : coordinateMod5Factor1 ∣ frobeniusIter 5 10 - coordinateMod5Factor1r10 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob9
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q10Coeffs, by rw [coordinateMod5Factor1Step10]; ring⟩
end
end Biunimodular.F11
