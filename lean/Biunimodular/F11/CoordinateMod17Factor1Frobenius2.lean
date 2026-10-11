/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor1Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor1Step6 : coordinateMod17Factor1r5 ^ 17 - coordinateMod17Factor1r6 =
    integerCoefficientEval X coordinateMod17Factor1q6Coeffs * coordinateMod17Factor1 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor1r5Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor1r6Coeffs)) (integerCoefficientMul coordinateMod17Factor1q6Coeffs coordinateMod17Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor1, coordinateMod17Factor1r5, coordinateMod17Factor1r6] using h
theorem coordinateMod17Factor1Frob6 : coordinateMod17Factor1 ∣ frobeniusIter 17 6 - coordinateMod17Factor1r6 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor1Frob5
  exact ⟨integerCoefficientEval X coordinateMod17Factor1q6Coeffs, by rw [coordinateMod17Factor1Step6]; ring⟩
theorem coordinateMod17Factor1Step7 : coordinateMod17Factor1r6 ^ 17 - coordinateMod17Factor1r7 =
    integerCoefficientEval X coordinateMod17Factor1q7Coeffs * coordinateMod17Factor1 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor1r6Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor1r7Coeffs)) (integerCoefficientMul coordinateMod17Factor1q7Coeffs coordinateMod17Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor1, coordinateMod17Factor1r6, coordinateMod17Factor1r7] using h
theorem coordinateMod17Factor1Frob7 : coordinateMod17Factor1 ∣ frobeniusIter 17 7 - coordinateMod17Factor1r7 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor1Frob6
  exact ⟨integerCoefficientEval X coordinateMod17Factor1q7Coeffs, by rw [coordinateMod17Factor1Step7]; ring⟩
theorem coordinateMod17Factor1Step8 : coordinateMod17Factor1r7 ^ 17 - coordinateMod17Factor1r8 =
    integerCoefficientEval X coordinateMod17Factor1q8Coeffs * coordinateMod17Factor1 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor1r7Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor1r8Coeffs)) (integerCoefficientMul coordinateMod17Factor1q8Coeffs coordinateMod17Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor1, coordinateMod17Factor1r7, coordinateMod17Factor1r8] using h
theorem coordinateMod17Factor1Frob8 : coordinateMod17Factor1 ∣ frobeniusIter 17 8 - coordinateMod17Factor1r8 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor1Frob7
  exact ⟨integerCoefficientEval X coordinateMod17Factor1q8Coeffs, by rw [coordinateMod17Factor1Step8]; ring⟩
theorem coordinateMod17Factor1Step9 : coordinateMod17Factor1r8 ^ 17 - coordinateMod17Factor1r9 =
    integerCoefficientEval X coordinateMod17Factor1q9Coeffs * coordinateMod17Factor1 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor1r8Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor1r9Coeffs)) (integerCoefficientMul coordinateMod17Factor1q9Coeffs coordinateMod17Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor1, coordinateMod17Factor1r8, coordinateMod17Factor1r9] using h
theorem coordinateMod17Factor1Frob9 : coordinateMod17Factor1 ∣ frobeniusIter 17 9 - coordinateMod17Factor1r9 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor1Frob8
  exact ⟨integerCoefficientEval X coordinateMod17Factor1q9Coeffs, by rw [coordinateMod17Factor1Step9]; ring⟩
theorem coordinateMod17Factor1Step10 : coordinateMod17Factor1r9 ^ 17 - coordinateMod17Factor1r10 =
    integerCoefficientEval X coordinateMod17Factor1q10Coeffs * coordinateMod17Factor1 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor1r9Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor1r10Coeffs)) (integerCoefficientMul coordinateMod17Factor1q10Coeffs coordinateMod17Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor1, coordinateMod17Factor1r9, coordinateMod17Factor1r10] using h
theorem coordinateMod17Factor1Frob10 : coordinateMod17Factor1 ∣ frobeniusIter 17 10 - coordinateMod17Factor1r10 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor1Frob9
  exact ⟨integerCoefficientEval X coordinateMod17Factor1q10Coeffs, by rw [coordinateMod17Factor1Step10]; ring⟩
end
end Biunimodular.F11
