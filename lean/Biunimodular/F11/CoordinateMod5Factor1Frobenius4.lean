/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Frobenius3

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Step16 : coordinateMod5Factor1r15 ^ 5 - coordinateMod5Factor1r16 =
    integerCoefficientEval X coordinateMod5Factor1q16Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r15Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r16Coeffs)) (integerCoefficientMul coordinateMod5Factor1q16Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r15, coordinateMod5Factor1r16] using h
theorem coordinateMod5Factor1Frob16 : coordinateMod5Factor1 ∣ frobeniusIter 5 16 - coordinateMod5Factor1r16 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob15
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q16Coeffs, by rw [coordinateMod5Factor1Step16]; ring⟩
theorem coordinateMod5Factor1Step17 : coordinateMod5Factor1r16 ^ 5 - coordinateMod5Factor1r17 =
    integerCoefficientEval X coordinateMod5Factor1q17Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r16Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r17Coeffs)) (integerCoefficientMul coordinateMod5Factor1q17Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r16, coordinateMod5Factor1r17] using h
theorem coordinateMod5Factor1Frob17 : coordinateMod5Factor1 ∣ frobeniusIter 5 17 - coordinateMod5Factor1r17 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob16
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q17Coeffs, by rw [coordinateMod5Factor1Step17]; ring⟩
theorem coordinateMod5Factor1Step18 : coordinateMod5Factor1r17 ^ 5 - coordinateMod5Factor1r18 =
    integerCoefficientEval X coordinateMod5Factor1q18Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r17Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r18Coeffs)) (integerCoefficientMul coordinateMod5Factor1q18Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r17, coordinateMod5Factor1r18] using h
theorem coordinateMod5Factor1Frob18 : coordinateMod5Factor1 ∣ frobeniusIter 5 18 - coordinateMod5Factor1r18 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob17
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q18Coeffs, by rw [coordinateMod5Factor1Step18]; ring⟩
theorem coordinateMod5Factor1Step19 : coordinateMod5Factor1r18 ^ 5 - coordinateMod5Factor1r19 =
    integerCoefficientEval X coordinateMod5Factor1q19Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r18Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r19Coeffs)) (integerCoefficientMul coordinateMod5Factor1q19Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r18, coordinateMod5Factor1r19] using h
theorem coordinateMod5Factor1Frob19 : coordinateMod5Factor1 ∣ frobeniusIter 5 19 - coordinateMod5Factor1r19 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob18
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q19Coeffs, by rw [coordinateMod5Factor1Step19]; ring⟩
theorem coordinateMod5Factor1Step20 : coordinateMod5Factor1r19 ^ 5 - coordinateMod5Factor1r20 =
    integerCoefficientEval X coordinateMod5Factor1q20Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r19Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r20Coeffs)) (integerCoefficientMul coordinateMod5Factor1q20Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r19, coordinateMod5Factor1r20] using h
theorem coordinateMod5Factor1Frob20 : coordinateMod5Factor1 ∣ frobeniusIter 5 20 - coordinateMod5Factor1r20 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob19
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q20Coeffs, by rw [coordinateMod5Factor1Step20]; ring⟩
end
end Biunimodular.F11
