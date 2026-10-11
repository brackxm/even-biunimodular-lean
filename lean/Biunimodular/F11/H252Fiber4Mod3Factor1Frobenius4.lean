/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4Mod3Factor1Frobenius3

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber4Mod3Factor1Step16 : h252Fiber4Mod3Factor1r15 ^ 3 - h252Fiber4Mod3Factor1r16 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q16Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r15Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r16Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q16Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r15, h252Fiber4Mod3Factor1r16] using h
theorem h252Fiber4Mod3Factor1Frob16 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 16 - h252Fiber4Mod3Factor1r16 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob15
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q16Coeffs, by rw [h252Fiber4Mod3Factor1Step16]; ring⟩
theorem h252Fiber4Mod3Factor1Step17 : h252Fiber4Mod3Factor1r16 ^ 3 - h252Fiber4Mod3Factor1r17 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q17Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r16Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r17Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q17Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r16, h252Fiber4Mod3Factor1r17] using h
theorem h252Fiber4Mod3Factor1Frob17 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 17 - h252Fiber4Mod3Factor1r17 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob16
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q17Coeffs, by rw [h252Fiber4Mod3Factor1Step17]; ring⟩
theorem h252Fiber4Mod3Factor1Step18 : h252Fiber4Mod3Factor1r17 ^ 3 - h252Fiber4Mod3Factor1r18 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q18Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r17Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r18Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q18Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r17, h252Fiber4Mod3Factor1r18] using h
theorem h252Fiber4Mod3Factor1Frob18 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 18 - h252Fiber4Mod3Factor1r18 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob17
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q18Coeffs, by rw [h252Fiber4Mod3Factor1Step18]; ring⟩
theorem h252Fiber4Mod3Factor1Step19 : h252Fiber4Mod3Factor1r18 ^ 3 - h252Fiber4Mod3Factor1r19 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q19Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r18Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r19Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q19Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r18, h252Fiber4Mod3Factor1r19] using h
theorem h252Fiber4Mod3Factor1Frob19 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 19 - h252Fiber4Mod3Factor1r19 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob18
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q19Coeffs, by rw [h252Fiber4Mod3Factor1Step19]; ring⟩
theorem h252Fiber4Mod3Factor1Step20 : h252Fiber4Mod3Factor1r19 ^ 3 - h252Fiber4Mod3Factor1r20 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q20Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r19Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r20Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q20Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r19, h252Fiber4Mod3Factor1r20] using h
theorem h252Fiber4Mod3Factor1Frob20 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 20 - h252Fiber4Mod3Factor1r20 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob19
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q20Coeffs, by rw [h252Fiber4Mod3Factor1Step20]; ring⟩
end
end Biunimodular.F11
