/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4Mod3Factor1Frobenius2

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber4Mod3Factor1Step11 : h252Fiber4Mod3Factor1r10 ^ 3 - h252Fiber4Mod3Factor1r11 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q11Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r10Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r11Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q11Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r10, h252Fiber4Mod3Factor1r11] using h
theorem h252Fiber4Mod3Factor1Frob11 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 11 - h252Fiber4Mod3Factor1r11 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob10
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q11Coeffs, by rw [h252Fiber4Mod3Factor1Step11]; ring⟩
theorem h252Fiber4Mod3Factor1Step12 : h252Fiber4Mod3Factor1r11 ^ 3 - h252Fiber4Mod3Factor1r12 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q12Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r11Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r12Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q12Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r11, h252Fiber4Mod3Factor1r12] using h
theorem h252Fiber4Mod3Factor1Frob12 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 12 - h252Fiber4Mod3Factor1r12 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob11
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q12Coeffs, by rw [h252Fiber4Mod3Factor1Step12]; ring⟩
theorem h252Fiber4Mod3Factor1Step13 : h252Fiber4Mod3Factor1r12 ^ 3 - h252Fiber4Mod3Factor1r13 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q13Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r12Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r13Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q13Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r12, h252Fiber4Mod3Factor1r13] using h
theorem h252Fiber4Mod3Factor1Frob13 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 13 - h252Fiber4Mod3Factor1r13 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob12
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q13Coeffs, by rw [h252Fiber4Mod3Factor1Step13]; ring⟩
theorem h252Fiber4Mod3Factor1Step14 : h252Fiber4Mod3Factor1r13 ^ 3 - h252Fiber4Mod3Factor1r14 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q14Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r13Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r14Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q14Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r13, h252Fiber4Mod3Factor1r14] using h
theorem h252Fiber4Mod3Factor1Frob14 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 14 - h252Fiber4Mod3Factor1r14 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob13
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q14Coeffs, by rw [h252Fiber4Mod3Factor1Step14]; ring⟩
theorem h252Fiber4Mod3Factor1Step15 : h252Fiber4Mod3Factor1r14 ^ 3 - h252Fiber4Mod3Factor1r15 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q15Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r14Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r15Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q15Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r14, h252Fiber4Mod3Factor1r15] using h
theorem h252Fiber4Mod3Factor1Frob15 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 15 - h252Fiber4Mod3Factor1r15 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob14
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q15Coeffs, by rw [h252Fiber4Mod3Factor1Step15]; ring⟩
end
end Biunimodular.F11
