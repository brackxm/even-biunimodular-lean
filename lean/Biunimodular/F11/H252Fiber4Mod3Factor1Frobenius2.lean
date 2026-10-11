/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4Mod3Factor1Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber4Mod3Factor1Step6 : h252Fiber4Mod3Factor1r5 ^ 3 - h252Fiber4Mod3Factor1r6 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q6Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r5Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r6Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q6Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r5, h252Fiber4Mod3Factor1r6] using h
theorem h252Fiber4Mod3Factor1Frob6 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 6 - h252Fiber4Mod3Factor1r6 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob5
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q6Coeffs, by rw [h252Fiber4Mod3Factor1Step6]; ring⟩
theorem h252Fiber4Mod3Factor1Step7 : h252Fiber4Mod3Factor1r6 ^ 3 - h252Fiber4Mod3Factor1r7 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q7Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r6Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r7Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q7Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r6, h252Fiber4Mod3Factor1r7] using h
theorem h252Fiber4Mod3Factor1Frob7 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 7 - h252Fiber4Mod3Factor1r7 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob6
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q7Coeffs, by rw [h252Fiber4Mod3Factor1Step7]; ring⟩
theorem h252Fiber4Mod3Factor1Step8 : h252Fiber4Mod3Factor1r7 ^ 3 - h252Fiber4Mod3Factor1r8 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q8Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r7Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r8Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q8Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r7, h252Fiber4Mod3Factor1r8] using h
theorem h252Fiber4Mod3Factor1Frob8 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 8 - h252Fiber4Mod3Factor1r8 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob7
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q8Coeffs, by rw [h252Fiber4Mod3Factor1Step8]; ring⟩
theorem h252Fiber4Mod3Factor1Step9 : h252Fiber4Mod3Factor1r8 ^ 3 - h252Fiber4Mod3Factor1r9 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q9Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r8Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r9Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q9Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r8, h252Fiber4Mod3Factor1r9] using h
theorem h252Fiber4Mod3Factor1Frob9 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 9 - h252Fiber4Mod3Factor1r9 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob8
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q9Coeffs, by rw [h252Fiber4Mod3Factor1Step9]; ring⟩
theorem h252Fiber4Mod3Factor1Step10 : h252Fiber4Mod3Factor1r9 ^ 3 - h252Fiber4Mod3Factor1r10 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q10Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r9Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r10Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q10Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r9, h252Fiber4Mod3Factor1r10] using h
theorem h252Fiber4Mod3Factor1Frob10 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 10 - h252Fiber4Mod3Factor1r10 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob9
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q10Coeffs, by rw [h252Fiber4Mod3Factor1Step10]; ring⟩
end
end Biunimodular.F11
