/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4Mod3Factor1Frobenius5

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber4Mod3Factor1Step26 : h252Fiber4Mod3Factor1r25 ^ 3 - h252Fiber4Mod3Factor1r26 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q26Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r25Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r26Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q26Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r25, h252Fiber4Mod3Factor1r26] using h
theorem h252Fiber4Mod3Factor1Frob26 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 26 - h252Fiber4Mod3Factor1r26 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob25
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q26Coeffs, by rw [h252Fiber4Mod3Factor1Step26]; ring⟩
theorem h252Fiber4Mod3Factor1Step27 : h252Fiber4Mod3Factor1r26 ^ 3 - h252Fiber4Mod3Factor1r27 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q27Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r26Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r27Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q27Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r26, h252Fiber4Mod3Factor1r27] using h
theorem h252Fiber4Mod3Factor1Frob27 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 27 - h252Fiber4Mod3Factor1r27 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob26
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q27Coeffs, by rw [h252Fiber4Mod3Factor1Step27]; ring⟩
theorem h252Fiber4Mod3Factor1Step28 : h252Fiber4Mod3Factor1r27 ^ 3 - h252Fiber4Mod3Factor1r28 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q28Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r27Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r28Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q28Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r27, h252Fiber4Mod3Factor1r28] using h
theorem h252Fiber4Mod3Factor1Frob28 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 28 - h252Fiber4Mod3Factor1r28 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob27
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q28Coeffs, by rw [h252Fiber4Mod3Factor1Step28]; ring⟩
theorem h252Fiber4Mod3Factor1Step29 : h252Fiber4Mod3Factor1r28 ^ 3 - h252Fiber4Mod3Factor1r29 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q29Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r28Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r29Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q29Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r28, h252Fiber4Mod3Factor1r29] using h
theorem h252Fiber4Mod3Factor1Frob29 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 29 - h252Fiber4Mod3Factor1r29 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob28
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q29Coeffs, by rw [h252Fiber4Mod3Factor1Step29]; ring⟩
theorem h252Fiber4Mod3Factor1Step30 : h252Fiber4Mod3Factor1r29 ^ 3 - h252Fiber4Mod3Factor1r30 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q30Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r29Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r30Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q30Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r29, h252Fiber4Mod3Factor1r30] using h
theorem h252Fiber4Mod3Factor1Frob30 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 30 - h252Fiber4Mod3Factor1r30 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob29
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q30Coeffs, by rw [h252Fiber4Mod3Factor1Step30]; ring⟩
end
end Biunimodular.F11
