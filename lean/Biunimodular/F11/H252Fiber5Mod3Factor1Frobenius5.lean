/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber5Mod3Factor1Frobenius4

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber5Mod3Factor1Step21 : h252Fiber5Mod3Factor1r20 ^ 3 - h252Fiber5Mod3Factor1r21 =
    integerCoefficientEval X h252Fiber5Mod3Factor1q21Coeffs * h252Fiber5Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber5Mod3Factor1r20Coeffs 3) (integerCoefficientScale (-1) h252Fiber5Mod3Factor1r21Coeffs)) (integerCoefficientMul h252Fiber5Mod3Factor1q21Coeffs h252Fiber5Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber5Mod3Factor1, h252Fiber5Mod3Factor1r20, h252Fiber5Mod3Factor1r21] using h
theorem h252Fiber5Mod3Factor1Frob21 : h252Fiber5Mod3Factor1 ∣ frobeniusIter 3 21 - h252Fiber5Mod3Factor1r21 := by
  apply frobeniusIter_dvd_next h252Fiber5Mod3Factor1Frob20
  exact ⟨integerCoefficientEval X h252Fiber5Mod3Factor1q21Coeffs, by rw [h252Fiber5Mod3Factor1Step21]; ring⟩
theorem h252Fiber5Mod3Factor1Step22 : h252Fiber5Mod3Factor1r21 ^ 3 - h252Fiber5Mod3Factor1r22 =
    integerCoefficientEval X h252Fiber5Mod3Factor1q22Coeffs * h252Fiber5Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber5Mod3Factor1r21Coeffs 3) (integerCoefficientScale (-1) h252Fiber5Mod3Factor1r22Coeffs)) (integerCoefficientMul h252Fiber5Mod3Factor1q22Coeffs h252Fiber5Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber5Mod3Factor1, h252Fiber5Mod3Factor1r21, h252Fiber5Mod3Factor1r22] using h
theorem h252Fiber5Mod3Factor1Frob22 : h252Fiber5Mod3Factor1 ∣ frobeniusIter 3 22 - h252Fiber5Mod3Factor1r22 := by
  apply frobeniusIter_dvd_next h252Fiber5Mod3Factor1Frob21
  exact ⟨integerCoefficientEval X h252Fiber5Mod3Factor1q22Coeffs, by rw [h252Fiber5Mod3Factor1Step22]; ring⟩
theorem h252Fiber5Mod3Factor1Step23 : h252Fiber5Mod3Factor1r22 ^ 3 - h252Fiber5Mod3Factor1r23 =
    integerCoefficientEval X h252Fiber5Mod3Factor1q23Coeffs * h252Fiber5Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber5Mod3Factor1r22Coeffs 3) (integerCoefficientScale (-1) h252Fiber5Mod3Factor1r23Coeffs)) (integerCoefficientMul h252Fiber5Mod3Factor1q23Coeffs h252Fiber5Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber5Mod3Factor1, h252Fiber5Mod3Factor1r22, h252Fiber5Mod3Factor1r23] using h
theorem h252Fiber5Mod3Factor1Frob23 : h252Fiber5Mod3Factor1 ∣ frobeniusIter 3 23 - h252Fiber5Mod3Factor1r23 := by
  apply frobeniusIter_dvd_next h252Fiber5Mod3Factor1Frob22
  exact ⟨integerCoefficientEval X h252Fiber5Mod3Factor1q23Coeffs, by rw [h252Fiber5Mod3Factor1Step23]; ring⟩
theorem h252Fiber5Mod3Factor1Step24 : h252Fiber5Mod3Factor1r23 ^ 3 - h252Fiber5Mod3Factor1r24 =
    integerCoefficientEval X h252Fiber5Mod3Factor1q24Coeffs * h252Fiber5Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber5Mod3Factor1r23Coeffs 3) (integerCoefficientScale (-1) h252Fiber5Mod3Factor1r24Coeffs)) (integerCoefficientMul h252Fiber5Mod3Factor1q24Coeffs h252Fiber5Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber5Mod3Factor1, h252Fiber5Mod3Factor1r23, h252Fiber5Mod3Factor1r24] using h
theorem h252Fiber5Mod3Factor1Frob24 : h252Fiber5Mod3Factor1 ∣ frobeniusIter 3 24 - h252Fiber5Mod3Factor1r24 := by
  apply frobeniusIter_dvd_next h252Fiber5Mod3Factor1Frob23
  exact ⟨integerCoefficientEval X h252Fiber5Mod3Factor1q24Coeffs, by rw [h252Fiber5Mod3Factor1Step24]; ring⟩
theorem h252Fiber5Mod3Factor1Step25 : h252Fiber5Mod3Factor1r24 ^ 3 - h252Fiber5Mod3Factor1r25 =
    integerCoefficientEval X h252Fiber5Mod3Factor1q25Coeffs * h252Fiber5Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber5Mod3Factor1r24Coeffs 3) (integerCoefficientScale (-1) h252Fiber5Mod3Factor1r25Coeffs)) (integerCoefficientMul h252Fiber5Mod3Factor1q25Coeffs h252Fiber5Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber5Mod3Factor1, h252Fiber5Mod3Factor1r24, h252Fiber5Mod3Factor1r25] using h
theorem h252Fiber5Mod3Factor1Frob25 : h252Fiber5Mod3Factor1 ∣ frobeniusIter 3 25 - h252Fiber5Mod3Factor1r25 := by
  apply frobeniusIter_dvd_next h252Fiber5Mod3Factor1Frob24
  exact ⟨integerCoefficientEval X h252Fiber5Mod3Factor1q25Coeffs, by rw [h252Fiber5Mod3Factor1Step25]; ring⟩
end
end Biunimodular.F11
