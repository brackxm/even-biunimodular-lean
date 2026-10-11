/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6Mod3Factor1Frobenius10

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber6Mod3Factor1Step51 : h252Fiber6Mod3Factor1r50 ^ 3 - h252Fiber6Mod3Factor1r51 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q51Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r50Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r51Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q51Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r50, h252Fiber6Mod3Factor1r51] using h
theorem h252Fiber6Mod3Factor1Frob51 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 51 - h252Fiber6Mod3Factor1r51 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob50
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q51Coeffs, by rw [h252Fiber6Mod3Factor1Step51]; ring⟩
theorem h252Fiber6Mod3Factor1Step52 : h252Fiber6Mod3Factor1r51 ^ 3 - h252Fiber6Mod3Factor1r52 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q52Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r51Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r52Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q52Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r51, h252Fiber6Mod3Factor1r52] using h
theorem h252Fiber6Mod3Factor1Frob52 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 52 - h252Fiber6Mod3Factor1r52 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob51
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q52Coeffs, by rw [h252Fiber6Mod3Factor1Step52]; ring⟩
theorem h252Fiber6Mod3Factor1Step53 : h252Fiber6Mod3Factor1r52 ^ 3 - h252Fiber6Mod3Factor1r53 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q53Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r52Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r53Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q53Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r52, h252Fiber6Mod3Factor1r53] using h
theorem h252Fiber6Mod3Factor1Frob53 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 53 - h252Fiber6Mod3Factor1r53 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob52
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q53Coeffs, by rw [h252Fiber6Mod3Factor1Step53]; ring⟩
theorem h252Fiber6Mod3Factor1Step54 : h252Fiber6Mod3Factor1r53 ^ 3 - h252Fiber6Mod3Factor1r54 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q54Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r53Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r54Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q54Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r53, h252Fiber6Mod3Factor1r54] using h
theorem h252Fiber6Mod3Factor1Frob54 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 54 - h252Fiber6Mod3Factor1r54 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob53
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q54Coeffs, by rw [h252Fiber6Mod3Factor1Step54]; ring⟩
theorem h252Fiber6Mod3Factor1Step55 : h252Fiber6Mod3Factor1r54 ^ 3 - h252Fiber6Mod3Factor1r55 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q55Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r54Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r55Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q55Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r54, h252Fiber6Mod3Factor1r55] using h
theorem h252Fiber6Mod3Factor1Frob55 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 55 - h252Fiber6Mod3Factor1r55 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob54
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q55Coeffs, by rw [h252Fiber6Mod3Factor1Step55]; ring⟩
end
end Biunimodular.F11
