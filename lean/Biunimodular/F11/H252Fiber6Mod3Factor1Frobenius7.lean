/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6Mod3Factor1Frobenius6

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber6Mod3Factor1Step31 : h252Fiber6Mod3Factor1r30 ^ 3 - h252Fiber6Mod3Factor1r31 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q31Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r30Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r31Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q31Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r30, h252Fiber6Mod3Factor1r31] using h
theorem h252Fiber6Mod3Factor1Frob31 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 31 - h252Fiber6Mod3Factor1r31 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob30
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q31Coeffs, by rw [h252Fiber6Mod3Factor1Step31]; ring⟩
theorem h252Fiber6Mod3Factor1Step32 : h252Fiber6Mod3Factor1r31 ^ 3 - h252Fiber6Mod3Factor1r32 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q32Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r31Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r32Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q32Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r31, h252Fiber6Mod3Factor1r32] using h
theorem h252Fiber6Mod3Factor1Frob32 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 32 - h252Fiber6Mod3Factor1r32 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob31
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q32Coeffs, by rw [h252Fiber6Mod3Factor1Step32]; ring⟩
theorem h252Fiber6Mod3Factor1Step33 : h252Fiber6Mod3Factor1r32 ^ 3 - h252Fiber6Mod3Factor1r33 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q33Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r32Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r33Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q33Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r32, h252Fiber6Mod3Factor1r33] using h
theorem h252Fiber6Mod3Factor1Frob33 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 33 - h252Fiber6Mod3Factor1r33 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob32
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q33Coeffs, by rw [h252Fiber6Mod3Factor1Step33]; ring⟩
theorem h252Fiber6Mod3Factor1Step34 : h252Fiber6Mod3Factor1r33 ^ 3 - h252Fiber6Mod3Factor1r34 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q34Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r33Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r34Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q34Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r33, h252Fiber6Mod3Factor1r34] using h
theorem h252Fiber6Mod3Factor1Frob34 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 34 - h252Fiber6Mod3Factor1r34 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob33
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q34Coeffs, by rw [h252Fiber6Mod3Factor1Step34]; ring⟩
theorem h252Fiber6Mod3Factor1Step35 : h252Fiber6Mod3Factor1r34 ^ 3 - h252Fiber6Mod3Factor1r35 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q35Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r34Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r35Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q35Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r34, h252Fiber6Mod3Factor1r35] using h
theorem h252Fiber6Mod3Factor1Frob35 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 35 - h252Fiber6Mod3Factor1r35 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob34
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q35Coeffs, by rw [h252Fiber6Mod3Factor1Step35]; ring⟩
end
end Biunimodular.F11
