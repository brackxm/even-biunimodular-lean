/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3Mod29Factor1Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber3Mod29Factor1Frob0 : h252Fiber3Mod29Factor1 ∣ frobeniusIter 29 0 - h252Fiber3Mod29Factor1r0 := by
  simp [h252Fiber3Mod29Factor1r0, h252Fiber3Mod29Factor1r0Coeffs, frobeniusIter, integerCoefficientEval]
theorem h252Fiber3Mod29Factor1Step1 : h252Fiber3Mod29Factor1r0 ^ 29 - h252Fiber3Mod29Factor1r1 =
    integerCoefficientEval X h252Fiber3Mod29Factor1q1Coeffs * h252Fiber3Mod29Factor1 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor1r0Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor1r1Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor1q1Coeffs h252Fiber3Mod29Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1r0, h252Fiber3Mod29Factor1r1] using h
theorem h252Fiber3Mod29Factor1Frob1 : h252Fiber3Mod29Factor1 ∣ frobeniusIter 29 1 - h252Fiber3Mod29Factor1r1 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor1Frob0
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor1q1Coeffs, by rw [h252Fiber3Mod29Factor1Step1]; ring⟩
theorem h252Fiber3Mod29Factor1Step2 : h252Fiber3Mod29Factor1r1 ^ 29 - h252Fiber3Mod29Factor1r2 =
    integerCoefficientEval X h252Fiber3Mod29Factor1q2Coeffs * h252Fiber3Mod29Factor1 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor1r1Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor1r2Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor1q2Coeffs h252Fiber3Mod29Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1r1, h252Fiber3Mod29Factor1r2] using h
theorem h252Fiber3Mod29Factor1Frob2 : h252Fiber3Mod29Factor1 ∣ frobeniusIter 29 2 - h252Fiber3Mod29Factor1r2 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor1Frob1
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor1q2Coeffs, by rw [h252Fiber3Mod29Factor1Step2]; ring⟩
theorem h252Fiber3Mod29Factor1Step3 : h252Fiber3Mod29Factor1r2 ^ 29 - h252Fiber3Mod29Factor1r3 =
    integerCoefficientEval X h252Fiber3Mod29Factor1q3Coeffs * h252Fiber3Mod29Factor1 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor1r2Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor1r3Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor1q3Coeffs h252Fiber3Mod29Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1r2, h252Fiber3Mod29Factor1r3] using h
theorem h252Fiber3Mod29Factor1Frob3 : h252Fiber3Mod29Factor1 ∣ frobeniusIter 29 3 - h252Fiber3Mod29Factor1r3 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor1Frob2
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor1q3Coeffs, by rw [h252Fiber3Mod29Factor1Step3]; ring⟩
theorem h252Fiber3Mod29Factor1Step4 : h252Fiber3Mod29Factor1r3 ^ 29 - h252Fiber3Mod29Factor1r4 =
    integerCoefficientEval X h252Fiber3Mod29Factor1q4Coeffs * h252Fiber3Mod29Factor1 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor1r3Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor1r4Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor1q4Coeffs h252Fiber3Mod29Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1r3, h252Fiber3Mod29Factor1r4] using h
theorem h252Fiber3Mod29Factor1Frob4 : h252Fiber3Mod29Factor1 ∣ frobeniusIter 29 4 - h252Fiber3Mod29Factor1r4 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor1Frob3
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor1q4Coeffs, by rw [h252Fiber3Mod29Factor1Step4]; ring⟩
theorem h252Fiber3Mod29Factor1Step5 : h252Fiber3Mod29Factor1r4 ^ 29 - h252Fiber3Mod29Factor1r5 =
    integerCoefficientEval X h252Fiber3Mod29Factor1q5Coeffs * h252Fiber3Mod29Factor1 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor1r4Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor1r5Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor1q5Coeffs h252Fiber3Mod29Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1r4, h252Fiber3Mod29Factor1r5] using h
theorem h252Fiber3Mod29Factor1Frob5 : h252Fiber3Mod29Factor1 ∣ frobeniusIter 29 5 - h252Fiber3Mod29Factor1r5 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor1Frob4
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor1q5Coeffs, by rw [h252Fiber3Mod29Factor1Step5]; ring⟩
end
end Biunimodular.F11
