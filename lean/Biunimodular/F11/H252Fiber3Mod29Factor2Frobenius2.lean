/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3Mod29Factor2Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber3Mod29Factor2Step6 : h252Fiber3Mod29Factor2r5 ^ 29 - h252Fiber3Mod29Factor2r6 =
    integerCoefficientEval X h252Fiber3Mod29Factor2q6Coeffs * h252Fiber3Mod29Factor2 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor2r5Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor2r6Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor2q6Coeffs h252Fiber3Mod29Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor2, h252Fiber3Mod29Factor2r5, h252Fiber3Mod29Factor2r6] using h
theorem h252Fiber3Mod29Factor2Frob6 : h252Fiber3Mod29Factor2 ∣ frobeniusIter 29 6 - h252Fiber3Mod29Factor2r6 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor2Frob5
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor2q6Coeffs, by rw [h252Fiber3Mod29Factor2Step6]; ring⟩
theorem h252Fiber3Mod29Factor2Step7 : h252Fiber3Mod29Factor2r6 ^ 29 - h252Fiber3Mod29Factor2r7 =
    integerCoefficientEval X h252Fiber3Mod29Factor2q7Coeffs * h252Fiber3Mod29Factor2 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor2r6Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor2r7Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor2q7Coeffs h252Fiber3Mod29Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor2, h252Fiber3Mod29Factor2r6, h252Fiber3Mod29Factor2r7] using h
theorem h252Fiber3Mod29Factor2Frob7 : h252Fiber3Mod29Factor2 ∣ frobeniusIter 29 7 - h252Fiber3Mod29Factor2r7 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor2Frob6
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor2q7Coeffs, by rw [h252Fiber3Mod29Factor2Step7]; ring⟩
theorem h252Fiber3Mod29Factor2Step8 : h252Fiber3Mod29Factor2r7 ^ 29 - h252Fiber3Mod29Factor2r8 =
    integerCoefficientEval X h252Fiber3Mod29Factor2q8Coeffs * h252Fiber3Mod29Factor2 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor2r7Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor2r8Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor2q8Coeffs h252Fiber3Mod29Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor2, h252Fiber3Mod29Factor2r7, h252Fiber3Mod29Factor2r8] using h
theorem h252Fiber3Mod29Factor2Frob8 : h252Fiber3Mod29Factor2 ∣ frobeniusIter 29 8 - h252Fiber3Mod29Factor2r8 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor2Frob7
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor2q8Coeffs, by rw [h252Fiber3Mod29Factor2Step8]; ring⟩
theorem h252Fiber3Mod29Factor2Step9 : h252Fiber3Mod29Factor2r8 ^ 29 - h252Fiber3Mod29Factor2r9 =
    integerCoefficientEval X h252Fiber3Mod29Factor2q9Coeffs * h252Fiber3Mod29Factor2 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor2r8Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor2r9Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor2q9Coeffs h252Fiber3Mod29Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor2, h252Fiber3Mod29Factor2r8, h252Fiber3Mod29Factor2r9] using h
theorem h252Fiber3Mod29Factor2Frob9 : h252Fiber3Mod29Factor2 ∣ frobeniusIter 29 9 - h252Fiber3Mod29Factor2r9 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor2Frob8
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor2q9Coeffs, by rw [h252Fiber3Mod29Factor2Step9]; ring⟩
theorem h252Fiber3Mod29Factor2Step10 : h252Fiber3Mod29Factor2r9 ^ 29 - h252Fiber3Mod29Factor2r10 =
    integerCoefficientEval X h252Fiber3Mod29Factor2q10Coeffs * h252Fiber3Mod29Factor2 := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientPow h252Fiber3Mod29Factor2r9Coeffs 29) (integerCoefficientScale (-1) h252Fiber3Mod29Factor2r10Coeffs)) (integerCoefficientMul h252Fiber3Mod29Factor2q10Coeffs h252Fiber3Mod29Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber3Mod29Factor2, h252Fiber3Mod29Factor2r9, h252Fiber3Mod29Factor2r10] using h
theorem h252Fiber3Mod29Factor2Frob10 : h252Fiber3Mod29Factor2 ∣ frobeniusIter 29 10 - h252Fiber3Mod29Factor2r10 := by
  apply frobeniusIter_dvd_next h252Fiber3Mod29Factor2Frob9
  exact ⟨integerCoefficientEval X h252Fiber3Mod29Factor2q10Coeffs, by rw [h252Fiber3Mod29Factor2Step10]; ring⟩
end
end Biunimodular.F11
