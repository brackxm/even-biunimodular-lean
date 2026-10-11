/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4Mod3Factor1Frobenius7

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber4Mod3Factor1Step36 : h252Fiber4Mod3Factor1r35 ^ 3 - h252Fiber4Mod3Factor1r36 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q36Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r35Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r36Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q36Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r35, h252Fiber4Mod3Factor1r36] using h
theorem h252Fiber4Mod3Factor1Frob36 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 36 - h252Fiber4Mod3Factor1r36 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob35
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q36Coeffs, by rw [h252Fiber4Mod3Factor1Step36]; ring⟩
theorem h252Fiber4Mod3Factor1Step37 : h252Fiber4Mod3Factor1r36 ^ 3 - h252Fiber4Mod3Factor1r37 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q37Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r36Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r37Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q37Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r36, h252Fiber4Mod3Factor1r37] using h
theorem h252Fiber4Mod3Factor1Frob37 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 37 - h252Fiber4Mod3Factor1r37 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob36
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q37Coeffs, by rw [h252Fiber4Mod3Factor1Step37]; ring⟩
theorem h252Fiber4Mod3Factor1Step38 : h252Fiber4Mod3Factor1r37 ^ 3 - h252Fiber4Mod3Factor1r38 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q38Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r37Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r38Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q38Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r37, h252Fiber4Mod3Factor1r38] using h
theorem h252Fiber4Mod3Factor1Frob38 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 38 - h252Fiber4Mod3Factor1r38 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob37
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q38Coeffs, by rw [h252Fiber4Mod3Factor1Step38]; ring⟩
theorem h252Fiber4Mod3Factor1Step39 : h252Fiber4Mod3Factor1r38 ^ 3 - h252Fiber4Mod3Factor1r39 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q39Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r38Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r39Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q39Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r38, h252Fiber4Mod3Factor1r39] using h
theorem h252Fiber4Mod3Factor1Frob39 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 39 - h252Fiber4Mod3Factor1r39 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob38
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q39Coeffs, by rw [h252Fiber4Mod3Factor1Step39]; ring⟩
theorem h252Fiber4Mod3Factor1Step40 : h252Fiber4Mod3Factor1r39 ^ 3 - h252Fiber4Mod3Factor1r40 =
    integerCoefficientEval X h252Fiber4Mod3Factor1q40Coeffs * h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber4Mod3Factor1r39Coeffs 3) (integerCoefficientScale (-1) h252Fiber4Mod3Factor1r40Coeffs)) (integerCoefficientMul h252Fiber4Mod3Factor1q40Coeffs h252Fiber4Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber4Mod3Factor1, h252Fiber4Mod3Factor1r39, h252Fiber4Mod3Factor1r40] using h
theorem h252Fiber4Mod3Factor1Frob40 : h252Fiber4Mod3Factor1 ∣ frobeniusIter 3 40 - h252Fiber4Mod3Factor1r40 := by
  apply frobeniusIter_dvd_next h252Fiber4Mod3Factor1Frob39
  exact ⟨integerCoefficientEval X h252Fiber4Mod3Factor1q40Coeffs, by rw [h252Fiber4Mod3Factor1Step40]; ring⟩
end
end Biunimodular.F11
