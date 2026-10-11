/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6Mod3Factor1Frobenius11

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber6Mod3Factor1Step56 : h252Fiber6Mod3Factor1r55 ^ 3 - h252Fiber6Mod3Factor1r56 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q56Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r55Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r56Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q56Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r55, h252Fiber6Mod3Factor1r56] using h
theorem h252Fiber6Mod3Factor1Frob56 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 56 - h252Fiber6Mod3Factor1r56 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob55
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q56Coeffs, by rw [h252Fiber6Mod3Factor1Step56]; ring⟩
theorem h252Fiber6Mod3Factor1Step57 : h252Fiber6Mod3Factor1r56 ^ 3 - h252Fiber6Mod3Factor1r57 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q57Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r56Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r57Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q57Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r56, h252Fiber6Mod3Factor1r57] using h
theorem h252Fiber6Mod3Factor1Frob57 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 57 - h252Fiber6Mod3Factor1r57 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob56
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q57Coeffs, by rw [h252Fiber6Mod3Factor1Step57]; ring⟩
theorem h252Fiber6Mod3Factor1Step58 : h252Fiber6Mod3Factor1r57 ^ 3 - h252Fiber6Mod3Factor1r58 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q58Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r57Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r58Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q58Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r57, h252Fiber6Mod3Factor1r58] using h
theorem h252Fiber6Mod3Factor1Frob58 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 58 - h252Fiber6Mod3Factor1r58 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob57
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q58Coeffs, by rw [h252Fiber6Mod3Factor1Step58]; ring⟩
theorem h252Fiber6Mod3Factor1Step59 : h252Fiber6Mod3Factor1r58 ^ 3 - h252Fiber6Mod3Factor1r59 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q59Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r58Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r59Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q59Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r58, h252Fiber6Mod3Factor1r59] using h
theorem h252Fiber6Mod3Factor1Frob59 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 59 - h252Fiber6Mod3Factor1r59 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob58
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q59Coeffs, by rw [h252Fiber6Mod3Factor1Step59]; ring⟩
theorem h252Fiber6Mod3Factor1Step60 : h252Fiber6Mod3Factor1r59 ^ 3 - h252Fiber6Mod3Factor1r60 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q60Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r59Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r60Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q60Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r59, h252Fiber6Mod3Factor1r60] using h
theorem h252Fiber6Mod3Factor1Frob60 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 60 - h252Fiber6Mod3Factor1r60 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob59
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q60Coeffs, by rw [h252Fiber6Mod3Factor1Step60]; ring⟩
end
end Biunimodular.F11
