/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6Mod3Factor1Frobenius9

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber6Mod3Factor1Step46 : h252Fiber6Mod3Factor1r45 ^ 3 - h252Fiber6Mod3Factor1r46 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q46Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r45Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r46Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q46Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r45, h252Fiber6Mod3Factor1r46] using h
theorem h252Fiber6Mod3Factor1Frob46 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 46 - h252Fiber6Mod3Factor1r46 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob45
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q46Coeffs, by rw [h252Fiber6Mod3Factor1Step46]; ring⟩
theorem h252Fiber6Mod3Factor1Step47 : h252Fiber6Mod3Factor1r46 ^ 3 - h252Fiber6Mod3Factor1r47 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q47Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r46Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r47Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q47Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r46, h252Fiber6Mod3Factor1r47] using h
theorem h252Fiber6Mod3Factor1Frob47 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 47 - h252Fiber6Mod3Factor1r47 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob46
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q47Coeffs, by rw [h252Fiber6Mod3Factor1Step47]; ring⟩
theorem h252Fiber6Mod3Factor1Step48 : h252Fiber6Mod3Factor1r47 ^ 3 - h252Fiber6Mod3Factor1r48 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q48Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r47Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r48Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q48Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r47, h252Fiber6Mod3Factor1r48] using h
theorem h252Fiber6Mod3Factor1Frob48 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 48 - h252Fiber6Mod3Factor1r48 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob47
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q48Coeffs, by rw [h252Fiber6Mod3Factor1Step48]; ring⟩
theorem h252Fiber6Mod3Factor1Step49 : h252Fiber6Mod3Factor1r48 ^ 3 - h252Fiber6Mod3Factor1r49 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q49Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r48Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r49Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q49Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r48, h252Fiber6Mod3Factor1r49] using h
theorem h252Fiber6Mod3Factor1Frob49 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 49 - h252Fiber6Mod3Factor1r49 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob48
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q49Coeffs, by rw [h252Fiber6Mod3Factor1Step49]; ring⟩
theorem h252Fiber6Mod3Factor1Step50 : h252Fiber6Mod3Factor1r49 ^ 3 - h252Fiber6Mod3Factor1r50 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q50Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r49Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r50Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q50Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r49, h252Fiber6Mod3Factor1r50] using h
theorem h252Fiber6Mod3Factor1Frob50 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 50 - h252Fiber6Mod3Factor1r50 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob49
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q50Coeffs, by rw [h252Fiber6Mod3Factor1Step50]; ring⟩
end
end Biunimodular.F11
