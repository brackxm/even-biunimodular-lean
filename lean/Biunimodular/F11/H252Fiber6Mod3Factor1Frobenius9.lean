/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6Mod3Factor1Frobenius8

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber6Mod3Factor1Step41 : h252Fiber6Mod3Factor1r40 ^ 3 - h252Fiber6Mod3Factor1r41 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q41Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r40Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r41Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q41Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r40, h252Fiber6Mod3Factor1r41] using h
theorem h252Fiber6Mod3Factor1Frob41 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 41 - h252Fiber6Mod3Factor1r41 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob40
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q41Coeffs, by rw [h252Fiber6Mod3Factor1Step41]; ring⟩
theorem h252Fiber6Mod3Factor1Step42 : h252Fiber6Mod3Factor1r41 ^ 3 - h252Fiber6Mod3Factor1r42 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q42Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r41Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r42Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q42Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r41, h252Fiber6Mod3Factor1r42] using h
theorem h252Fiber6Mod3Factor1Frob42 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 42 - h252Fiber6Mod3Factor1r42 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob41
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q42Coeffs, by rw [h252Fiber6Mod3Factor1Step42]; ring⟩
theorem h252Fiber6Mod3Factor1Step43 : h252Fiber6Mod3Factor1r42 ^ 3 - h252Fiber6Mod3Factor1r43 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q43Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r42Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r43Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q43Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r42, h252Fiber6Mod3Factor1r43] using h
theorem h252Fiber6Mod3Factor1Frob43 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 43 - h252Fiber6Mod3Factor1r43 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob42
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q43Coeffs, by rw [h252Fiber6Mod3Factor1Step43]; ring⟩
theorem h252Fiber6Mod3Factor1Step44 : h252Fiber6Mod3Factor1r43 ^ 3 - h252Fiber6Mod3Factor1r44 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q44Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r43Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r44Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q44Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r43, h252Fiber6Mod3Factor1r44] using h
theorem h252Fiber6Mod3Factor1Frob44 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 44 - h252Fiber6Mod3Factor1r44 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob43
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q44Coeffs, by rw [h252Fiber6Mod3Factor1Step44]; ring⟩
theorem h252Fiber6Mod3Factor1Step45 : h252Fiber6Mod3Factor1r44 ^ 3 - h252Fiber6Mod3Factor1r45 =
    integerCoefficientEval X h252Fiber6Mod3Factor1q45Coeffs * h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientPow h252Fiber6Mod3Factor1r44Coeffs 3) (integerCoefficientScale (-1) h252Fiber6Mod3Factor1r45Coeffs)) (integerCoefficientMul h252Fiber6Mod3Factor1q45Coeffs h252Fiber6Mod3Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r44, h252Fiber6Mod3Factor1r45] using h
theorem h252Fiber6Mod3Factor1Frob45 : h252Fiber6Mod3Factor1 ∣ frobeniusIter 3 45 - h252Fiber6Mod3Factor1r45 := by
  apply frobeniusIter_dvd_next h252Fiber6Mod3Factor1Frob44
  exact ⟨integerCoefficientEval X h252Fiber6Mod3Factor1q45Coeffs, by rw [h252Fiber6Mod3Factor1Step45]; ring⟩
end
end Biunimodular.F11
