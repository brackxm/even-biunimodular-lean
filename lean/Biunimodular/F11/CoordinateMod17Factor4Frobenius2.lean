/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor4Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor4Step6 : coordinateMod17Factor4r5 ^ 17 - coordinateMod17Factor4r6 =
    integerCoefficientEval X coordinateMod17Factor4q6Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r5Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r6Coeffs)) (integerCoefficientMul coordinateMod17Factor4q6Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r5, coordinateMod17Factor4r6] using h
theorem coordinateMod17Factor4Frob6 : coordinateMod17Factor4 ∣ frobeniusIter 17 6 - coordinateMod17Factor4r6 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob5
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q6Coeffs, by rw [coordinateMod17Factor4Step6]; ring⟩
theorem coordinateMod17Factor4Step7 : coordinateMod17Factor4r6 ^ 17 - coordinateMod17Factor4r7 =
    integerCoefficientEval X coordinateMod17Factor4q7Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r6Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r7Coeffs)) (integerCoefficientMul coordinateMod17Factor4q7Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r6, coordinateMod17Factor4r7] using h
theorem coordinateMod17Factor4Frob7 : coordinateMod17Factor4 ∣ frobeniusIter 17 7 - coordinateMod17Factor4r7 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob6
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q7Coeffs, by rw [coordinateMod17Factor4Step7]; ring⟩
theorem coordinateMod17Factor4Step8 : coordinateMod17Factor4r7 ^ 17 - coordinateMod17Factor4r8 =
    integerCoefficientEval X coordinateMod17Factor4q8Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r7Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r8Coeffs)) (integerCoefficientMul coordinateMod17Factor4q8Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r7, coordinateMod17Factor4r8] using h
theorem coordinateMod17Factor4Frob8 : coordinateMod17Factor4 ∣ frobeniusIter 17 8 - coordinateMod17Factor4r8 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob7
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q8Coeffs, by rw [coordinateMod17Factor4Step8]; ring⟩
theorem coordinateMod17Factor4Step9 : coordinateMod17Factor4r8 ^ 17 - coordinateMod17Factor4r9 =
    integerCoefficientEval X coordinateMod17Factor4q9Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r8Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r9Coeffs)) (integerCoefficientMul coordinateMod17Factor4q9Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r8, coordinateMod17Factor4r9] using h
theorem coordinateMod17Factor4Frob9 : coordinateMod17Factor4 ∣ frobeniusIter 17 9 - coordinateMod17Factor4r9 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob8
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q9Coeffs, by rw [coordinateMod17Factor4Step9]; ring⟩
theorem coordinateMod17Factor4Step10 : coordinateMod17Factor4r9 ^ 17 - coordinateMod17Factor4r10 =
    integerCoefficientEval X coordinateMod17Factor4q10Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r9Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r10Coeffs)) (integerCoefficientMul coordinateMod17Factor4q10Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r9, coordinateMod17Factor4r10] using h
theorem coordinateMod17Factor4Frob10 : coordinateMod17Factor4 ∣ frobeniusIter 17 10 - coordinateMod17Factor4r10 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob9
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q10Coeffs, by rw [coordinateMod17Factor4Step10]; ring⟩
end
end Biunimodular.F11
