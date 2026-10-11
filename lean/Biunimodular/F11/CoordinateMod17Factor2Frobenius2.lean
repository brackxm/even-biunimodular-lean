/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor2Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor2Step6 : coordinateMod17Factor2r5 ^ 17 - coordinateMod17Factor2r6 =
    integerCoefficientEval X coordinateMod17Factor2q6Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r5Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r6Coeffs)) (integerCoefficientMul coordinateMod17Factor2q6Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r5, coordinateMod17Factor2r6] using h
theorem coordinateMod17Factor2Frob6 : coordinateMod17Factor2 ∣ frobeniusIter 17 6 - coordinateMod17Factor2r6 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob5
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q6Coeffs, by rw [coordinateMod17Factor2Step6]; ring⟩
theorem coordinateMod17Factor2Step7 : coordinateMod17Factor2r6 ^ 17 - coordinateMod17Factor2r7 =
    integerCoefficientEval X coordinateMod17Factor2q7Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r6Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r7Coeffs)) (integerCoefficientMul coordinateMod17Factor2q7Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r6, coordinateMod17Factor2r7] using h
theorem coordinateMod17Factor2Frob7 : coordinateMod17Factor2 ∣ frobeniusIter 17 7 - coordinateMod17Factor2r7 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob6
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q7Coeffs, by rw [coordinateMod17Factor2Step7]; ring⟩
theorem coordinateMod17Factor2Step8 : coordinateMod17Factor2r7 ^ 17 - coordinateMod17Factor2r8 =
    integerCoefficientEval X coordinateMod17Factor2q8Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r7Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r8Coeffs)) (integerCoefficientMul coordinateMod17Factor2q8Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r7, coordinateMod17Factor2r8] using h
theorem coordinateMod17Factor2Frob8 : coordinateMod17Factor2 ∣ frobeniusIter 17 8 - coordinateMod17Factor2r8 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob7
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q8Coeffs, by rw [coordinateMod17Factor2Step8]; ring⟩
theorem coordinateMod17Factor2Step9 : coordinateMod17Factor2r8 ^ 17 - coordinateMod17Factor2r9 =
    integerCoefficientEval X coordinateMod17Factor2q9Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r8Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r9Coeffs)) (integerCoefficientMul coordinateMod17Factor2q9Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r8, coordinateMod17Factor2r9] using h
theorem coordinateMod17Factor2Frob9 : coordinateMod17Factor2 ∣ frobeniusIter 17 9 - coordinateMod17Factor2r9 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob8
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q9Coeffs, by rw [coordinateMod17Factor2Step9]; ring⟩
theorem coordinateMod17Factor2Step10 : coordinateMod17Factor2r9 ^ 17 - coordinateMod17Factor2r10 =
    integerCoefficientEval X coordinateMod17Factor2q10Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r9Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r10Coeffs)) (integerCoefficientMul coordinateMod17Factor2q10Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r9, coordinateMod17Factor2r10] using h
theorem coordinateMod17Factor2Frob10 : coordinateMod17Factor2 ∣ frobeniusIter 17 10 - coordinateMod17Factor2r10 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob9
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q10Coeffs, by rw [coordinateMod17Factor2Step10]; ring⟩
end
end Biunimodular.F11
