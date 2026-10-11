/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor3Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor3Step6 : coordinateMod17Factor3r5 ^ 17 - coordinateMod17Factor3r6 =
    integerCoefficientEval X coordinateMod17Factor3q6Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r5Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r6Coeffs)) (integerCoefficientMul coordinateMod17Factor3q6Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r5, coordinateMod17Factor3r6] using h
theorem coordinateMod17Factor3Frob6 : coordinateMod17Factor3 ∣ frobeniusIter 17 6 - coordinateMod17Factor3r6 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob5
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q6Coeffs, by rw [coordinateMod17Factor3Step6]; ring⟩
theorem coordinateMod17Factor3Step7 : coordinateMod17Factor3r6 ^ 17 - coordinateMod17Factor3r7 =
    integerCoefficientEval X coordinateMod17Factor3q7Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r6Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r7Coeffs)) (integerCoefficientMul coordinateMod17Factor3q7Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r6, coordinateMod17Factor3r7] using h
theorem coordinateMod17Factor3Frob7 : coordinateMod17Factor3 ∣ frobeniusIter 17 7 - coordinateMod17Factor3r7 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob6
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q7Coeffs, by rw [coordinateMod17Factor3Step7]; ring⟩
theorem coordinateMod17Factor3Step8 : coordinateMod17Factor3r7 ^ 17 - coordinateMod17Factor3r8 =
    integerCoefficientEval X coordinateMod17Factor3q8Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r7Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r8Coeffs)) (integerCoefficientMul coordinateMod17Factor3q8Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r7, coordinateMod17Factor3r8] using h
theorem coordinateMod17Factor3Frob8 : coordinateMod17Factor3 ∣ frobeniusIter 17 8 - coordinateMod17Factor3r8 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob7
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q8Coeffs, by rw [coordinateMod17Factor3Step8]; ring⟩
theorem coordinateMod17Factor3Step9 : coordinateMod17Factor3r8 ^ 17 - coordinateMod17Factor3r9 =
    integerCoefficientEval X coordinateMod17Factor3q9Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r8Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r9Coeffs)) (integerCoefficientMul coordinateMod17Factor3q9Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r8, coordinateMod17Factor3r9] using h
theorem coordinateMod17Factor3Frob9 : coordinateMod17Factor3 ∣ frobeniusIter 17 9 - coordinateMod17Factor3r9 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob8
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q9Coeffs, by rw [coordinateMod17Factor3Step9]; ring⟩
theorem coordinateMod17Factor3Step10 : coordinateMod17Factor3r9 ^ 17 - coordinateMod17Factor3r10 =
    integerCoefficientEval X coordinateMod17Factor3q10Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r9Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r10Coeffs)) (integerCoefficientMul coordinateMod17Factor3q10Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r9, coordinateMod17Factor3r10] using h
theorem coordinateMod17Factor3Frob10 : coordinateMod17Factor3 ∣ frobeniusIter 17 10 - coordinateMod17Factor3r10 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob9
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q10Coeffs, by rw [coordinateMod17Factor3Step10]; ring⟩
end
end Biunimodular.F11
