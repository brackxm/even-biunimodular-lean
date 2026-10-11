/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor3Frobenius3

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor3Step16 : coordinateMod17Factor3r15 ^ 17 - coordinateMod17Factor3r16 =
    integerCoefficientEval X coordinateMod17Factor3q16Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r15Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r16Coeffs)) (integerCoefficientMul coordinateMod17Factor3q16Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r15, coordinateMod17Factor3r16] using h
theorem coordinateMod17Factor3Frob16 : coordinateMod17Factor3 ∣ frobeniusIter 17 16 - coordinateMod17Factor3r16 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob15
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q16Coeffs, by rw [coordinateMod17Factor3Step16]; ring⟩
theorem coordinateMod17Factor3Step17 : coordinateMod17Factor3r16 ^ 17 - coordinateMod17Factor3r17 =
    integerCoefficientEval X coordinateMod17Factor3q17Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r16Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r17Coeffs)) (integerCoefficientMul coordinateMod17Factor3q17Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r16, coordinateMod17Factor3r17] using h
theorem coordinateMod17Factor3Frob17 : coordinateMod17Factor3 ∣ frobeniusIter 17 17 - coordinateMod17Factor3r17 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob16
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q17Coeffs, by rw [coordinateMod17Factor3Step17]; ring⟩
theorem coordinateMod17Factor3Step18 : coordinateMod17Factor3r17 ^ 17 - coordinateMod17Factor3r18 =
    integerCoefficientEval X coordinateMod17Factor3q18Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r17Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r18Coeffs)) (integerCoefficientMul coordinateMod17Factor3q18Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r17, coordinateMod17Factor3r18] using h
theorem coordinateMod17Factor3Frob18 : coordinateMod17Factor3 ∣ frobeniusIter 17 18 - coordinateMod17Factor3r18 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob17
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q18Coeffs, by rw [coordinateMod17Factor3Step18]; ring⟩
theorem coordinateMod17Factor3Step19 : coordinateMod17Factor3r18 ^ 17 - coordinateMod17Factor3r19 =
    integerCoefficientEval X coordinateMod17Factor3q19Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r18Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r19Coeffs)) (integerCoefficientMul coordinateMod17Factor3q19Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r18, coordinateMod17Factor3r19] using h
theorem coordinateMod17Factor3Frob19 : coordinateMod17Factor3 ∣ frobeniusIter 17 19 - coordinateMod17Factor3r19 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob18
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q19Coeffs, by rw [coordinateMod17Factor3Step19]; ring⟩
theorem coordinateMod17Factor3Step20 : coordinateMod17Factor3r19 ^ 17 - coordinateMod17Factor3r20 =
    integerCoefficientEval X coordinateMod17Factor3q20Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r19Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r20Coeffs)) (integerCoefficientMul coordinateMod17Factor3q20Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r19, coordinateMod17Factor3r20] using h
theorem coordinateMod17Factor3Frob20 : coordinateMod17Factor3 ∣ frobeniusIter 17 20 - coordinateMod17Factor3r20 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob19
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q20Coeffs, by rw [coordinateMod17Factor3Step20]; ring⟩
end
end Biunimodular.F11
