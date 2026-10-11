/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor4Frobenius3

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor4Step16 : coordinateMod17Factor4r15 ^ 17 - coordinateMod17Factor4r16 =
    integerCoefficientEval X coordinateMod17Factor4q16Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r15Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r16Coeffs)) (integerCoefficientMul coordinateMod17Factor4q16Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r15, coordinateMod17Factor4r16] using h
theorem coordinateMod17Factor4Frob16 : coordinateMod17Factor4 ∣ frobeniusIter 17 16 - coordinateMod17Factor4r16 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob15
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q16Coeffs, by rw [coordinateMod17Factor4Step16]; ring⟩
theorem coordinateMod17Factor4Step17 : coordinateMod17Factor4r16 ^ 17 - coordinateMod17Factor4r17 =
    integerCoefficientEval X coordinateMod17Factor4q17Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r16Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r17Coeffs)) (integerCoefficientMul coordinateMod17Factor4q17Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r16, coordinateMod17Factor4r17] using h
theorem coordinateMod17Factor4Frob17 : coordinateMod17Factor4 ∣ frobeniusIter 17 17 - coordinateMod17Factor4r17 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob16
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q17Coeffs, by rw [coordinateMod17Factor4Step17]; ring⟩
theorem coordinateMod17Factor4Step18 : coordinateMod17Factor4r17 ^ 17 - coordinateMod17Factor4r18 =
    integerCoefficientEval X coordinateMod17Factor4q18Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r17Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r18Coeffs)) (integerCoefficientMul coordinateMod17Factor4q18Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r17, coordinateMod17Factor4r18] using h
theorem coordinateMod17Factor4Frob18 : coordinateMod17Factor4 ∣ frobeniusIter 17 18 - coordinateMod17Factor4r18 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob17
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q18Coeffs, by rw [coordinateMod17Factor4Step18]; ring⟩
theorem coordinateMod17Factor4Step19 : coordinateMod17Factor4r18 ^ 17 - coordinateMod17Factor4r19 =
    integerCoefficientEval X coordinateMod17Factor4q19Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r18Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r19Coeffs)) (integerCoefficientMul coordinateMod17Factor4q19Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r18, coordinateMod17Factor4r19] using h
theorem coordinateMod17Factor4Frob19 : coordinateMod17Factor4 ∣ frobeniusIter 17 19 - coordinateMod17Factor4r19 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob18
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q19Coeffs, by rw [coordinateMod17Factor4Step19]; ring⟩
theorem coordinateMod17Factor4Step20 : coordinateMod17Factor4r19 ^ 17 - coordinateMod17Factor4r20 =
    integerCoefficientEval X coordinateMod17Factor4q20Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r19Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r20Coeffs)) (integerCoefficientMul coordinateMod17Factor4q20Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r19, coordinateMod17Factor4r20] using h
theorem coordinateMod17Factor4Frob20 : coordinateMod17Factor4 ∣ frobeniusIter 17 20 - coordinateMod17Factor4r20 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob19
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q20Coeffs, by rw [coordinateMod17Factor4Step20]; ring⟩
end
end Biunimodular.F11
