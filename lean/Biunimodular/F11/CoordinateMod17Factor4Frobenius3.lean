/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor4Frobenius2

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor4Step11 : coordinateMod17Factor4r10 ^ 17 - coordinateMod17Factor4r11 =
    integerCoefficientEval X coordinateMod17Factor4q11Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r10Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r11Coeffs)) (integerCoefficientMul coordinateMod17Factor4q11Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r10, coordinateMod17Factor4r11] using h
theorem coordinateMod17Factor4Frob11 : coordinateMod17Factor4 ∣ frobeniusIter 17 11 - coordinateMod17Factor4r11 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob10
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q11Coeffs, by rw [coordinateMod17Factor4Step11]; ring⟩
theorem coordinateMod17Factor4Step12 : coordinateMod17Factor4r11 ^ 17 - coordinateMod17Factor4r12 =
    integerCoefficientEval X coordinateMod17Factor4q12Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r11Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r12Coeffs)) (integerCoefficientMul coordinateMod17Factor4q12Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r11, coordinateMod17Factor4r12] using h
theorem coordinateMod17Factor4Frob12 : coordinateMod17Factor4 ∣ frobeniusIter 17 12 - coordinateMod17Factor4r12 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob11
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q12Coeffs, by rw [coordinateMod17Factor4Step12]; ring⟩
theorem coordinateMod17Factor4Step13 : coordinateMod17Factor4r12 ^ 17 - coordinateMod17Factor4r13 =
    integerCoefficientEval X coordinateMod17Factor4q13Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r12Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r13Coeffs)) (integerCoefficientMul coordinateMod17Factor4q13Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r12, coordinateMod17Factor4r13] using h
theorem coordinateMod17Factor4Frob13 : coordinateMod17Factor4 ∣ frobeniusIter 17 13 - coordinateMod17Factor4r13 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob12
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q13Coeffs, by rw [coordinateMod17Factor4Step13]; ring⟩
theorem coordinateMod17Factor4Step14 : coordinateMod17Factor4r13 ^ 17 - coordinateMod17Factor4r14 =
    integerCoefficientEval X coordinateMod17Factor4q14Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r13Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r14Coeffs)) (integerCoefficientMul coordinateMod17Factor4q14Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r13, coordinateMod17Factor4r14] using h
theorem coordinateMod17Factor4Frob14 : coordinateMod17Factor4 ∣ frobeniusIter 17 14 - coordinateMod17Factor4r14 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob13
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q14Coeffs, by rw [coordinateMod17Factor4Step14]; ring⟩
theorem coordinateMod17Factor4Step15 : coordinateMod17Factor4r14 ^ 17 - coordinateMod17Factor4r15 =
    integerCoefficientEval X coordinateMod17Factor4q15Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r14Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r15Coeffs)) (integerCoefficientMul coordinateMod17Factor4q15Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r14, coordinateMod17Factor4r15] using h
theorem coordinateMod17Factor4Frob15 : coordinateMod17Factor4 ∣ frobeniusIter 17 15 - coordinateMod17Factor4r15 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob14
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q15Coeffs, by rw [coordinateMod17Factor4Step15]; ring⟩
end
end Biunimodular.F11
