/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor3Frobenius2

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor3Step11 : coordinateMod17Factor3r10 ^ 17 - coordinateMod17Factor3r11 =
    integerCoefficientEval X coordinateMod17Factor3q11Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r10Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r11Coeffs)) (integerCoefficientMul coordinateMod17Factor3q11Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r10, coordinateMod17Factor3r11] using h
theorem coordinateMod17Factor3Frob11 : coordinateMod17Factor3 ∣ frobeniusIter 17 11 - coordinateMod17Factor3r11 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob10
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q11Coeffs, by rw [coordinateMod17Factor3Step11]; ring⟩
theorem coordinateMod17Factor3Step12 : coordinateMod17Factor3r11 ^ 17 - coordinateMod17Factor3r12 =
    integerCoefficientEval X coordinateMod17Factor3q12Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r11Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r12Coeffs)) (integerCoefficientMul coordinateMod17Factor3q12Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r11, coordinateMod17Factor3r12] using h
theorem coordinateMod17Factor3Frob12 : coordinateMod17Factor3 ∣ frobeniusIter 17 12 - coordinateMod17Factor3r12 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob11
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q12Coeffs, by rw [coordinateMod17Factor3Step12]; ring⟩
theorem coordinateMod17Factor3Step13 : coordinateMod17Factor3r12 ^ 17 - coordinateMod17Factor3r13 =
    integerCoefficientEval X coordinateMod17Factor3q13Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r12Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r13Coeffs)) (integerCoefficientMul coordinateMod17Factor3q13Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r12, coordinateMod17Factor3r13] using h
theorem coordinateMod17Factor3Frob13 : coordinateMod17Factor3 ∣ frobeniusIter 17 13 - coordinateMod17Factor3r13 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob12
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q13Coeffs, by rw [coordinateMod17Factor3Step13]; ring⟩
theorem coordinateMod17Factor3Step14 : coordinateMod17Factor3r13 ^ 17 - coordinateMod17Factor3r14 =
    integerCoefficientEval X coordinateMod17Factor3q14Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r13Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r14Coeffs)) (integerCoefficientMul coordinateMod17Factor3q14Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r13, coordinateMod17Factor3r14] using h
theorem coordinateMod17Factor3Frob14 : coordinateMod17Factor3 ∣ frobeniusIter 17 14 - coordinateMod17Factor3r14 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob13
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q14Coeffs, by rw [coordinateMod17Factor3Step14]; ring⟩
theorem coordinateMod17Factor3Step15 : coordinateMod17Factor3r14 ^ 17 - coordinateMod17Factor3r15 =
    integerCoefficientEval X coordinateMod17Factor3q15Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r14Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r15Coeffs)) (integerCoefficientMul coordinateMod17Factor3q15Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r14, coordinateMod17Factor3r15] using h
theorem coordinateMod17Factor3Frob15 : coordinateMod17Factor3 ∣ frobeniusIter 17 15 - coordinateMod17Factor3r15 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob14
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q15Coeffs, by rw [coordinateMod17Factor3Step15]; ring⟩
end
end Biunimodular.F11
