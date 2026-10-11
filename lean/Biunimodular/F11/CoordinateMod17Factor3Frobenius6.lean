/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor3Frobenius5

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor3Step26 : coordinateMod17Factor3r25 ^ 17 - coordinateMod17Factor3r26 =
    integerCoefficientEval X coordinateMod17Factor3q26Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r25Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r26Coeffs)) (integerCoefficientMul coordinateMod17Factor3q26Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r25, coordinateMod17Factor3r26] using h
theorem coordinateMod17Factor3Frob26 : coordinateMod17Factor3 ∣ frobeniusIter 17 26 - coordinateMod17Factor3r26 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob25
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q26Coeffs, by rw [coordinateMod17Factor3Step26]; ring⟩
theorem coordinateMod17Factor3Step27 : coordinateMod17Factor3r26 ^ 17 - coordinateMod17Factor3r27 =
    integerCoefficientEval X coordinateMod17Factor3q27Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r26Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r27Coeffs)) (integerCoefficientMul coordinateMod17Factor3q27Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r26, coordinateMod17Factor3r27] using h
theorem coordinateMod17Factor3Frob27 : coordinateMod17Factor3 ∣ frobeniusIter 17 27 - coordinateMod17Factor3r27 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob26
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q27Coeffs, by rw [coordinateMod17Factor3Step27]; ring⟩
theorem coordinateMod17Factor3Step28 : coordinateMod17Factor3r27 ^ 17 - coordinateMod17Factor3r28 =
    integerCoefficientEval X coordinateMod17Factor3q28Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r27Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r28Coeffs)) (integerCoefficientMul coordinateMod17Factor3q28Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r27, coordinateMod17Factor3r28] using h
theorem coordinateMod17Factor3Frob28 : coordinateMod17Factor3 ∣ frobeniusIter 17 28 - coordinateMod17Factor3r28 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob27
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q28Coeffs, by rw [coordinateMod17Factor3Step28]; ring⟩
theorem coordinateMod17Factor3Step29 : coordinateMod17Factor3r28 ^ 17 - coordinateMod17Factor3r29 =
    integerCoefficientEval X coordinateMod17Factor3q29Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r28Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r29Coeffs)) (integerCoefficientMul coordinateMod17Factor3q29Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r28, coordinateMod17Factor3r29] using h
theorem coordinateMod17Factor3Frob29 : coordinateMod17Factor3 ∣ frobeniusIter 17 29 - coordinateMod17Factor3r29 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob28
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q29Coeffs, by rw [coordinateMod17Factor3Step29]; ring⟩
theorem coordinateMod17Factor3Step30 : coordinateMod17Factor3r29 ^ 17 - coordinateMod17Factor3r30 =
    integerCoefficientEval X coordinateMod17Factor3q30Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r29Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r30Coeffs)) (integerCoefficientMul coordinateMod17Factor3q30Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r29, coordinateMod17Factor3r30] using h
theorem coordinateMod17Factor3Frob30 : coordinateMod17Factor3 ∣ frobeniusIter 17 30 - coordinateMod17Factor3r30 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob29
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q30Coeffs, by rw [coordinateMod17Factor3Step30]; ring⟩
end
end Biunimodular.F11
