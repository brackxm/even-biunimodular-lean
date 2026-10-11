/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor4Frobenius5

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor4Step26 : coordinateMod17Factor4r25 ^ 17 - coordinateMod17Factor4r26 =
    integerCoefficientEval X coordinateMod17Factor4q26Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r25Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r26Coeffs)) (integerCoefficientMul coordinateMod17Factor4q26Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r25, coordinateMod17Factor4r26] using h
theorem coordinateMod17Factor4Frob26 : coordinateMod17Factor4 ∣ frobeniusIter 17 26 - coordinateMod17Factor4r26 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob25
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q26Coeffs, by rw [coordinateMod17Factor4Step26]; ring⟩
theorem coordinateMod17Factor4Step27 : coordinateMod17Factor4r26 ^ 17 - coordinateMod17Factor4r27 =
    integerCoefficientEval X coordinateMod17Factor4q27Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r26Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r27Coeffs)) (integerCoefficientMul coordinateMod17Factor4q27Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r26, coordinateMod17Factor4r27] using h
theorem coordinateMod17Factor4Frob27 : coordinateMod17Factor4 ∣ frobeniusIter 17 27 - coordinateMod17Factor4r27 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob26
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q27Coeffs, by rw [coordinateMod17Factor4Step27]; ring⟩
theorem coordinateMod17Factor4Step28 : coordinateMod17Factor4r27 ^ 17 - coordinateMod17Factor4r28 =
    integerCoefficientEval X coordinateMod17Factor4q28Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r27Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r28Coeffs)) (integerCoefficientMul coordinateMod17Factor4q28Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r27, coordinateMod17Factor4r28] using h
theorem coordinateMod17Factor4Frob28 : coordinateMod17Factor4 ∣ frobeniusIter 17 28 - coordinateMod17Factor4r28 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob27
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q28Coeffs, by rw [coordinateMod17Factor4Step28]; ring⟩
theorem coordinateMod17Factor4Step29 : coordinateMod17Factor4r28 ^ 17 - coordinateMod17Factor4r29 =
    integerCoefficientEval X coordinateMod17Factor4q29Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r28Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r29Coeffs)) (integerCoefficientMul coordinateMod17Factor4q29Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r28, coordinateMod17Factor4r29] using h
theorem coordinateMod17Factor4Frob29 : coordinateMod17Factor4 ∣ frobeniusIter 17 29 - coordinateMod17Factor4r29 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob28
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q29Coeffs, by rw [coordinateMod17Factor4Step29]; ring⟩
theorem coordinateMod17Factor4Step30 : coordinateMod17Factor4r29 ^ 17 - coordinateMod17Factor4r30 =
    integerCoefficientEval X coordinateMod17Factor4q30Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r29Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r30Coeffs)) (integerCoefficientMul coordinateMod17Factor4q30Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r29, coordinateMod17Factor4r30] using h
theorem coordinateMod17Factor4Frob30 : coordinateMod17Factor4 ∣ frobeniusIter 17 30 - coordinateMod17Factor4r30 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob29
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q30Coeffs, by rw [coordinateMod17Factor4Step30]; ring⟩
end
end Biunimodular.F11
