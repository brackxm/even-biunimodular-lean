/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Frobenius5

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Step26 : coordinateMod5Factor1r25 ^ 5 - coordinateMod5Factor1r26 =
    integerCoefficientEval X coordinateMod5Factor1q26Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r25Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r26Coeffs)) (integerCoefficientMul coordinateMod5Factor1q26Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r25, coordinateMod5Factor1r26] using h
theorem coordinateMod5Factor1Frob26 : coordinateMod5Factor1 ∣ frobeniusIter 5 26 - coordinateMod5Factor1r26 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob25
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q26Coeffs, by rw [coordinateMod5Factor1Step26]; ring⟩
theorem coordinateMod5Factor1Step27 : coordinateMod5Factor1r26 ^ 5 - coordinateMod5Factor1r27 =
    integerCoefficientEval X coordinateMod5Factor1q27Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r26Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r27Coeffs)) (integerCoefficientMul coordinateMod5Factor1q27Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r26, coordinateMod5Factor1r27] using h
theorem coordinateMod5Factor1Frob27 : coordinateMod5Factor1 ∣ frobeniusIter 5 27 - coordinateMod5Factor1r27 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob26
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q27Coeffs, by rw [coordinateMod5Factor1Step27]; ring⟩
theorem coordinateMod5Factor1Step28 : coordinateMod5Factor1r27 ^ 5 - coordinateMod5Factor1r28 =
    integerCoefficientEval X coordinateMod5Factor1q28Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r27Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r28Coeffs)) (integerCoefficientMul coordinateMod5Factor1q28Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r27, coordinateMod5Factor1r28] using h
theorem coordinateMod5Factor1Frob28 : coordinateMod5Factor1 ∣ frobeniusIter 5 28 - coordinateMod5Factor1r28 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob27
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q28Coeffs, by rw [coordinateMod5Factor1Step28]; ring⟩
theorem coordinateMod5Factor1Step29 : coordinateMod5Factor1r28 ^ 5 - coordinateMod5Factor1r29 =
    integerCoefficientEval X coordinateMod5Factor1q29Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r28Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r29Coeffs)) (integerCoefficientMul coordinateMod5Factor1q29Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r28, coordinateMod5Factor1r29] using h
theorem coordinateMod5Factor1Frob29 : coordinateMod5Factor1 ∣ frobeniusIter 5 29 - coordinateMod5Factor1r29 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob28
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q29Coeffs, by rw [coordinateMod5Factor1Step29]; ring⟩
theorem coordinateMod5Factor1Step30 : coordinateMod5Factor1r29 ^ 5 - coordinateMod5Factor1r30 =
    integerCoefficientEval X coordinateMod5Factor1q30Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r29Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r30Coeffs)) (integerCoefficientMul coordinateMod5Factor1q30Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r29, coordinateMod5Factor1r30] using h
theorem coordinateMod5Factor1Frob30 : coordinateMod5Factor1 ∣ frobeniusIter 5 30 - coordinateMod5Factor1r30 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob29
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q30Coeffs, by rw [coordinateMod5Factor1Step30]; ring⟩
end
end Biunimodular.F11
