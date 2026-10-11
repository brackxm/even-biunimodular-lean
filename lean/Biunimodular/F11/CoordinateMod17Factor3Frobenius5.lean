/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor3Frobenius4

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor3Step21 : coordinateMod17Factor3r20 ^ 17 - coordinateMod17Factor3r21 =
    integerCoefficientEval X coordinateMod17Factor3q21Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r20Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r21Coeffs)) (integerCoefficientMul coordinateMod17Factor3q21Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r20, coordinateMod17Factor3r21] using h
theorem coordinateMod17Factor3Frob21 : coordinateMod17Factor3 ∣ frobeniusIter 17 21 - coordinateMod17Factor3r21 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob20
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q21Coeffs, by rw [coordinateMod17Factor3Step21]; ring⟩
theorem coordinateMod17Factor3Step22 : coordinateMod17Factor3r21 ^ 17 - coordinateMod17Factor3r22 =
    integerCoefficientEval X coordinateMod17Factor3q22Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r21Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r22Coeffs)) (integerCoefficientMul coordinateMod17Factor3q22Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r21, coordinateMod17Factor3r22] using h
theorem coordinateMod17Factor3Frob22 : coordinateMod17Factor3 ∣ frobeniusIter 17 22 - coordinateMod17Factor3r22 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob21
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q22Coeffs, by rw [coordinateMod17Factor3Step22]; ring⟩
theorem coordinateMod17Factor3Step23 : coordinateMod17Factor3r22 ^ 17 - coordinateMod17Factor3r23 =
    integerCoefficientEval X coordinateMod17Factor3q23Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r22Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r23Coeffs)) (integerCoefficientMul coordinateMod17Factor3q23Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r22, coordinateMod17Factor3r23] using h
theorem coordinateMod17Factor3Frob23 : coordinateMod17Factor3 ∣ frobeniusIter 17 23 - coordinateMod17Factor3r23 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob22
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q23Coeffs, by rw [coordinateMod17Factor3Step23]; ring⟩
theorem coordinateMod17Factor3Step24 : coordinateMod17Factor3r23 ^ 17 - coordinateMod17Factor3r24 =
    integerCoefficientEval X coordinateMod17Factor3q24Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r23Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r24Coeffs)) (integerCoefficientMul coordinateMod17Factor3q24Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r23, coordinateMod17Factor3r24] using h
theorem coordinateMod17Factor3Frob24 : coordinateMod17Factor3 ∣ frobeniusIter 17 24 - coordinateMod17Factor3r24 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob23
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q24Coeffs, by rw [coordinateMod17Factor3Step24]; ring⟩
theorem coordinateMod17Factor3Step25 : coordinateMod17Factor3r24 ^ 17 - coordinateMod17Factor3r25 =
    integerCoefficientEval X coordinateMod17Factor3q25Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r24Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r25Coeffs)) (integerCoefficientMul coordinateMod17Factor3q25Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r24, coordinateMod17Factor3r25] using h
theorem coordinateMod17Factor3Frob25 : coordinateMod17Factor3 ∣ frobeniusIter 17 25 - coordinateMod17Factor3r25 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob24
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q25Coeffs, by rw [coordinateMod17Factor3Step25]; ring⟩
end
end Biunimodular.F11
