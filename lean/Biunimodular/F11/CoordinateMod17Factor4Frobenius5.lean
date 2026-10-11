/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor4Frobenius4

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor4Step21 : coordinateMod17Factor4r20 ^ 17 - coordinateMod17Factor4r21 =
    integerCoefficientEval X coordinateMod17Factor4q21Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r20Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r21Coeffs)) (integerCoefficientMul coordinateMod17Factor4q21Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r20, coordinateMod17Factor4r21] using h
theorem coordinateMod17Factor4Frob21 : coordinateMod17Factor4 ∣ frobeniusIter 17 21 - coordinateMod17Factor4r21 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob20
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q21Coeffs, by rw [coordinateMod17Factor4Step21]; ring⟩
theorem coordinateMod17Factor4Step22 : coordinateMod17Factor4r21 ^ 17 - coordinateMod17Factor4r22 =
    integerCoefficientEval X coordinateMod17Factor4q22Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r21Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r22Coeffs)) (integerCoefficientMul coordinateMod17Factor4q22Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r21, coordinateMod17Factor4r22] using h
theorem coordinateMod17Factor4Frob22 : coordinateMod17Factor4 ∣ frobeniusIter 17 22 - coordinateMod17Factor4r22 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob21
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q22Coeffs, by rw [coordinateMod17Factor4Step22]; ring⟩
theorem coordinateMod17Factor4Step23 : coordinateMod17Factor4r22 ^ 17 - coordinateMod17Factor4r23 =
    integerCoefficientEval X coordinateMod17Factor4q23Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r22Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r23Coeffs)) (integerCoefficientMul coordinateMod17Factor4q23Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r22, coordinateMod17Factor4r23] using h
theorem coordinateMod17Factor4Frob23 : coordinateMod17Factor4 ∣ frobeniusIter 17 23 - coordinateMod17Factor4r23 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob22
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q23Coeffs, by rw [coordinateMod17Factor4Step23]; ring⟩
theorem coordinateMod17Factor4Step24 : coordinateMod17Factor4r23 ^ 17 - coordinateMod17Factor4r24 =
    integerCoefficientEval X coordinateMod17Factor4q24Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r23Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r24Coeffs)) (integerCoefficientMul coordinateMod17Factor4q24Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r23, coordinateMod17Factor4r24] using h
theorem coordinateMod17Factor4Frob24 : coordinateMod17Factor4 ∣ frobeniusIter 17 24 - coordinateMod17Factor4r24 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob23
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q24Coeffs, by rw [coordinateMod17Factor4Step24]; ring⟩
theorem coordinateMod17Factor4Step25 : coordinateMod17Factor4r24 ^ 17 - coordinateMod17Factor4r25 =
    integerCoefficientEval X coordinateMod17Factor4q25Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r24Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r25Coeffs)) (integerCoefficientMul coordinateMod17Factor4q25Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r24, coordinateMod17Factor4r25] using h
theorem coordinateMod17Factor4Frob25 : coordinateMod17Factor4 ∣ frobeniusIter 17 25 - coordinateMod17Factor4r25 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob24
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q25Coeffs, by rw [coordinateMod17Factor4Step25]; ring⟩
end
end Biunimodular.F11
