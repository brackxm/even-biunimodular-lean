/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Frobenius4

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Step21 : coordinateMod5Factor1r20 ^ 5 - coordinateMod5Factor1r21 =
    integerCoefficientEval X coordinateMod5Factor1q21Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r20Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r21Coeffs)) (integerCoefficientMul coordinateMod5Factor1q21Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r20, coordinateMod5Factor1r21] using h
theorem coordinateMod5Factor1Frob21 : coordinateMod5Factor1 ∣ frobeniusIter 5 21 - coordinateMod5Factor1r21 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob20
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q21Coeffs, by rw [coordinateMod5Factor1Step21]; ring⟩
theorem coordinateMod5Factor1Step22 : coordinateMod5Factor1r21 ^ 5 - coordinateMod5Factor1r22 =
    integerCoefficientEval X coordinateMod5Factor1q22Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r21Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r22Coeffs)) (integerCoefficientMul coordinateMod5Factor1q22Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r21, coordinateMod5Factor1r22] using h
theorem coordinateMod5Factor1Frob22 : coordinateMod5Factor1 ∣ frobeniusIter 5 22 - coordinateMod5Factor1r22 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob21
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q22Coeffs, by rw [coordinateMod5Factor1Step22]; ring⟩
theorem coordinateMod5Factor1Step23 : coordinateMod5Factor1r22 ^ 5 - coordinateMod5Factor1r23 =
    integerCoefficientEval X coordinateMod5Factor1q23Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r22Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r23Coeffs)) (integerCoefficientMul coordinateMod5Factor1q23Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r22, coordinateMod5Factor1r23] using h
theorem coordinateMod5Factor1Frob23 : coordinateMod5Factor1 ∣ frobeniusIter 5 23 - coordinateMod5Factor1r23 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob22
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q23Coeffs, by rw [coordinateMod5Factor1Step23]; ring⟩
theorem coordinateMod5Factor1Step24 : coordinateMod5Factor1r23 ^ 5 - coordinateMod5Factor1r24 =
    integerCoefficientEval X coordinateMod5Factor1q24Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r23Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r24Coeffs)) (integerCoefficientMul coordinateMod5Factor1q24Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r23, coordinateMod5Factor1r24] using h
theorem coordinateMod5Factor1Frob24 : coordinateMod5Factor1 ∣ frobeniusIter 5 24 - coordinateMod5Factor1r24 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob23
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q24Coeffs, by rw [coordinateMod5Factor1Step24]; ring⟩
theorem coordinateMod5Factor1Step25 : coordinateMod5Factor1r24 ^ 5 - coordinateMod5Factor1r25 =
    integerCoefficientEval X coordinateMod5Factor1q25Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r24Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r25Coeffs)) (integerCoefficientMul coordinateMod5Factor1q25Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r24, coordinateMod5Factor1r25] using h
theorem coordinateMod5Factor1Frob25 : coordinateMod5Factor1 ∣ frobeniusIter 5 25 - coordinateMod5Factor1r25 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob24
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q25Coeffs, by rw [coordinateMod5Factor1Step25]; ring⟩
end
end Biunimodular.F11
