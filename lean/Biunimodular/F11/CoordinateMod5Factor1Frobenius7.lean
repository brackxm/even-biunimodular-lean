/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Frobenius6

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Step31 : coordinateMod5Factor1r30 ^ 5 - coordinateMod5Factor1r31 =
    integerCoefficientEval X coordinateMod5Factor1q31Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r30Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r31Coeffs)) (integerCoefficientMul coordinateMod5Factor1q31Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r30, coordinateMod5Factor1r31] using h
theorem coordinateMod5Factor1Frob31 : coordinateMod5Factor1 ∣ frobeniusIter 5 31 - coordinateMod5Factor1r31 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob30
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q31Coeffs, by rw [coordinateMod5Factor1Step31]; ring⟩
theorem coordinateMod5Factor1Step32 : coordinateMod5Factor1r31 ^ 5 - coordinateMod5Factor1r32 =
    integerCoefficientEval X coordinateMod5Factor1q32Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r31Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r32Coeffs)) (integerCoefficientMul coordinateMod5Factor1q32Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r31, coordinateMod5Factor1r32] using h
theorem coordinateMod5Factor1Frob32 : coordinateMod5Factor1 ∣ frobeniusIter 5 32 - coordinateMod5Factor1r32 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob31
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q32Coeffs, by rw [coordinateMod5Factor1Step32]; ring⟩
theorem coordinateMod5Factor1Step33 : coordinateMod5Factor1r32 ^ 5 - coordinateMod5Factor1r33 =
    integerCoefficientEval X coordinateMod5Factor1q33Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r32Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r33Coeffs)) (integerCoefficientMul coordinateMod5Factor1q33Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r32, coordinateMod5Factor1r33] using h
theorem coordinateMod5Factor1Frob33 : coordinateMod5Factor1 ∣ frobeniusIter 5 33 - coordinateMod5Factor1r33 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob32
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q33Coeffs, by rw [coordinateMod5Factor1Step33]; ring⟩
theorem coordinateMod5Factor1Step34 : coordinateMod5Factor1r33 ^ 5 - coordinateMod5Factor1r34 =
    integerCoefficientEval X coordinateMod5Factor1q34Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r33Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r34Coeffs)) (integerCoefficientMul coordinateMod5Factor1q34Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r33, coordinateMod5Factor1r34] using h
theorem coordinateMod5Factor1Frob34 : coordinateMod5Factor1 ∣ frobeniusIter 5 34 - coordinateMod5Factor1r34 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob33
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q34Coeffs, by rw [coordinateMod5Factor1Step34]; ring⟩
theorem coordinateMod5Factor1Step35 : coordinateMod5Factor1r34 ^ 5 - coordinateMod5Factor1r35 =
    integerCoefficientEval X coordinateMod5Factor1q35Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r34Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r35Coeffs)) (integerCoefficientMul coordinateMod5Factor1q35Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r34, coordinateMod5Factor1r35] using h
theorem coordinateMod5Factor1Frob35 : coordinateMod5Factor1 ∣ frobeniusIter 5 35 - coordinateMod5Factor1r35 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob34
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q35Coeffs, by rw [coordinateMod5Factor1Step35]; ring⟩
end
end Biunimodular.F11
