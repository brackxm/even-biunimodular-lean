/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Frob0 : coordinateMod5Factor1 ∣ frobeniusIter 5 0 - coordinateMod5Factor1r0 := by
  simp [coordinateMod5Factor1r0, coordinateMod5Factor1r0Coeffs, frobeniusIter, integerCoefficientEval]
theorem coordinateMod5Factor1Step1 : coordinateMod5Factor1r0 ^ 5 - coordinateMod5Factor1r1 =
    integerCoefficientEval X coordinateMod5Factor1q1Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r0Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r1Coeffs)) (integerCoefficientMul coordinateMod5Factor1q1Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r0, coordinateMod5Factor1r1] using h
theorem coordinateMod5Factor1Frob1 : coordinateMod5Factor1 ∣ frobeniusIter 5 1 - coordinateMod5Factor1r1 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob0
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q1Coeffs, by rw [coordinateMod5Factor1Step1]; ring⟩
theorem coordinateMod5Factor1Step2 : coordinateMod5Factor1r1 ^ 5 - coordinateMod5Factor1r2 =
    integerCoefficientEval X coordinateMod5Factor1q2Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r1Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r2Coeffs)) (integerCoefficientMul coordinateMod5Factor1q2Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r1, coordinateMod5Factor1r2] using h
theorem coordinateMod5Factor1Frob2 : coordinateMod5Factor1 ∣ frobeniusIter 5 2 - coordinateMod5Factor1r2 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob1
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q2Coeffs, by rw [coordinateMod5Factor1Step2]; ring⟩
theorem coordinateMod5Factor1Step3 : coordinateMod5Factor1r2 ^ 5 - coordinateMod5Factor1r3 =
    integerCoefficientEval X coordinateMod5Factor1q3Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r2Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r3Coeffs)) (integerCoefficientMul coordinateMod5Factor1q3Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r2, coordinateMod5Factor1r3] using h
theorem coordinateMod5Factor1Frob3 : coordinateMod5Factor1 ∣ frobeniusIter 5 3 - coordinateMod5Factor1r3 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob2
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q3Coeffs, by rw [coordinateMod5Factor1Step3]; ring⟩
theorem coordinateMod5Factor1Step4 : coordinateMod5Factor1r3 ^ 5 - coordinateMod5Factor1r4 =
    integerCoefficientEval X coordinateMod5Factor1q4Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r3Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r4Coeffs)) (integerCoefficientMul coordinateMod5Factor1q4Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r3, coordinateMod5Factor1r4] using h
theorem coordinateMod5Factor1Frob4 : coordinateMod5Factor1 ∣ frobeniusIter 5 4 - coordinateMod5Factor1r4 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob3
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q4Coeffs, by rw [coordinateMod5Factor1Step4]; ring⟩
theorem coordinateMod5Factor1Step5 : coordinateMod5Factor1r4 ^ 5 - coordinateMod5Factor1r5 =
    integerCoefficientEval X coordinateMod5Factor1q5Coeffs * coordinateMod5Factor1 := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientPow coordinateMod5Factor1r4Coeffs 5) (integerCoefficientScale (-1) coordinateMod5Factor1r5Coeffs)) (integerCoefficientMul coordinateMod5Factor1q5Coeffs coordinateMod5Factor1Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r4, coordinateMod5Factor1r5] using h
theorem coordinateMod5Factor1Frob5 : coordinateMod5Factor1 ∣ frobeniusIter 5 5 - coordinateMod5Factor1r5 := by
  apply frobeniusIter_dvd_next coordinateMod5Factor1Frob4
  exact ⟨integerCoefficientEval X coordinateMod5Factor1q5Coeffs, by rw [coordinateMod5Factor1Step5]; ring⟩
end
end Biunimodular.F11
