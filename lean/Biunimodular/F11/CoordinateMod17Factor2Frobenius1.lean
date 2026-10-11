/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor2Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor2Frob0 : coordinateMod17Factor2 ∣ frobeniusIter 17 0 - coordinateMod17Factor2r0 := by
  simp [coordinateMod17Factor2r0, coordinateMod17Factor2r0Coeffs, frobeniusIter, integerCoefficientEval]
theorem coordinateMod17Factor2Step1 : coordinateMod17Factor2r0 ^ 17 - coordinateMod17Factor2r1 =
    integerCoefficientEval X coordinateMod17Factor2q1Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r0Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r1Coeffs)) (integerCoefficientMul coordinateMod17Factor2q1Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r0, coordinateMod17Factor2r1] using h
theorem coordinateMod17Factor2Frob1 : coordinateMod17Factor2 ∣ frobeniusIter 17 1 - coordinateMod17Factor2r1 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob0
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q1Coeffs, by rw [coordinateMod17Factor2Step1]; ring⟩
theorem coordinateMod17Factor2Step2 : coordinateMod17Factor2r1 ^ 17 - coordinateMod17Factor2r2 =
    integerCoefficientEval X coordinateMod17Factor2q2Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r1Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r2Coeffs)) (integerCoefficientMul coordinateMod17Factor2q2Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r1, coordinateMod17Factor2r2] using h
theorem coordinateMod17Factor2Frob2 : coordinateMod17Factor2 ∣ frobeniusIter 17 2 - coordinateMod17Factor2r2 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob1
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q2Coeffs, by rw [coordinateMod17Factor2Step2]; ring⟩
theorem coordinateMod17Factor2Step3 : coordinateMod17Factor2r2 ^ 17 - coordinateMod17Factor2r3 =
    integerCoefficientEval X coordinateMod17Factor2q3Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r2Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r3Coeffs)) (integerCoefficientMul coordinateMod17Factor2q3Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r2, coordinateMod17Factor2r3] using h
theorem coordinateMod17Factor2Frob3 : coordinateMod17Factor2 ∣ frobeniusIter 17 3 - coordinateMod17Factor2r3 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob2
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q3Coeffs, by rw [coordinateMod17Factor2Step3]; ring⟩
theorem coordinateMod17Factor2Step4 : coordinateMod17Factor2r3 ^ 17 - coordinateMod17Factor2r4 =
    integerCoefficientEval X coordinateMod17Factor2q4Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r3Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r4Coeffs)) (integerCoefficientMul coordinateMod17Factor2q4Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r3, coordinateMod17Factor2r4] using h
theorem coordinateMod17Factor2Frob4 : coordinateMod17Factor2 ∣ frobeniusIter 17 4 - coordinateMod17Factor2r4 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob3
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q4Coeffs, by rw [coordinateMod17Factor2Step4]; ring⟩
theorem coordinateMod17Factor2Step5 : coordinateMod17Factor2r4 ^ 17 - coordinateMod17Factor2r5 =
    integerCoefficientEval X coordinateMod17Factor2q5Coeffs * coordinateMod17Factor2 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor2r4Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor2r5Coeffs)) (integerCoefficientMul coordinateMod17Factor2q5Coeffs coordinateMod17Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r4, coordinateMod17Factor2r5] using h
theorem coordinateMod17Factor2Frob5 : coordinateMod17Factor2 ∣ frobeniusIter 17 5 - coordinateMod17Factor2r5 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor2Frob4
  exact ⟨integerCoefficientEval X coordinateMod17Factor2q5Coeffs, by rw [coordinateMod17Factor2Step5]; ring⟩
end
end Biunimodular.F11
