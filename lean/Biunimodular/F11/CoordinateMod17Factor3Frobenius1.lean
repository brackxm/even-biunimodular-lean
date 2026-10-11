/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor3Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor3Frob0 : coordinateMod17Factor3 ∣ frobeniusIter 17 0 - coordinateMod17Factor3r0 := by
  simp [coordinateMod17Factor3r0, coordinateMod17Factor3r0Coeffs, frobeniusIter, integerCoefficientEval]
theorem coordinateMod17Factor3Step1 : coordinateMod17Factor3r0 ^ 17 - coordinateMod17Factor3r1 =
    integerCoefficientEval X coordinateMod17Factor3q1Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r0Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r1Coeffs)) (integerCoefficientMul coordinateMod17Factor3q1Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r0, coordinateMod17Factor3r1] using h
theorem coordinateMod17Factor3Frob1 : coordinateMod17Factor3 ∣ frobeniusIter 17 1 - coordinateMod17Factor3r1 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob0
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q1Coeffs, by rw [coordinateMod17Factor3Step1]; ring⟩
theorem coordinateMod17Factor3Step2 : coordinateMod17Factor3r1 ^ 17 - coordinateMod17Factor3r2 =
    integerCoefficientEval X coordinateMod17Factor3q2Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r1Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r2Coeffs)) (integerCoefficientMul coordinateMod17Factor3q2Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r1, coordinateMod17Factor3r2] using h
theorem coordinateMod17Factor3Frob2 : coordinateMod17Factor3 ∣ frobeniusIter 17 2 - coordinateMod17Factor3r2 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob1
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q2Coeffs, by rw [coordinateMod17Factor3Step2]; ring⟩
theorem coordinateMod17Factor3Step3 : coordinateMod17Factor3r2 ^ 17 - coordinateMod17Factor3r3 =
    integerCoefficientEval X coordinateMod17Factor3q3Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r2Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r3Coeffs)) (integerCoefficientMul coordinateMod17Factor3q3Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r2, coordinateMod17Factor3r3] using h
theorem coordinateMod17Factor3Frob3 : coordinateMod17Factor3 ∣ frobeniusIter 17 3 - coordinateMod17Factor3r3 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob2
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q3Coeffs, by rw [coordinateMod17Factor3Step3]; ring⟩
theorem coordinateMod17Factor3Step4 : coordinateMod17Factor3r3 ^ 17 - coordinateMod17Factor3r4 =
    integerCoefficientEval X coordinateMod17Factor3q4Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r3Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r4Coeffs)) (integerCoefficientMul coordinateMod17Factor3q4Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r3, coordinateMod17Factor3r4] using h
theorem coordinateMod17Factor3Frob4 : coordinateMod17Factor3 ∣ frobeniusIter 17 4 - coordinateMod17Factor3r4 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob3
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q4Coeffs, by rw [coordinateMod17Factor3Step4]; ring⟩
theorem coordinateMod17Factor3Step5 : coordinateMod17Factor3r4 ^ 17 - coordinateMod17Factor3r5 =
    integerCoefficientEval X coordinateMod17Factor3q5Coeffs * coordinateMod17Factor3 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor3r4Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor3r5Coeffs)) (integerCoefficientMul coordinateMod17Factor3q5Coeffs coordinateMod17Factor3Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r4, coordinateMod17Factor3r5] using h
theorem coordinateMod17Factor3Frob5 : coordinateMod17Factor3 ∣ frobeniusIter 17 5 - coordinateMod17Factor3r5 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor3Frob4
  exact ⟨integerCoefficientEval X coordinateMod17Factor3q5Coeffs, by rw [coordinateMod17Factor3Step5]; ring⟩
end
end Biunimodular.F11
