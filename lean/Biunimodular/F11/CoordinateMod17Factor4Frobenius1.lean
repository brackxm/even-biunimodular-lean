/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor4Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor4Frob0 : coordinateMod17Factor4 ∣ frobeniusIter 17 0 - coordinateMod17Factor4r0 := by
  simp [coordinateMod17Factor4r0, coordinateMod17Factor4r0Coeffs, frobeniusIter, integerCoefficientEval]
theorem coordinateMod17Factor4Step1 : coordinateMod17Factor4r0 ^ 17 - coordinateMod17Factor4r1 =
    integerCoefficientEval X coordinateMod17Factor4q1Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r0Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r1Coeffs)) (integerCoefficientMul coordinateMod17Factor4q1Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r0, coordinateMod17Factor4r1] using h
theorem coordinateMod17Factor4Frob1 : coordinateMod17Factor4 ∣ frobeniusIter 17 1 - coordinateMod17Factor4r1 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob0
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q1Coeffs, by rw [coordinateMod17Factor4Step1]; ring⟩
theorem coordinateMod17Factor4Step2 : coordinateMod17Factor4r1 ^ 17 - coordinateMod17Factor4r2 =
    integerCoefficientEval X coordinateMod17Factor4q2Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r1Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r2Coeffs)) (integerCoefficientMul coordinateMod17Factor4q2Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r1, coordinateMod17Factor4r2] using h
theorem coordinateMod17Factor4Frob2 : coordinateMod17Factor4 ∣ frobeniusIter 17 2 - coordinateMod17Factor4r2 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob1
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q2Coeffs, by rw [coordinateMod17Factor4Step2]; ring⟩
theorem coordinateMod17Factor4Step3 : coordinateMod17Factor4r2 ^ 17 - coordinateMod17Factor4r3 =
    integerCoefficientEval X coordinateMod17Factor4q3Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r2Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r3Coeffs)) (integerCoefficientMul coordinateMod17Factor4q3Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r2, coordinateMod17Factor4r3] using h
theorem coordinateMod17Factor4Frob3 : coordinateMod17Factor4 ∣ frobeniusIter 17 3 - coordinateMod17Factor4r3 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob2
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q3Coeffs, by rw [coordinateMod17Factor4Step3]; ring⟩
theorem coordinateMod17Factor4Step4 : coordinateMod17Factor4r3 ^ 17 - coordinateMod17Factor4r4 =
    integerCoefficientEval X coordinateMod17Factor4q4Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r3Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r4Coeffs)) (integerCoefficientMul coordinateMod17Factor4q4Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r3, coordinateMod17Factor4r4] using h
theorem coordinateMod17Factor4Frob4 : coordinateMod17Factor4 ∣ frobeniusIter 17 4 - coordinateMod17Factor4r4 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob3
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q4Coeffs, by rw [coordinateMod17Factor4Step4]; ring⟩
theorem coordinateMod17Factor4Step5 : coordinateMod17Factor4r4 ^ 17 - coordinateMod17Factor4r5 =
    integerCoefficientEval X coordinateMod17Factor4q5Coeffs * coordinateMod17Factor4 := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientPow coordinateMod17Factor4r4Coeffs 17) (integerCoefficientScale (-1) coordinateMod17Factor4r5Coeffs)) (integerCoefficientMul coordinateMod17Factor4q5Coeffs coordinateMod17Factor4Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  simpa only [integerCoefficientEval_add, integerCoefficientEval_scale, integerCoefficientEval_pow, integerCoefficientEval_mul, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r4, coordinateMod17Factor4r5] using h
theorem coordinateMod17Factor4Frob5 : coordinateMod17Factor4 ∣ frobeniusIter 17 5 - coordinateMod17Factor4r5 := by
  apply frobeniusIter_dvd_next coordinateMod17Factor4Frob4
  exact ⟨integerCoefficientEval X coordinateMod17Factor4q5Coeffs, by rw [coordinateMod17Factor4Step5]; ring⟩
end
end Biunimodular.F11
