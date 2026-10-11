/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor2Frobenius5

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor2Binary26Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^1-h252Fiber7Mod163Factor2r25 := by simp
theorem h252Fiber7Mod163Factor2Binary26Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r25Coeffs h252Fiber7Mod163Factor2r25Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r25)*(h252Fiber7Mod163Factor2r25)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r25)*(h252Fiber7Mod163Factor2r25)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (h252Fiber7Mod163Factor2r25) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs) 1 h252Fiber7Mod163Factor2Binary26Step0 hs
theorem h252Fiber7Mod163Factor2Binary26Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r1Coeffs h252Fiber7Mod163Factor2b26r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r2Coeffs) 2 h252Fiber7Mod163Factor2Binary26Step1 hs
theorem h252Fiber7Mod163Factor2Binary26Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r2Coeffs h252Fiber7Mod163Factor2r25Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r2Coeffs)*(h252Fiber7Mod163Factor2r25)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r2Coeffs)*(h252Fiber7Mod163Factor2r25)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs) 4 h252Fiber7Mod163Factor2Binary26Step2 hs
theorem h252Fiber7Mod163Factor2Binary26Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r3Coeffs h252Fiber7Mod163Factor2b26r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs) 5 h252Fiber7Mod163Factor2Binary26Step3 hs
theorem h252Fiber7Mod163Factor2Binary26Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r4Coeffs h252Fiber7Mod163Factor2b26r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs) 10 h252Fiber7Mod163Factor2Binary26Step4 hs
theorem h252Fiber7Mod163Factor2Binary26Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r5Coeffs h252Fiber7Mod163Factor2b26r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs) 20 h252Fiber7Mod163Factor2Binary26Step5 hs
theorem h252Fiber7Mod163Factor2Binary26Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r6Coeffs h252Fiber7Mod163Factor2b26r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r7Coeffs) 40 h252Fiber7Mod163Factor2Binary26Step6 hs
theorem h252Fiber7Mod163Factor2Binary26Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r7Coeffs h252Fiber7Mod163Factor2r25Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r7Coeffs)*(h252Fiber7Mod163Factor2r25)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r7Coeffs)*(h252Fiber7Mod163Factor2r25)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs) 80 h252Fiber7Mod163Factor2Binary26Step7 hs
theorem h252Fiber7Mod163Factor2Binary26Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r8Coeffs h252Fiber7Mod163Factor2b26r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r9Coeffs) 81 h252Fiber7Mod163Factor2Binary26Step8 hs
theorem h252Fiber7Mod163Factor2Binary26Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b26r9Coeffs h252Fiber7Mod163Factor2r25Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b26r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b26q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b26r9Coeffs)*(h252Fiber7Mod163Factor2r25)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b26q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r25] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b26r9Coeffs)*(h252Fiber7Mod163Factor2r25)-(integerCoefficientEval X h252Fiber7Mod163Factor2b26r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b26q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r25 (integerCoefficientEval X h252Fiber7Mod163Factor2b26r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b26r10Coeffs) 162 h252Fiber7Mod163Factor2Binary26Step9 hs
theorem h252Fiber7Mod163Factor2Step26 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r25^163-h252Fiber7Mod163Factor2r26 := by
  have he : h252Fiber7Mod163Factor2b26r10Coeffs = h252Fiber7Mod163Factor2r26Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r26] using h252Fiber7Mod163Factor2Binary26Step10
theorem h252Fiber7Mod163Factor2Frob26 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 26-h252Fiber7Mod163Factor2r26 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob25 h252Fiber7Mod163Factor2Step26
theorem h252Fiber7Mod163Factor2Binary27Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^1-h252Fiber7Mod163Factor2r26 := by simp
theorem h252Fiber7Mod163Factor2Binary27Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r26Coeffs h252Fiber7Mod163Factor2r26Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r26)*(h252Fiber7Mod163Factor2r26)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r26)*(h252Fiber7Mod163Factor2r26)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (h252Fiber7Mod163Factor2r26) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs) 1 h252Fiber7Mod163Factor2Binary27Step0 hs
theorem h252Fiber7Mod163Factor2Binary27Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r1Coeffs h252Fiber7Mod163Factor2b27r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r2Coeffs) 2 h252Fiber7Mod163Factor2Binary27Step1 hs
theorem h252Fiber7Mod163Factor2Binary27Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r2Coeffs h252Fiber7Mod163Factor2r26Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r2Coeffs)*(h252Fiber7Mod163Factor2r26)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r2Coeffs)*(h252Fiber7Mod163Factor2r26)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs) 4 h252Fiber7Mod163Factor2Binary27Step2 hs
theorem h252Fiber7Mod163Factor2Binary27Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r3Coeffs h252Fiber7Mod163Factor2b27r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs) 5 h252Fiber7Mod163Factor2Binary27Step3 hs
theorem h252Fiber7Mod163Factor2Binary27Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r4Coeffs h252Fiber7Mod163Factor2b27r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs) 10 h252Fiber7Mod163Factor2Binary27Step4 hs
theorem h252Fiber7Mod163Factor2Binary27Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r5Coeffs h252Fiber7Mod163Factor2b27r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs) 20 h252Fiber7Mod163Factor2Binary27Step5 hs
theorem h252Fiber7Mod163Factor2Binary27Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r6Coeffs h252Fiber7Mod163Factor2b27r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r7Coeffs) 40 h252Fiber7Mod163Factor2Binary27Step6 hs
theorem h252Fiber7Mod163Factor2Binary27Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r7Coeffs h252Fiber7Mod163Factor2r26Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r7Coeffs)*(h252Fiber7Mod163Factor2r26)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r7Coeffs)*(h252Fiber7Mod163Factor2r26)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs) 80 h252Fiber7Mod163Factor2Binary27Step7 hs
theorem h252Fiber7Mod163Factor2Binary27Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r8Coeffs h252Fiber7Mod163Factor2b27r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r9Coeffs) 81 h252Fiber7Mod163Factor2Binary27Step8 hs
theorem h252Fiber7Mod163Factor2Binary27Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b27r9Coeffs h252Fiber7Mod163Factor2r26Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b27r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b27q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b27r9Coeffs)*(h252Fiber7Mod163Factor2r26)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b27q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r26] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b27r9Coeffs)*(h252Fiber7Mod163Factor2r26)-(integerCoefficientEval X h252Fiber7Mod163Factor2b27r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b27q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r26 (integerCoefficientEval X h252Fiber7Mod163Factor2b27r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b27r10Coeffs) 162 h252Fiber7Mod163Factor2Binary27Step9 hs
theorem h252Fiber7Mod163Factor2Step27 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r26^163-h252Fiber7Mod163Factor2r27 := by
  have he : h252Fiber7Mod163Factor2b27r10Coeffs = h252Fiber7Mod163Factor2r27Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r27] using h252Fiber7Mod163Factor2Binary27Step10
theorem h252Fiber7Mod163Factor2Frob27 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 27-h252Fiber7Mod163Factor2r27 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob26 h252Fiber7Mod163Factor2Step27
theorem h252Fiber7Mod163Factor2Binary28Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^1-h252Fiber7Mod163Factor2r27 := by simp
theorem h252Fiber7Mod163Factor2Binary28Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r27Coeffs h252Fiber7Mod163Factor2r27Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r27)*(h252Fiber7Mod163Factor2r27)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r27)*(h252Fiber7Mod163Factor2r27)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (h252Fiber7Mod163Factor2r27) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs) 1 h252Fiber7Mod163Factor2Binary28Step0 hs
theorem h252Fiber7Mod163Factor2Binary28Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r1Coeffs h252Fiber7Mod163Factor2b28r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r2Coeffs) 2 h252Fiber7Mod163Factor2Binary28Step1 hs
theorem h252Fiber7Mod163Factor2Binary28Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r2Coeffs h252Fiber7Mod163Factor2r27Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r2Coeffs)*(h252Fiber7Mod163Factor2r27)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r2Coeffs)*(h252Fiber7Mod163Factor2r27)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs) 4 h252Fiber7Mod163Factor2Binary28Step2 hs
theorem h252Fiber7Mod163Factor2Binary28Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r3Coeffs h252Fiber7Mod163Factor2b28r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs) 5 h252Fiber7Mod163Factor2Binary28Step3 hs
theorem h252Fiber7Mod163Factor2Binary28Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r4Coeffs h252Fiber7Mod163Factor2b28r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs) 10 h252Fiber7Mod163Factor2Binary28Step4 hs
theorem h252Fiber7Mod163Factor2Binary28Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r5Coeffs h252Fiber7Mod163Factor2b28r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs) 20 h252Fiber7Mod163Factor2Binary28Step5 hs
theorem h252Fiber7Mod163Factor2Binary28Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r6Coeffs h252Fiber7Mod163Factor2b28r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r7Coeffs) 40 h252Fiber7Mod163Factor2Binary28Step6 hs
theorem h252Fiber7Mod163Factor2Binary28Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r7Coeffs h252Fiber7Mod163Factor2r27Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r7Coeffs)*(h252Fiber7Mod163Factor2r27)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r7Coeffs)*(h252Fiber7Mod163Factor2r27)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs) 80 h252Fiber7Mod163Factor2Binary28Step7 hs
theorem h252Fiber7Mod163Factor2Binary28Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r8Coeffs h252Fiber7Mod163Factor2b28r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r9Coeffs) 81 h252Fiber7Mod163Factor2Binary28Step8 hs
theorem h252Fiber7Mod163Factor2Binary28Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b28r9Coeffs h252Fiber7Mod163Factor2r27Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b28r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b28q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b28r9Coeffs)*(h252Fiber7Mod163Factor2r27)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b28q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r27] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b28r9Coeffs)*(h252Fiber7Mod163Factor2r27)-(integerCoefficientEval X h252Fiber7Mod163Factor2b28r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b28q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r27 (integerCoefficientEval X h252Fiber7Mod163Factor2b28r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b28r10Coeffs) 162 h252Fiber7Mod163Factor2Binary28Step9 hs
theorem h252Fiber7Mod163Factor2Step28 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r27^163-h252Fiber7Mod163Factor2r28 := by
  have he : h252Fiber7Mod163Factor2b28r10Coeffs = h252Fiber7Mod163Factor2r28Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r28] using h252Fiber7Mod163Factor2Binary28Step10
theorem h252Fiber7Mod163Factor2Frob28 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 28-h252Fiber7Mod163Factor2r28 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob27 h252Fiber7Mod163Factor2Step28
theorem h252Fiber7Mod163Factor2Binary29Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^1-h252Fiber7Mod163Factor2r28 := by simp
theorem h252Fiber7Mod163Factor2Binary29Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r28Coeffs h252Fiber7Mod163Factor2r28Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r28)*(h252Fiber7Mod163Factor2r28)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r28)*(h252Fiber7Mod163Factor2r28)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (h252Fiber7Mod163Factor2r28) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs) 1 h252Fiber7Mod163Factor2Binary29Step0 hs
theorem h252Fiber7Mod163Factor2Binary29Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r1Coeffs h252Fiber7Mod163Factor2b29r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r2Coeffs) 2 h252Fiber7Mod163Factor2Binary29Step1 hs
theorem h252Fiber7Mod163Factor2Binary29Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r2Coeffs h252Fiber7Mod163Factor2r28Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r2Coeffs)*(h252Fiber7Mod163Factor2r28)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r2Coeffs)*(h252Fiber7Mod163Factor2r28)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs) 4 h252Fiber7Mod163Factor2Binary29Step2 hs
theorem h252Fiber7Mod163Factor2Binary29Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r3Coeffs h252Fiber7Mod163Factor2b29r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs) 5 h252Fiber7Mod163Factor2Binary29Step3 hs
theorem h252Fiber7Mod163Factor2Binary29Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r4Coeffs h252Fiber7Mod163Factor2b29r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs) 10 h252Fiber7Mod163Factor2Binary29Step4 hs
theorem h252Fiber7Mod163Factor2Binary29Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r5Coeffs h252Fiber7Mod163Factor2b29r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs) 20 h252Fiber7Mod163Factor2Binary29Step5 hs
theorem h252Fiber7Mod163Factor2Binary29Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r6Coeffs h252Fiber7Mod163Factor2b29r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r7Coeffs) 40 h252Fiber7Mod163Factor2Binary29Step6 hs
theorem h252Fiber7Mod163Factor2Binary29Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r7Coeffs h252Fiber7Mod163Factor2r28Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r7Coeffs)*(h252Fiber7Mod163Factor2r28)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r7Coeffs)*(h252Fiber7Mod163Factor2r28)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs) 80 h252Fiber7Mod163Factor2Binary29Step7 hs
theorem h252Fiber7Mod163Factor2Binary29Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r8Coeffs h252Fiber7Mod163Factor2b29r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r9Coeffs) 81 h252Fiber7Mod163Factor2Binary29Step8 hs
theorem h252Fiber7Mod163Factor2Binary29Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b29r9Coeffs h252Fiber7Mod163Factor2r28Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b29r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b29q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b29r9Coeffs)*(h252Fiber7Mod163Factor2r28)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b29q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r28] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b29r9Coeffs)*(h252Fiber7Mod163Factor2r28)-(integerCoefficientEval X h252Fiber7Mod163Factor2b29r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b29q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r28 (integerCoefficientEval X h252Fiber7Mod163Factor2b29r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b29r10Coeffs) 162 h252Fiber7Mod163Factor2Binary29Step9 hs
theorem h252Fiber7Mod163Factor2Step29 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r28^163-h252Fiber7Mod163Factor2r29 := by
  have he : h252Fiber7Mod163Factor2b29r10Coeffs = h252Fiber7Mod163Factor2r29Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r29] using h252Fiber7Mod163Factor2Binary29Step10
theorem h252Fiber7Mod163Factor2Frob29 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 29-h252Fiber7Mod163Factor2r29 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob28 h252Fiber7Mod163Factor2Step29
theorem h252Fiber7Mod163Factor2Binary30Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^1-h252Fiber7Mod163Factor2r29 := by simp
theorem h252Fiber7Mod163Factor2Binary30Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r29Coeffs h252Fiber7Mod163Factor2r29Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r29)*(h252Fiber7Mod163Factor2r29)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r29)*(h252Fiber7Mod163Factor2r29)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (h252Fiber7Mod163Factor2r29) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs) 1 h252Fiber7Mod163Factor2Binary30Step0 hs
theorem h252Fiber7Mod163Factor2Binary30Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r1Coeffs h252Fiber7Mod163Factor2b30r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r2Coeffs) 2 h252Fiber7Mod163Factor2Binary30Step1 hs
theorem h252Fiber7Mod163Factor2Binary30Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r2Coeffs h252Fiber7Mod163Factor2r29Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r2Coeffs)*(h252Fiber7Mod163Factor2r29)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r2Coeffs)*(h252Fiber7Mod163Factor2r29)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs) 4 h252Fiber7Mod163Factor2Binary30Step2 hs
theorem h252Fiber7Mod163Factor2Binary30Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r3Coeffs h252Fiber7Mod163Factor2b30r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs) 5 h252Fiber7Mod163Factor2Binary30Step3 hs
theorem h252Fiber7Mod163Factor2Binary30Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r4Coeffs h252Fiber7Mod163Factor2b30r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs) 10 h252Fiber7Mod163Factor2Binary30Step4 hs
theorem h252Fiber7Mod163Factor2Binary30Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r5Coeffs h252Fiber7Mod163Factor2b30r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs) 20 h252Fiber7Mod163Factor2Binary30Step5 hs
theorem h252Fiber7Mod163Factor2Binary30Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r6Coeffs h252Fiber7Mod163Factor2b30r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r7Coeffs) 40 h252Fiber7Mod163Factor2Binary30Step6 hs
theorem h252Fiber7Mod163Factor2Binary30Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r7Coeffs h252Fiber7Mod163Factor2r29Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r7Coeffs)*(h252Fiber7Mod163Factor2r29)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r7Coeffs)*(h252Fiber7Mod163Factor2r29)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs) 80 h252Fiber7Mod163Factor2Binary30Step7 hs
theorem h252Fiber7Mod163Factor2Binary30Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r8Coeffs h252Fiber7Mod163Factor2b30r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r9Coeffs) 81 h252Fiber7Mod163Factor2Binary30Step8 hs
theorem h252Fiber7Mod163Factor2Binary30Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b30r9Coeffs h252Fiber7Mod163Factor2r29Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b30r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b30q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b30r9Coeffs)*(h252Fiber7Mod163Factor2r29)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b30q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r29] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b30r9Coeffs)*(h252Fiber7Mod163Factor2r29)-(integerCoefficientEval X h252Fiber7Mod163Factor2b30r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b30q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r29 (integerCoefficientEval X h252Fiber7Mod163Factor2b30r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b30r10Coeffs) 162 h252Fiber7Mod163Factor2Binary30Step9 hs
theorem h252Fiber7Mod163Factor2Step30 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r29^163-h252Fiber7Mod163Factor2r30 := by
  have he : h252Fiber7Mod163Factor2b30r10Coeffs = h252Fiber7Mod163Factor2r30Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r30] using h252Fiber7Mod163Factor2Binary30Step10
theorem h252Fiber7Mod163Factor2Frob30 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 30-h252Fiber7Mod163Factor2r30 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob29 h252Fiber7Mod163Factor2Step30
end
end Biunimodular.F11
