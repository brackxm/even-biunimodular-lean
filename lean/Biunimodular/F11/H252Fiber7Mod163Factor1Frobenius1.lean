/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor1Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor1Frob0 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 0 - h252Fiber7Mod163Factor1r0 := by
  simp [h252Fiber7Mod163Factor1r0, h252Fiber7Mod163Factor1r0Coeffs, frobeniusIter, integerCoefficientEval]
theorem h252Fiber7Mod163Factor1Binary1Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^1-h252Fiber7Mod163Factor1r0 := by simp
theorem h252Fiber7Mod163Factor1Binary1Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r0Coeffs h252Fiber7Mod163Factor1r0Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r0)*(h252Fiber7Mod163Factor1r0)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r0)*(h252Fiber7Mod163Factor1r0)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (h252Fiber7Mod163Factor1r0) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs) 1 h252Fiber7Mod163Factor1Binary1Step0 hs
theorem h252Fiber7Mod163Factor1Binary1Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r1Coeffs h252Fiber7Mod163Factor1b1r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r2Coeffs) 2 h252Fiber7Mod163Factor1Binary1Step1 hs
theorem h252Fiber7Mod163Factor1Binary1Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r2Coeffs h252Fiber7Mod163Factor1r0Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r2Coeffs)*(h252Fiber7Mod163Factor1r0)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r2Coeffs)*(h252Fiber7Mod163Factor1r0)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs) 4 h252Fiber7Mod163Factor1Binary1Step2 hs
theorem h252Fiber7Mod163Factor1Binary1Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r3Coeffs h252Fiber7Mod163Factor1b1r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs) 5 h252Fiber7Mod163Factor1Binary1Step3 hs
theorem h252Fiber7Mod163Factor1Binary1Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r4Coeffs h252Fiber7Mod163Factor1b1r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs) 10 h252Fiber7Mod163Factor1Binary1Step4 hs
theorem h252Fiber7Mod163Factor1Binary1Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r5Coeffs h252Fiber7Mod163Factor1b1r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs) 20 h252Fiber7Mod163Factor1Binary1Step5 hs
theorem h252Fiber7Mod163Factor1Binary1Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r6Coeffs h252Fiber7Mod163Factor1b1r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r7Coeffs) 40 h252Fiber7Mod163Factor1Binary1Step6 hs
theorem h252Fiber7Mod163Factor1Binary1Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r7Coeffs h252Fiber7Mod163Factor1r0Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r7Coeffs)*(h252Fiber7Mod163Factor1r0)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r7Coeffs)*(h252Fiber7Mod163Factor1r0)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs) 80 h252Fiber7Mod163Factor1Binary1Step7 hs
theorem h252Fiber7Mod163Factor1Binary1Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r8Coeffs h252Fiber7Mod163Factor1b1r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r9Coeffs) 81 h252Fiber7Mod163Factor1Binary1Step8 hs
theorem h252Fiber7Mod163Factor1Binary1Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b1r9Coeffs h252Fiber7Mod163Factor1r0Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b1r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b1q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b1r9Coeffs)*(h252Fiber7Mod163Factor1r0)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b1q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r0] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b1r9Coeffs)*(h252Fiber7Mod163Factor1r0)-(integerCoefficientEval X h252Fiber7Mod163Factor1b1r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b1q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r0 (integerCoefficientEval X h252Fiber7Mod163Factor1b1r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b1r10Coeffs) 162 h252Fiber7Mod163Factor1Binary1Step9 hs
theorem h252Fiber7Mod163Factor1Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r0^163-h252Fiber7Mod163Factor1r1 := by
  have he : h252Fiber7Mod163Factor1b1r10Coeffs = h252Fiber7Mod163Factor1r1Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r1] using h252Fiber7Mod163Factor1Binary1Step10
theorem h252Fiber7Mod163Factor1Frob1 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 1-h252Fiber7Mod163Factor1r1 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob0 h252Fiber7Mod163Factor1Step1
theorem h252Fiber7Mod163Factor1Binary2Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^1-h252Fiber7Mod163Factor1r1 := by simp
theorem h252Fiber7Mod163Factor1Binary2Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r1Coeffs h252Fiber7Mod163Factor1r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r1)*(h252Fiber7Mod163Factor1r1)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r1)*(h252Fiber7Mod163Factor1r1)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (h252Fiber7Mod163Factor1r1) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs) 1 h252Fiber7Mod163Factor1Binary2Step0 hs
theorem h252Fiber7Mod163Factor1Binary2Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r1Coeffs h252Fiber7Mod163Factor1b2r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r2Coeffs) 2 h252Fiber7Mod163Factor1Binary2Step1 hs
theorem h252Fiber7Mod163Factor1Binary2Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r2Coeffs h252Fiber7Mod163Factor1r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r2Coeffs)*(h252Fiber7Mod163Factor1r1)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r2Coeffs)*(h252Fiber7Mod163Factor1r1)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs) 4 h252Fiber7Mod163Factor1Binary2Step2 hs
theorem h252Fiber7Mod163Factor1Binary2Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r3Coeffs h252Fiber7Mod163Factor1b2r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs) 5 h252Fiber7Mod163Factor1Binary2Step3 hs
theorem h252Fiber7Mod163Factor1Binary2Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r4Coeffs h252Fiber7Mod163Factor1b2r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs) 10 h252Fiber7Mod163Factor1Binary2Step4 hs
theorem h252Fiber7Mod163Factor1Binary2Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r5Coeffs h252Fiber7Mod163Factor1b2r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs) 20 h252Fiber7Mod163Factor1Binary2Step5 hs
theorem h252Fiber7Mod163Factor1Binary2Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r6Coeffs h252Fiber7Mod163Factor1b2r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r7Coeffs) 40 h252Fiber7Mod163Factor1Binary2Step6 hs
theorem h252Fiber7Mod163Factor1Binary2Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r7Coeffs h252Fiber7Mod163Factor1r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r7Coeffs)*(h252Fiber7Mod163Factor1r1)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r7Coeffs)*(h252Fiber7Mod163Factor1r1)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs) 80 h252Fiber7Mod163Factor1Binary2Step7 hs
theorem h252Fiber7Mod163Factor1Binary2Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r8Coeffs h252Fiber7Mod163Factor1b2r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r9Coeffs) 81 h252Fiber7Mod163Factor1Binary2Step8 hs
theorem h252Fiber7Mod163Factor1Binary2Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b2r9Coeffs h252Fiber7Mod163Factor1r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b2r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b2q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b2r9Coeffs)*(h252Fiber7Mod163Factor1r1)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b2q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b2r9Coeffs)*(h252Fiber7Mod163Factor1r1)-(integerCoefficientEval X h252Fiber7Mod163Factor1b2r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b2q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r1 (integerCoefficientEval X h252Fiber7Mod163Factor1b2r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b2r10Coeffs) 162 h252Fiber7Mod163Factor1Binary2Step9 hs
theorem h252Fiber7Mod163Factor1Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r1^163-h252Fiber7Mod163Factor1r2 := by
  have he : h252Fiber7Mod163Factor1b2r10Coeffs = h252Fiber7Mod163Factor1r2Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r2] using h252Fiber7Mod163Factor1Binary2Step10
theorem h252Fiber7Mod163Factor1Frob2 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 2-h252Fiber7Mod163Factor1r2 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob1 h252Fiber7Mod163Factor1Step2
theorem h252Fiber7Mod163Factor1Binary3Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^1-h252Fiber7Mod163Factor1r2 := by simp
theorem h252Fiber7Mod163Factor1Binary3Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r2Coeffs h252Fiber7Mod163Factor1r2Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r2)*(h252Fiber7Mod163Factor1r2)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r2)*(h252Fiber7Mod163Factor1r2)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (h252Fiber7Mod163Factor1r2) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs) 1 h252Fiber7Mod163Factor1Binary3Step0 hs
theorem h252Fiber7Mod163Factor1Binary3Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r1Coeffs h252Fiber7Mod163Factor1b3r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r2Coeffs) 2 h252Fiber7Mod163Factor1Binary3Step1 hs
theorem h252Fiber7Mod163Factor1Binary3Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r2Coeffs h252Fiber7Mod163Factor1r2Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r2Coeffs)*(h252Fiber7Mod163Factor1r2)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r2Coeffs)*(h252Fiber7Mod163Factor1r2)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs) 4 h252Fiber7Mod163Factor1Binary3Step2 hs
theorem h252Fiber7Mod163Factor1Binary3Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r3Coeffs h252Fiber7Mod163Factor1b3r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs) 5 h252Fiber7Mod163Factor1Binary3Step3 hs
theorem h252Fiber7Mod163Factor1Binary3Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r4Coeffs h252Fiber7Mod163Factor1b3r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs) 10 h252Fiber7Mod163Factor1Binary3Step4 hs
theorem h252Fiber7Mod163Factor1Binary3Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r5Coeffs h252Fiber7Mod163Factor1b3r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs) 20 h252Fiber7Mod163Factor1Binary3Step5 hs
theorem h252Fiber7Mod163Factor1Binary3Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r6Coeffs h252Fiber7Mod163Factor1b3r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r7Coeffs) 40 h252Fiber7Mod163Factor1Binary3Step6 hs
theorem h252Fiber7Mod163Factor1Binary3Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r7Coeffs h252Fiber7Mod163Factor1r2Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r7Coeffs)*(h252Fiber7Mod163Factor1r2)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r7Coeffs)*(h252Fiber7Mod163Factor1r2)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs) 80 h252Fiber7Mod163Factor1Binary3Step7 hs
theorem h252Fiber7Mod163Factor1Binary3Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r8Coeffs h252Fiber7Mod163Factor1b3r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r9Coeffs) 81 h252Fiber7Mod163Factor1Binary3Step8 hs
theorem h252Fiber7Mod163Factor1Binary3Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b3r9Coeffs h252Fiber7Mod163Factor1r2Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b3r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b3q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b3r9Coeffs)*(h252Fiber7Mod163Factor1r2)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b3q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b3r9Coeffs)*(h252Fiber7Mod163Factor1r2)-(integerCoefficientEval X h252Fiber7Mod163Factor1b3r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b3q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r2 (integerCoefficientEval X h252Fiber7Mod163Factor1b3r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b3r10Coeffs) 162 h252Fiber7Mod163Factor1Binary3Step9 hs
theorem h252Fiber7Mod163Factor1Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r2^163-h252Fiber7Mod163Factor1r3 := by
  have he : h252Fiber7Mod163Factor1b3r10Coeffs = h252Fiber7Mod163Factor1r3Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r3] using h252Fiber7Mod163Factor1Binary3Step10
theorem h252Fiber7Mod163Factor1Frob3 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 3-h252Fiber7Mod163Factor1r3 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob2 h252Fiber7Mod163Factor1Step3
theorem h252Fiber7Mod163Factor1Binary4Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^1-h252Fiber7Mod163Factor1r3 := by simp
theorem h252Fiber7Mod163Factor1Binary4Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r3Coeffs h252Fiber7Mod163Factor1r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r3)*(h252Fiber7Mod163Factor1r3)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r3)*(h252Fiber7Mod163Factor1r3)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (h252Fiber7Mod163Factor1r3) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs) 1 h252Fiber7Mod163Factor1Binary4Step0 hs
theorem h252Fiber7Mod163Factor1Binary4Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r1Coeffs h252Fiber7Mod163Factor1b4r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r2Coeffs) 2 h252Fiber7Mod163Factor1Binary4Step1 hs
theorem h252Fiber7Mod163Factor1Binary4Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r2Coeffs h252Fiber7Mod163Factor1r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r2Coeffs)*(h252Fiber7Mod163Factor1r3)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r2Coeffs)*(h252Fiber7Mod163Factor1r3)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs) 4 h252Fiber7Mod163Factor1Binary4Step2 hs
theorem h252Fiber7Mod163Factor1Binary4Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r3Coeffs h252Fiber7Mod163Factor1b4r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs) 5 h252Fiber7Mod163Factor1Binary4Step3 hs
theorem h252Fiber7Mod163Factor1Binary4Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r4Coeffs h252Fiber7Mod163Factor1b4r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs) 10 h252Fiber7Mod163Factor1Binary4Step4 hs
theorem h252Fiber7Mod163Factor1Binary4Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r5Coeffs h252Fiber7Mod163Factor1b4r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs) 20 h252Fiber7Mod163Factor1Binary4Step5 hs
theorem h252Fiber7Mod163Factor1Binary4Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r6Coeffs h252Fiber7Mod163Factor1b4r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r7Coeffs) 40 h252Fiber7Mod163Factor1Binary4Step6 hs
theorem h252Fiber7Mod163Factor1Binary4Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r7Coeffs h252Fiber7Mod163Factor1r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r7Coeffs)*(h252Fiber7Mod163Factor1r3)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r7Coeffs)*(h252Fiber7Mod163Factor1r3)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs) 80 h252Fiber7Mod163Factor1Binary4Step7 hs
theorem h252Fiber7Mod163Factor1Binary4Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r8Coeffs h252Fiber7Mod163Factor1b4r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r9Coeffs) 81 h252Fiber7Mod163Factor1Binary4Step8 hs
theorem h252Fiber7Mod163Factor1Binary4Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b4r9Coeffs h252Fiber7Mod163Factor1r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b4r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b4q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b4r9Coeffs)*(h252Fiber7Mod163Factor1r3)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b4q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r3] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b4r9Coeffs)*(h252Fiber7Mod163Factor1r3)-(integerCoefficientEval X h252Fiber7Mod163Factor1b4r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b4q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r3 (integerCoefficientEval X h252Fiber7Mod163Factor1b4r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b4r10Coeffs) 162 h252Fiber7Mod163Factor1Binary4Step9 hs
theorem h252Fiber7Mod163Factor1Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r3^163-h252Fiber7Mod163Factor1r4 := by
  have he : h252Fiber7Mod163Factor1b4r10Coeffs = h252Fiber7Mod163Factor1r4Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r4] using h252Fiber7Mod163Factor1Binary4Step10
theorem h252Fiber7Mod163Factor1Frob4 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 4-h252Fiber7Mod163Factor1r4 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob3 h252Fiber7Mod163Factor1Step4
theorem h252Fiber7Mod163Factor1Binary5Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^1-h252Fiber7Mod163Factor1r4 := by simp
theorem h252Fiber7Mod163Factor1Binary5Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r4Coeffs h252Fiber7Mod163Factor1r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r4)*(h252Fiber7Mod163Factor1r4)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r4)*(h252Fiber7Mod163Factor1r4)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (h252Fiber7Mod163Factor1r4) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs) 1 h252Fiber7Mod163Factor1Binary5Step0 hs
theorem h252Fiber7Mod163Factor1Binary5Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r1Coeffs h252Fiber7Mod163Factor1b5r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r2Coeffs) 2 h252Fiber7Mod163Factor1Binary5Step1 hs
theorem h252Fiber7Mod163Factor1Binary5Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r2Coeffs h252Fiber7Mod163Factor1r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r2Coeffs)*(h252Fiber7Mod163Factor1r4)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r2Coeffs)*(h252Fiber7Mod163Factor1r4)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs) 4 h252Fiber7Mod163Factor1Binary5Step2 hs
theorem h252Fiber7Mod163Factor1Binary5Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r3Coeffs h252Fiber7Mod163Factor1b5r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs) 5 h252Fiber7Mod163Factor1Binary5Step3 hs
theorem h252Fiber7Mod163Factor1Binary5Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r4Coeffs h252Fiber7Mod163Factor1b5r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs) 10 h252Fiber7Mod163Factor1Binary5Step4 hs
theorem h252Fiber7Mod163Factor1Binary5Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r5Coeffs h252Fiber7Mod163Factor1b5r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs) 20 h252Fiber7Mod163Factor1Binary5Step5 hs
theorem h252Fiber7Mod163Factor1Binary5Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r6Coeffs h252Fiber7Mod163Factor1b5r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r7Coeffs) 40 h252Fiber7Mod163Factor1Binary5Step6 hs
theorem h252Fiber7Mod163Factor1Binary5Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r7Coeffs h252Fiber7Mod163Factor1r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r7Coeffs)*(h252Fiber7Mod163Factor1r4)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r7Coeffs)*(h252Fiber7Mod163Factor1r4)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs) 80 h252Fiber7Mod163Factor1Binary5Step7 hs
theorem h252Fiber7Mod163Factor1Binary5Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r8Coeffs h252Fiber7Mod163Factor1b5r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r9Coeffs) 81 h252Fiber7Mod163Factor1Binary5Step8 hs
theorem h252Fiber7Mod163Factor1Binary5Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b5r9Coeffs h252Fiber7Mod163Factor1r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b5r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b5q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b5r9Coeffs)*(h252Fiber7Mod163Factor1r4)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b5q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b5r9Coeffs)*(h252Fiber7Mod163Factor1r4)-(integerCoefficientEval X h252Fiber7Mod163Factor1b5r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b5q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r4 (integerCoefficientEval X h252Fiber7Mod163Factor1b5r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b5r10Coeffs) 162 h252Fiber7Mod163Factor1Binary5Step9 hs
theorem h252Fiber7Mod163Factor1Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r4^163-h252Fiber7Mod163Factor1r5 := by
  have he : h252Fiber7Mod163Factor1b5r10Coeffs = h252Fiber7Mod163Factor1r5Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r5] using h252Fiber7Mod163Factor1Binary5Step10
theorem h252Fiber7Mod163Factor1Frob5 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 5-h252Fiber7Mod163Factor1r5 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob4 h252Fiber7Mod163Factor1Step5
end
end Biunimodular.F11
