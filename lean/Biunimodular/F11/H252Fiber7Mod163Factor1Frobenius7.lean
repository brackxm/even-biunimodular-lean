/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor1Frobenius6

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor1Binary31Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^1-h252Fiber7Mod163Factor1r30 := by simp
theorem h252Fiber7Mod163Factor1Binary31Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r30Coeffs h252Fiber7Mod163Factor1r30Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r30)*(h252Fiber7Mod163Factor1r30)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r30)*(h252Fiber7Mod163Factor1r30)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (h252Fiber7Mod163Factor1r30) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs) 1 h252Fiber7Mod163Factor1Binary31Step0 hs
theorem h252Fiber7Mod163Factor1Binary31Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r1Coeffs h252Fiber7Mod163Factor1b31r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r2Coeffs) 2 h252Fiber7Mod163Factor1Binary31Step1 hs
theorem h252Fiber7Mod163Factor1Binary31Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r2Coeffs h252Fiber7Mod163Factor1r30Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r2Coeffs)*(h252Fiber7Mod163Factor1r30)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r2Coeffs)*(h252Fiber7Mod163Factor1r30)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs) 4 h252Fiber7Mod163Factor1Binary31Step2 hs
theorem h252Fiber7Mod163Factor1Binary31Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r3Coeffs h252Fiber7Mod163Factor1b31r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs) 5 h252Fiber7Mod163Factor1Binary31Step3 hs
theorem h252Fiber7Mod163Factor1Binary31Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r4Coeffs h252Fiber7Mod163Factor1b31r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs) 10 h252Fiber7Mod163Factor1Binary31Step4 hs
theorem h252Fiber7Mod163Factor1Binary31Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r5Coeffs h252Fiber7Mod163Factor1b31r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs) 20 h252Fiber7Mod163Factor1Binary31Step5 hs
theorem h252Fiber7Mod163Factor1Binary31Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r6Coeffs h252Fiber7Mod163Factor1b31r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r7Coeffs) 40 h252Fiber7Mod163Factor1Binary31Step6 hs
theorem h252Fiber7Mod163Factor1Binary31Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r7Coeffs h252Fiber7Mod163Factor1r30Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r7Coeffs)*(h252Fiber7Mod163Factor1r30)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r7Coeffs)*(h252Fiber7Mod163Factor1r30)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs) 80 h252Fiber7Mod163Factor1Binary31Step7 hs
theorem h252Fiber7Mod163Factor1Binary31Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r8Coeffs h252Fiber7Mod163Factor1b31r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r9Coeffs) 81 h252Fiber7Mod163Factor1Binary31Step8 hs
theorem h252Fiber7Mod163Factor1Binary31Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b31r9Coeffs h252Fiber7Mod163Factor1r30Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b31r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b31q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b31r9Coeffs)*(h252Fiber7Mod163Factor1r30)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b31q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r30] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b31r9Coeffs)*(h252Fiber7Mod163Factor1r30)-(integerCoefficientEval X h252Fiber7Mod163Factor1b31r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b31q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r30 (integerCoefficientEval X h252Fiber7Mod163Factor1b31r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b31r10Coeffs) 162 h252Fiber7Mod163Factor1Binary31Step9 hs
theorem h252Fiber7Mod163Factor1Step31 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r30^163-h252Fiber7Mod163Factor1r31 := by
  have he : h252Fiber7Mod163Factor1b31r10Coeffs = h252Fiber7Mod163Factor1r31Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r31] using h252Fiber7Mod163Factor1Binary31Step10
theorem h252Fiber7Mod163Factor1Frob31 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 31-h252Fiber7Mod163Factor1r31 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob30 h252Fiber7Mod163Factor1Step31
theorem h252Fiber7Mod163Factor1Binary32Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^1-h252Fiber7Mod163Factor1r31 := by simp
theorem h252Fiber7Mod163Factor1Binary32Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r31Coeffs h252Fiber7Mod163Factor1r31Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r31)*(h252Fiber7Mod163Factor1r31)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r31)*(h252Fiber7Mod163Factor1r31)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (h252Fiber7Mod163Factor1r31) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs) 1 h252Fiber7Mod163Factor1Binary32Step0 hs
theorem h252Fiber7Mod163Factor1Binary32Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r1Coeffs h252Fiber7Mod163Factor1b32r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r2Coeffs) 2 h252Fiber7Mod163Factor1Binary32Step1 hs
theorem h252Fiber7Mod163Factor1Binary32Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r2Coeffs h252Fiber7Mod163Factor1r31Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r2Coeffs)*(h252Fiber7Mod163Factor1r31)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r2Coeffs)*(h252Fiber7Mod163Factor1r31)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs) 4 h252Fiber7Mod163Factor1Binary32Step2 hs
theorem h252Fiber7Mod163Factor1Binary32Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r3Coeffs h252Fiber7Mod163Factor1b32r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs) 5 h252Fiber7Mod163Factor1Binary32Step3 hs
theorem h252Fiber7Mod163Factor1Binary32Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r4Coeffs h252Fiber7Mod163Factor1b32r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs) 10 h252Fiber7Mod163Factor1Binary32Step4 hs
theorem h252Fiber7Mod163Factor1Binary32Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r5Coeffs h252Fiber7Mod163Factor1b32r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs) 20 h252Fiber7Mod163Factor1Binary32Step5 hs
theorem h252Fiber7Mod163Factor1Binary32Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r6Coeffs h252Fiber7Mod163Factor1b32r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r7Coeffs) 40 h252Fiber7Mod163Factor1Binary32Step6 hs
theorem h252Fiber7Mod163Factor1Binary32Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r7Coeffs h252Fiber7Mod163Factor1r31Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r7Coeffs)*(h252Fiber7Mod163Factor1r31)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r7Coeffs)*(h252Fiber7Mod163Factor1r31)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs) 80 h252Fiber7Mod163Factor1Binary32Step7 hs
theorem h252Fiber7Mod163Factor1Binary32Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r8Coeffs h252Fiber7Mod163Factor1b32r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r9Coeffs) 81 h252Fiber7Mod163Factor1Binary32Step8 hs
theorem h252Fiber7Mod163Factor1Binary32Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b32r9Coeffs h252Fiber7Mod163Factor1r31Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b32r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b32q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b32r9Coeffs)*(h252Fiber7Mod163Factor1r31)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b32q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r31] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b32r9Coeffs)*(h252Fiber7Mod163Factor1r31)-(integerCoefficientEval X h252Fiber7Mod163Factor1b32r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b32q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r31 (integerCoefficientEval X h252Fiber7Mod163Factor1b32r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b32r10Coeffs) 162 h252Fiber7Mod163Factor1Binary32Step9 hs
theorem h252Fiber7Mod163Factor1Step32 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r31^163-h252Fiber7Mod163Factor1r32 := by
  have he : h252Fiber7Mod163Factor1b32r10Coeffs = h252Fiber7Mod163Factor1r32Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r32] using h252Fiber7Mod163Factor1Binary32Step10
theorem h252Fiber7Mod163Factor1Frob32 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 32-h252Fiber7Mod163Factor1r32 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob31 h252Fiber7Mod163Factor1Step32
theorem h252Fiber7Mod163Factor1Binary33Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^1-h252Fiber7Mod163Factor1r32 := by simp
theorem h252Fiber7Mod163Factor1Binary33Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r32Coeffs h252Fiber7Mod163Factor1r32Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r32)*(h252Fiber7Mod163Factor1r32)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r32)*(h252Fiber7Mod163Factor1r32)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (h252Fiber7Mod163Factor1r32) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs) 1 h252Fiber7Mod163Factor1Binary33Step0 hs
theorem h252Fiber7Mod163Factor1Binary33Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r1Coeffs h252Fiber7Mod163Factor1b33r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r2Coeffs) 2 h252Fiber7Mod163Factor1Binary33Step1 hs
theorem h252Fiber7Mod163Factor1Binary33Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r2Coeffs h252Fiber7Mod163Factor1r32Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r2Coeffs)*(h252Fiber7Mod163Factor1r32)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r2Coeffs)*(h252Fiber7Mod163Factor1r32)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs) 4 h252Fiber7Mod163Factor1Binary33Step2 hs
theorem h252Fiber7Mod163Factor1Binary33Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r3Coeffs h252Fiber7Mod163Factor1b33r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs) 5 h252Fiber7Mod163Factor1Binary33Step3 hs
theorem h252Fiber7Mod163Factor1Binary33Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r4Coeffs h252Fiber7Mod163Factor1b33r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs) 10 h252Fiber7Mod163Factor1Binary33Step4 hs
theorem h252Fiber7Mod163Factor1Binary33Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r5Coeffs h252Fiber7Mod163Factor1b33r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs) 20 h252Fiber7Mod163Factor1Binary33Step5 hs
theorem h252Fiber7Mod163Factor1Binary33Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r6Coeffs h252Fiber7Mod163Factor1b33r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r7Coeffs) 40 h252Fiber7Mod163Factor1Binary33Step6 hs
theorem h252Fiber7Mod163Factor1Binary33Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r7Coeffs h252Fiber7Mod163Factor1r32Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r7Coeffs)*(h252Fiber7Mod163Factor1r32)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r7Coeffs)*(h252Fiber7Mod163Factor1r32)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs) 80 h252Fiber7Mod163Factor1Binary33Step7 hs
theorem h252Fiber7Mod163Factor1Binary33Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r8Coeffs h252Fiber7Mod163Factor1b33r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r9Coeffs) 81 h252Fiber7Mod163Factor1Binary33Step8 hs
theorem h252Fiber7Mod163Factor1Binary33Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b33r9Coeffs h252Fiber7Mod163Factor1r32Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b33r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b33q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b33r9Coeffs)*(h252Fiber7Mod163Factor1r32)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b33q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r32] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b33r9Coeffs)*(h252Fiber7Mod163Factor1r32)-(integerCoefficientEval X h252Fiber7Mod163Factor1b33r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b33q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r32 (integerCoefficientEval X h252Fiber7Mod163Factor1b33r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b33r10Coeffs) 162 h252Fiber7Mod163Factor1Binary33Step9 hs
theorem h252Fiber7Mod163Factor1Step33 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r32^163-h252Fiber7Mod163Factor1r33 := by
  have he : h252Fiber7Mod163Factor1b33r10Coeffs = h252Fiber7Mod163Factor1r33Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r33] using h252Fiber7Mod163Factor1Binary33Step10
theorem h252Fiber7Mod163Factor1Frob33 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 33-h252Fiber7Mod163Factor1r33 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob32 h252Fiber7Mod163Factor1Step33
theorem h252Fiber7Mod163Factor1Binary34Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^1-h252Fiber7Mod163Factor1r33 := by simp
theorem h252Fiber7Mod163Factor1Binary34Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r33Coeffs h252Fiber7Mod163Factor1r33Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r33)*(h252Fiber7Mod163Factor1r33)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r33)*(h252Fiber7Mod163Factor1r33)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (h252Fiber7Mod163Factor1r33) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs) 1 h252Fiber7Mod163Factor1Binary34Step0 hs
theorem h252Fiber7Mod163Factor1Binary34Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r1Coeffs h252Fiber7Mod163Factor1b34r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r2Coeffs) 2 h252Fiber7Mod163Factor1Binary34Step1 hs
theorem h252Fiber7Mod163Factor1Binary34Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r2Coeffs h252Fiber7Mod163Factor1r33Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r2Coeffs)*(h252Fiber7Mod163Factor1r33)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r2Coeffs)*(h252Fiber7Mod163Factor1r33)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs) 4 h252Fiber7Mod163Factor1Binary34Step2 hs
theorem h252Fiber7Mod163Factor1Binary34Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r3Coeffs h252Fiber7Mod163Factor1b34r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs) 5 h252Fiber7Mod163Factor1Binary34Step3 hs
theorem h252Fiber7Mod163Factor1Binary34Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r4Coeffs h252Fiber7Mod163Factor1b34r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs) 10 h252Fiber7Mod163Factor1Binary34Step4 hs
theorem h252Fiber7Mod163Factor1Binary34Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r5Coeffs h252Fiber7Mod163Factor1b34r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs) 20 h252Fiber7Mod163Factor1Binary34Step5 hs
theorem h252Fiber7Mod163Factor1Binary34Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r6Coeffs h252Fiber7Mod163Factor1b34r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r7Coeffs) 40 h252Fiber7Mod163Factor1Binary34Step6 hs
theorem h252Fiber7Mod163Factor1Binary34Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r7Coeffs h252Fiber7Mod163Factor1r33Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r7Coeffs)*(h252Fiber7Mod163Factor1r33)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r7Coeffs)*(h252Fiber7Mod163Factor1r33)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs) 80 h252Fiber7Mod163Factor1Binary34Step7 hs
theorem h252Fiber7Mod163Factor1Binary34Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r8Coeffs h252Fiber7Mod163Factor1b34r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r9Coeffs) 81 h252Fiber7Mod163Factor1Binary34Step8 hs
theorem h252Fiber7Mod163Factor1Binary34Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b34r9Coeffs h252Fiber7Mod163Factor1r33Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b34r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b34q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b34r9Coeffs)*(h252Fiber7Mod163Factor1r33)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b34q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r33] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b34r9Coeffs)*(h252Fiber7Mod163Factor1r33)-(integerCoefficientEval X h252Fiber7Mod163Factor1b34r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b34q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r33 (integerCoefficientEval X h252Fiber7Mod163Factor1b34r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b34r10Coeffs) 162 h252Fiber7Mod163Factor1Binary34Step9 hs
theorem h252Fiber7Mod163Factor1Step34 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r33^163-h252Fiber7Mod163Factor1r34 := by
  have he : h252Fiber7Mod163Factor1b34r10Coeffs = h252Fiber7Mod163Factor1r34Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r34] using h252Fiber7Mod163Factor1Binary34Step10
theorem h252Fiber7Mod163Factor1Frob34 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 34-h252Fiber7Mod163Factor1r34 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob33 h252Fiber7Mod163Factor1Step34
theorem h252Fiber7Mod163Factor1Binary35Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^1-h252Fiber7Mod163Factor1r34 := by simp
theorem h252Fiber7Mod163Factor1Binary35Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r34Coeffs h252Fiber7Mod163Factor1r34Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r34)*(h252Fiber7Mod163Factor1r34)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r34)*(h252Fiber7Mod163Factor1r34)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (h252Fiber7Mod163Factor1r34) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs) 1 h252Fiber7Mod163Factor1Binary35Step0 hs
theorem h252Fiber7Mod163Factor1Binary35Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r1Coeffs h252Fiber7Mod163Factor1b35r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r2Coeffs) 2 h252Fiber7Mod163Factor1Binary35Step1 hs
theorem h252Fiber7Mod163Factor1Binary35Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r2Coeffs h252Fiber7Mod163Factor1r34Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r2Coeffs)*(h252Fiber7Mod163Factor1r34)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r2Coeffs)*(h252Fiber7Mod163Factor1r34)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs) 4 h252Fiber7Mod163Factor1Binary35Step2 hs
theorem h252Fiber7Mod163Factor1Binary35Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r3Coeffs h252Fiber7Mod163Factor1b35r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs) 5 h252Fiber7Mod163Factor1Binary35Step3 hs
theorem h252Fiber7Mod163Factor1Binary35Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r4Coeffs h252Fiber7Mod163Factor1b35r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs) 10 h252Fiber7Mod163Factor1Binary35Step4 hs
theorem h252Fiber7Mod163Factor1Binary35Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r5Coeffs h252Fiber7Mod163Factor1b35r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs) 20 h252Fiber7Mod163Factor1Binary35Step5 hs
theorem h252Fiber7Mod163Factor1Binary35Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r6Coeffs h252Fiber7Mod163Factor1b35r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r7Coeffs) 40 h252Fiber7Mod163Factor1Binary35Step6 hs
theorem h252Fiber7Mod163Factor1Binary35Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r7Coeffs h252Fiber7Mod163Factor1r34Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r7Coeffs)*(h252Fiber7Mod163Factor1r34)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r7Coeffs)*(h252Fiber7Mod163Factor1r34)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs) 80 h252Fiber7Mod163Factor1Binary35Step7 hs
theorem h252Fiber7Mod163Factor1Binary35Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r8Coeffs h252Fiber7Mod163Factor1b35r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r9Coeffs) 81 h252Fiber7Mod163Factor1Binary35Step8 hs
theorem h252Fiber7Mod163Factor1Binary35Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b35r9Coeffs h252Fiber7Mod163Factor1r34Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b35r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b35q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b35r9Coeffs)*(h252Fiber7Mod163Factor1r34)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b35q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r34] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b35r9Coeffs)*(h252Fiber7Mod163Factor1r34)-(integerCoefficientEval X h252Fiber7Mod163Factor1b35r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b35q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r34 (integerCoefficientEval X h252Fiber7Mod163Factor1b35r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b35r10Coeffs) 162 h252Fiber7Mod163Factor1Binary35Step9 hs
theorem h252Fiber7Mod163Factor1Step35 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r34^163-h252Fiber7Mod163Factor1r35 := by
  have he : h252Fiber7Mod163Factor1b35r10Coeffs = h252Fiber7Mod163Factor1r35Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r35] using h252Fiber7Mod163Factor1Binary35Step10
theorem h252Fiber7Mod163Factor1Frob35 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 35-h252Fiber7Mod163Factor1r35 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob34 h252Fiber7Mod163Factor1Step35
end
end Biunimodular.F11
