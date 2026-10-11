/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor1Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor1Binary6Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^1-h252Fiber7Mod163Factor1r5 := by simp
theorem h252Fiber7Mod163Factor1Binary6Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r5Coeffs h252Fiber7Mod163Factor1r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r5)*(h252Fiber7Mod163Factor1r5)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r5)*(h252Fiber7Mod163Factor1r5)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (h252Fiber7Mod163Factor1r5) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs) 1 h252Fiber7Mod163Factor1Binary6Step0 hs
theorem h252Fiber7Mod163Factor1Binary6Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r1Coeffs h252Fiber7Mod163Factor1b6r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r2Coeffs) 2 h252Fiber7Mod163Factor1Binary6Step1 hs
theorem h252Fiber7Mod163Factor1Binary6Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r2Coeffs h252Fiber7Mod163Factor1r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r2Coeffs)*(h252Fiber7Mod163Factor1r5)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r2Coeffs)*(h252Fiber7Mod163Factor1r5)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs) 4 h252Fiber7Mod163Factor1Binary6Step2 hs
theorem h252Fiber7Mod163Factor1Binary6Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r3Coeffs h252Fiber7Mod163Factor1b6r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs) 5 h252Fiber7Mod163Factor1Binary6Step3 hs
theorem h252Fiber7Mod163Factor1Binary6Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r4Coeffs h252Fiber7Mod163Factor1b6r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs) 10 h252Fiber7Mod163Factor1Binary6Step4 hs
theorem h252Fiber7Mod163Factor1Binary6Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r5Coeffs h252Fiber7Mod163Factor1b6r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs) 20 h252Fiber7Mod163Factor1Binary6Step5 hs
theorem h252Fiber7Mod163Factor1Binary6Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r6Coeffs h252Fiber7Mod163Factor1b6r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r7Coeffs) 40 h252Fiber7Mod163Factor1Binary6Step6 hs
theorem h252Fiber7Mod163Factor1Binary6Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r7Coeffs h252Fiber7Mod163Factor1r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r7Coeffs)*(h252Fiber7Mod163Factor1r5)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r7Coeffs)*(h252Fiber7Mod163Factor1r5)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs) 80 h252Fiber7Mod163Factor1Binary6Step7 hs
theorem h252Fiber7Mod163Factor1Binary6Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r8Coeffs h252Fiber7Mod163Factor1b6r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r9Coeffs) 81 h252Fiber7Mod163Factor1Binary6Step8 hs
theorem h252Fiber7Mod163Factor1Binary6Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b6r9Coeffs h252Fiber7Mod163Factor1r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b6r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b6q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b6r9Coeffs)*(h252Fiber7Mod163Factor1r5)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b6q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b6r9Coeffs)*(h252Fiber7Mod163Factor1r5)-(integerCoefficientEval X h252Fiber7Mod163Factor1b6r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b6q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r5 (integerCoefficientEval X h252Fiber7Mod163Factor1b6r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b6r10Coeffs) 162 h252Fiber7Mod163Factor1Binary6Step9 hs
theorem h252Fiber7Mod163Factor1Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r5^163-h252Fiber7Mod163Factor1r6 := by
  have he : h252Fiber7Mod163Factor1b6r10Coeffs = h252Fiber7Mod163Factor1r6Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r6] using h252Fiber7Mod163Factor1Binary6Step10
theorem h252Fiber7Mod163Factor1Frob6 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 6-h252Fiber7Mod163Factor1r6 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob5 h252Fiber7Mod163Factor1Step6
theorem h252Fiber7Mod163Factor1Binary7Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^1-h252Fiber7Mod163Factor1r6 := by simp
theorem h252Fiber7Mod163Factor1Binary7Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r6Coeffs h252Fiber7Mod163Factor1r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r6)*(h252Fiber7Mod163Factor1r6)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r6)*(h252Fiber7Mod163Factor1r6)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (h252Fiber7Mod163Factor1r6) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs) 1 h252Fiber7Mod163Factor1Binary7Step0 hs
theorem h252Fiber7Mod163Factor1Binary7Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r1Coeffs h252Fiber7Mod163Factor1b7r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r2Coeffs) 2 h252Fiber7Mod163Factor1Binary7Step1 hs
theorem h252Fiber7Mod163Factor1Binary7Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r2Coeffs h252Fiber7Mod163Factor1r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r2Coeffs)*(h252Fiber7Mod163Factor1r6)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r2Coeffs)*(h252Fiber7Mod163Factor1r6)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs) 4 h252Fiber7Mod163Factor1Binary7Step2 hs
theorem h252Fiber7Mod163Factor1Binary7Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r3Coeffs h252Fiber7Mod163Factor1b7r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs) 5 h252Fiber7Mod163Factor1Binary7Step3 hs
theorem h252Fiber7Mod163Factor1Binary7Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r4Coeffs h252Fiber7Mod163Factor1b7r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs) 10 h252Fiber7Mod163Factor1Binary7Step4 hs
theorem h252Fiber7Mod163Factor1Binary7Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r5Coeffs h252Fiber7Mod163Factor1b7r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs) 20 h252Fiber7Mod163Factor1Binary7Step5 hs
theorem h252Fiber7Mod163Factor1Binary7Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r6Coeffs h252Fiber7Mod163Factor1b7r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r7Coeffs) 40 h252Fiber7Mod163Factor1Binary7Step6 hs
theorem h252Fiber7Mod163Factor1Binary7Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r7Coeffs h252Fiber7Mod163Factor1r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r7Coeffs)*(h252Fiber7Mod163Factor1r6)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r7Coeffs)*(h252Fiber7Mod163Factor1r6)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs) 80 h252Fiber7Mod163Factor1Binary7Step7 hs
theorem h252Fiber7Mod163Factor1Binary7Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r8Coeffs h252Fiber7Mod163Factor1b7r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r9Coeffs) 81 h252Fiber7Mod163Factor1Binary7Step8 hs
theorem h252Fiber7Mod163Factor1Binary7Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b7r9Coeffs h252Fiber7Mod163Factor1r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b7r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b7q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b7r9Coeffs)*(h252Fiber7Mod163Factor1r6)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b7q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r6] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b7r9Coeffs)*(h252Fiber7Mod163Factor1r6)-(integerCoefficientEval X h252Fiber7Mod163Factor1b7r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b7q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r6 (integerCoefficientEval X h252Fiber7Mod163Factor1b7r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b7r10Coeffs) 162 h252Fiber7Mod163Factor1Binary7Step9 hs
theorem h252Fiber7Mod163Factor1Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r6^163-h252Fiber7Mod163Factor1r7 := by
  have he : h252Fiber7Mod163Factor1b7r10Coeffs = h252Fiber7Mod163Factor1r7Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r7] using h252Fiber7Mod163Factor1Binary7Step10
theorem h252Fiber7Mod163Factor1Frob7 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 7-h252Fiber7Mod163Factor1r7 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob6 h252Fiber7Mod163Factor1Step7
theorem h252Fiber7Mod163Factor1Binary8Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^1-h252Fiber7Mod163Factor1r7 := by simp
theorem h252Fiber7Mod163Factor1Binary8Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r7Coeffs h252Fiber7Mod163Factor1r7Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r7)*(h252Fiber7Mod163Factor1r7)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r7)*(h252Fiber7Mod163Factor1r7)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (h252Fiber7Mod163Factor1r7) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs) 1 h252Fiber7Mod163Factor1Binary8Step0 hs
theorem h252Fiber7Mod163Factor1Binary8Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r1Coeffs h252Fiber7Mod163Factor1b8r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r2Coeffs) 2 h252Fiber7Mod163Factor1Binary8Step1 hs
theorem h252Fiber7Mod163Factor1Binary8Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r2Coeffs h252Fiber7Mod163Factor1r7Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r2Coeffs)*(h252Fiber7Mod163Factor1r7)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r2Coeffs)*(h252Fiber7Mod163Factor1r7)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs) 4 h252Fiber7Mod163Factor1Binary8Step2 hs
theorem h252Fiber7Mod163Factor1Binary8Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r3Coeffs h252Fiber7Mod163Factor1b8r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs) 5 h252Fiber7Mod163Factor1Binary8Step3 hs
theorem h252Fiber7Mod163Factor1Binary8Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r4Coeffs h252Fiber7Mod163Factor1b8r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs) 10 h252Fiber7Mod163Factor1Binary8Step4 hs
theorem h252Fiber7Mod163Factor1Binary8Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r5Coeffs h252Fiber7Mod163Factor1b8r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs) 20 h252Fiber7Mod163Factor1Binary8Step5 hs
theorem h252Fiber7Mod163Factor1Binary8Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r6Coeffs h252Fiber7Mod163Factor1b8r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r7Coeffs) 40 h252Fiber7Mod163Factor1Binary8Step6 hs
theorem h252Fiber7Mod163Factor1Binary8Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r7Coeffs h252Fiber7Mod163Factor1r7Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r7Coeffs)*(h252Fiber7Mod163Factor1r7)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r7Coeffs)*(h252Fiber7Mod163Factor1r7)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs) 80 h252Fiber7Mod163Factor1Binary8Step7 hs
theorem h252Fiber7Mod163Factor1Binary8Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r8Coeffs h252Fiber7Mod163Factor1b8r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r9Coeffs) 81 h252Fiber7Mod163Factor1Binary8Step8 hs
theorem h252Fiber7Mod163Factor1Binary8Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b8r9Coeffs h252Fiber7Mod163Factor1r7Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b8r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b8q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b8r9Coeffs)*(h252Fiber7Mod163Factor1r7)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b8q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r7] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b8r9Coeffs)*(h252Fiber7Mod163Factor1r7)-(integerCoefficientEval X h252Fiber7Mod163Factor1b8r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b8q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r7 (integerCoefficientEval X h252Fiber7Mod163Factor1b8r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b8r10Coeffs) 162 h252Fiber7Mod163Factor1Binary8Step9 hs
theorem h252Fiber7Mod163Factor1Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r7^163-h252Fiber7Mod163Factor1r8 := by
  have he : h252Fiber7Mod163Factor1b8r10Coeffs = h252Fiber7Mod163Factor1r8Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r8] using h252Fiber7Mod163Factor1Binary8Step10
theorem h252Fiber7Mod163Factor1Frob8 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 8-h252Fiber7Mod163Factor1r8 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob7 h252Fiber7Mod163Factor1Step8
theorem h252Fiber7Mod163Factor1Binary9Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^1-h252Fiber7Mod163Factor1r8 := by simp
theorem h252Fiber7Mod163Factor1Binary9Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r8Coeffs h252Fiber7Mod163Factor1r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r8)*(h252Fiber7Mod163Factor1r8)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r8)*(h252Fiber7Mod163Factor1r8)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (h252Fiber7Mod163Factor1r8) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs) 1 h252Fiber7Mod163Factor1Binary9Step0 hs
theorem h252Fiber7Mod163Factor1Binary9Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r1Coeffs h252Fiber7Mod163Factor1b9r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r2Coeffs) 2 h252Fiber7Mod163Factor1Binary9Step1 hs
theorem h252Fiber7Mod163Factor1Binary9Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r2Coeffs h252Fiber7Mod163Factor1r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r2Coeffs)*(h252Fiber7Mod163Factor1r8)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r2Coeffs)*(h252Fiber7Mod163Factor1r8)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs) 4 h252Fiber7Mod163Factor1Binary9Step2 hs
theorem h252Fiber7Mod163Factor1Binary9Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r3Coeffs h252Fiber7Mod163Factor1b9r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs) 5 h252Fiber7Mod163Factor1Binary9Step3 hs
theorem h252Fiber7Mod163Factor1Binary9Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r4Coeffs h252Fiber7Mod163Factor1b9r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs) 10 h252Fiber7Mod163Factor1Binary9Step4 hs
theorem h252Fiber7Mod163Factor1Binary9Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r5Coeffs h252Fiber7Mod163Factor1b9r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs) 20 h252Fiber7Mod163Factor1Binary9Step5 hs
theorem h252Fiber7Mod163Factor1Binary9Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r6Coeffs h252Fiber7Mod163Factor1b9r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r7Coeffs) 40 h252Fiber7Mod163Factor1Binary9Step6 hs
theorem h252Fiber7Mod163Factor1Binary9Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r7Coeffs h252Fiber7Mod163Factor1r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r7Coeffs)*(h252Fiber7Mod163Factor1r8)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r7Coeffs)*(h252Fiber7Mod163Factor1r8)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs) 80 h252Fiber7Mod163Factor1Binary9Step7 hs
theorem h252Fiber7Mod163Factor1Binary9Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r8Coeffs h252Fiber7Mod163Factor1b9r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r9Coeffs) 81 h252Fiber7Mod163Factor1Binary9Step8 hs
theorem h252Fiber7Mod163Factor1Binary9Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b9r9Coeffs h252Fiber7Mod163Factor1r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b9r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b9q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b9r9Coeffs)*(h252Fiber7Mod163Factor1r8)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b9q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b9r9Coeffs)*(h252Fiber7Mod163Factor1r8)-(integerCoefficientEval X h252Fiber7Mod163Factor1b9r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b9q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r8 (integerCoefficientEval X h252Fiber7Mod163Factor1b9r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b9r10Coeffs) 162 h252Fiber7Mod163Factor1Binary9Step9 hs
theorem h252Fiber7Mod163Factor1Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r8^163-h252Fiber7Mod163Factor1r9 := by
  have he : h252Fiber7Mod163Factor1b9r10Coeffs = h252Fiber7Mod163Factor1r9Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r9] using h252Fiber7Mod163Factor1Binary9Step10
theorem h252Fiber7Mod163Factor1Frob9 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 9-h252Fiber7Mod163Factor1r9 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob8 h252Fiber7Mod163Factor1Step9
theorem h252Fiber7Mod163Factor1Binary10Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^1-h252Fiber7Mod163Factor1r9 := by simp
theorem h252Fiber7Mod163Factor1Binary10Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r9Coeffs h252Fiber7Mod163Factor1r9Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r9)*(h252Fiber7Mod163Factor1r9)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r9)*(h252Fiber7Mod163Factor1r9)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (h252Fiber7Mod163Factor1r9) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs) 1 h252Fiber7Mod163Factor1Binary10Step0 hs
theorem h252Fiber7Mod163Factor1Binary10Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r1Coeffs h252Fiber7Mod163Factor1b10r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r2Coeffs) 2 h252Fiber7Mod163Factor1Binary10Step1 hs
theorem h252Fiber7Mod163Factor1Binary10Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r2Coeffs h252Fiber7Mod163Factor1r9Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r2Coeffs)*(h252Fiber7Mod163Factor1r9)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r2Coeffs)*(h252Fiber7Mod163Factor1r9)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs) 4 h252Fiber7Mod163Factor1Binary10Step2 hs
theorem h252Fiber7Mod163Factor1Binary10Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r3Coeffs h252Fiber7Mod163Factor1b10r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs) 5 h252Fiber7Mod163Factor1Binary10Step3 hs
theorem h252Fiber7Mod163Factor1Binary10Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r4Coeffs h252Fiber7Mod163Factor1b10r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs) 10 h252Fiber7Mod163Factor1Binary10Step4 hs
theorem h252Fiber7Mod163Factor1Binary10Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r5Coeffs h252Fiber7Mod163Factor1b10r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs) 20 h252Fiber7Mod163Factor1Binary10Step5 hs
theorem h252Fiber7Mod163Factor1Binary10Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r6Coeffs h252Fiber7Mod163Factor1b10r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r7Coeffs) 40 h252Fiber7Mod163Factor1Binary10Step6 hs
theorem h252Fiber7Mod163Factor1Binary10Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r7Coeffs h252Fiber7Mod163Factor1r9Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r7Coeffs)*(h252Fiber7Mod163Factor1r9)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r7Coeffs)*(h252Fiber7Mod163Factor1r9)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs) 80 h252Fiber7Mod163Factor1Binary10Step7 hs
theorem h252Fiber7Mod163Factor1Binary10Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r8Coeffs h252Fiber7Mod163Factor1b10r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r9Coeffs) 81 h252Fiber7Mod163Factor1Binary10Step8 hs
theorem h252Fiber7Mod163Factor1Binary10Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b10r9Coeffs h252Fiber7Mod163Factor1r9Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b10r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b10q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b10r9Coeffs)*(h252Fiber7Mod163Factor1r9)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b10q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r9] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b10r9Coeffs)*(h252Fiber7Mod163Factor1r9)-(integerCoefficientEval X h252Fiber7Mod163Factor1b10r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b10q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r9 (integerCoefficientEval X h252Fiber7Mod163Factor1b10r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b10r10Coeffs) 162 h252Fiber7Mod163Factor1Binary10Step9 hs
theorem h252Fiber7Mod163Factor1Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r9^163-h252Fiber7Mod163Factor1r10 := by
  have he : h252Fiber7Mod163Factor1b10r10Coeffs = h252Fiber7Mod163Factor1r10Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r10] using h252Fiber7Mod163Factor1Binary10Step10
theorem h252Fiber7Mod163Factor1Frob10 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 10-h252Fiber7Mod163Factor1r10 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob9 h252Fiber7Mod163Factor1Step10
end
end Biunimodular.F11
