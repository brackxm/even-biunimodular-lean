/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor1Frobenius7

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor1Binary36Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^1-h252Fiber7Mod163Factor1r35 := by simp
theorem h252Fiber7Mod163Factor1Binary36Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r35Coeffs h252Fiber7Mod163Factor1r35Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r35)*(h252Fiber7Mod163Factor1r35)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r35)*(h252Fiber7Mod163Factor1r35)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (h252Fiber7Mod163Factor1r35) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs) 1 h252Fiber7Mod163Factor1Binary36Step0 hs
theorem h252Fiber7Mod163Factor1Binary36Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r1Coeffs h252Fiber7Mod163Factor1b36r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r2Coeffs) 2 h252Fiber7Mod163Factor1Binary36Step1 hs
theorem h252Fiber7Mod163Factor1Binary36Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r2Coeffs h252Fiber7Mod163Factor1r35Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r2Coeffs)*(h252Fiber7Mod163Factor1r35)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r2Coeffs)*(h252Fiber7Mod163Factor1r35)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs) 4 h252Fiber7Mod163Factor1Binary36Step2 hs
theorem h252Fiber7Mod163Factor1Binary36Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r3Coeffs h252Fiber7Mod163Factor1b36r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs) 5 h252Fiber7Mod163Factor1Binary36Step3 hs
theorem h252Fiber7Mod163Factor1Binary36Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r4Coeffs h252Fiber7Mod163Factor1b36r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs) 10 h252Fiber7Mod163Factor1Binary36Step4 hs
theorem h252Fiber7Mod163Factor1Binary36Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r5Coeffs h252Fiber7Mod163Factor1b36r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs) 20 h252Fiber7Mod163Factor1Binary36Step5 hs
theorem h252Fiber7Mod163Factor1Binary36Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r6Coeffs h252Fiber7Mod163Factor1b36r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r7Coeffs) 40 h252Fiber7Mod163Factor1Binary36Step6 hs
theorem h252Fiber7Mod163Factor1Binary36Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r7Coeffs h252Fiber7Mod163Factor1r35Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r7Coeffs)*(h252Fiber7Mod163Factor1r35)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r7Coeffs)*(h252Fiber7Mod163Factor1r35)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs) 80 h252Fiber7Mod163Factor1Binary36Step7 hs
theorem h252Fiber7Mod163Factor1Binary36Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r8Coeffs h252Fiber7Mod163Factor1b36r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r9Coeffs) 81 h252Fiber7Mod163Factor1Binary36Step8 hs
theorem h252Fiber7Mod163Factor1Binary36Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b36r9Coeffs h252Fiber7Mod163Factor1r35Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b36r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b36q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b36r9Coeffs)*(h252Fiber7Mod163Factor1r35)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b36q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r35] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b36r9Coeffs)*(h252Fiber7Mod163Factor1r35)-(integerCoefficientEval X h252Fiber7Mod163Factor1b36r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b36q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r35 (integerCoefficientEval X h252Fiber7Mod163Factor1b36r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b36r10Coeffs) 162 h252Fiber7Mod163Factor1Binary36Step9 hs
theorem h252Fiber7Mod163Factor1Step36 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r35^163-h252Fiber7Mod163Factor1r36 := by
  have he : h252Fiber7Mod163Factor1b36r10Coeffs = h252Fiber7Mod163Factor1r36Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r36] using h252Fiber7Mod163Factor1Binary36Step10
theorem h252Fiber7Mod163Factor1Frob36 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 36-h252Fiber7Mod163Factor1r36 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob35 h252Fiber7Mod163Factor1Step36
theorem h252Fiber7Mod163Factor1Binary37Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^1-h252Fiber7Mod163Factor1r36 := by simp
theorem h252Fiber7Mod163Factor1Binary37Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r36Coeffs h252Fiber7Mod163Factor1r36Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r36)*(h252Fiber7Mod163Factor1r36)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r36)*(h252Fiber7Mod163Factor1r36)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (h252Fiber7Mod163Factor1r36) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs) 1 h252Fiber7Mod163Factor1Binary37Step0 hs
theorem h252Fiber7Mod163Factor1Binary37Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r1Coeffs h252Fiber7Mod163Factor1b37r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r2Coeffs) 2 h252Fiber7Mod163Factor1Binary37Step1 hs
theorem h252Fiber7Mod163Factor1Binary37Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r2Coeffs h252Fiber7Mod163Factor1r36Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r2Coeffs)*(h252Fiber7Mod163Factor1r36)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r2Coeffs)*(h252Fiber7Mod163Factor1r36)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs) 4 h252Fiber7Mod163Factor1Binary37Step2 hs
theorem h252Fiber7Mod163Factor1Binary37Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r3Coeffs h252Fiber7Mod163Factor1b37r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs) 5 h252Fiber7Mod163Factor1Binary37Step3 hs
theorem h252Fiber7Mod163Factor1Binary37Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r4Coeffs h252Fiber7Mod163Factor1b37r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs) 10 h252Fiber7Mod163Factor1Binary37Step4 hs
theorem h252Fiber7Mod163Factor1Binary37Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r5Coeffs h252Fiber7Mod163Factor1b37r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs) 20 h252Fiber7Mod163Factor1Binary37Step5 hs
theorem h252Fiber7Mod163Factor1Binary37Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r6Coeffs h252Fiber7Mod163Factor1b37r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r7Coeffs) 40 h252Fiber7Mod163Factor1Binary37Step6 hs
theorem h252Fiber7Mod163Factor1Binary37Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r7Coeffs h252Fiber7Mod163Factor1r36Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r7Coeffs)*(h252Fiber7Mod163Factor1r36)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r7Coeffs)*(h252Fiber7Mod163Factor1r36)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs) 80 h252Fiber7Mod163Factor1Binary37Step7 hs
theorem h252Fiber7Mod163Factor1Binary37Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r8Coeffs h252Fiber7Mod163Factor1b37r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r9Coeffs) 81 h252Fiber7Mod163Factor1Binary37Step8 hs
theorem h252Fiber7Mod163Factor1Binary37Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b37r9Coeffs h252Fiber7Mod163Factor1r36Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b37r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b37q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b37r9Coeffs)*(h252Fiber7Mod163Factor1r36)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b37q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r36] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b37r9Coeffs)*(h252Fiber7Mod163Factor1r36)-(integerCoefficientEval X h252Fiber7Mod163Factor1b37r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b37q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r36 (integerCoefficientEval X h252Fiber7Mod163Factor1b37r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b37r10Coeffs) 162 h252Fiber7Mod163Factor1Binary37Step9 hs
theorem h252Fiber7Mod163Factor1Step37 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r36^163-h252Fiber7Mod163Factor1r37 := by
  have he : h252Fiber7Mod163Factor1b37r10Coeffs = h252Fiber7Mod163Factor1r37Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r37] using h252Fiber7Mod163Factor1Binary37Step10
theorem h252Fiber7Mod163Factor1Frob37 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 37-h252Fiber7Mod163Factor1r37 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob36 h252Fiber7Mod163Factor1Step37
theorem h252Fiber7Mod163Factor1Binary38Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^1-h252Fiber7Mod163Factor1r37 := by simp
theorem h252Fiber7Mod163Factor1Binary38Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r37Coeffs h252Fiber7Mod163Factor1r37Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r37)*(h252Fiber7Mod163Factor1r37)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r37)*(h252Fiber7Mod163Factor1r37)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (h252Fiber7Mod163Factor1r37) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs) 1 h252Fiber7Mod163Factor1Binary38Step0 hs
theorem h252Fiber7Mod163Factor1Binary38Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r1Coeffs h252Fiber7Mod163Factor1b38r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r2Coeffs) 2 h252Fiber7Mod163Factor1Binary38Step1 hs
theorem h252Fiber7Mod163Factor1Binary38Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r2Coeffs h252Fiber7Mod163Factor1r37Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r2Coeffs)*(h252Fiber7Mod163Factor1r37)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r2Coeffs)*(h252Fiber7Mod163Factor1r37)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs) 4 h252Fiber7Mod163Factor1Binary38Step2 hs
theorem h252Fiber7Mod163Factor1Binary38Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r3Coeffs h252Fiber7Mod163Factor1b38r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs) 5 h252Fiber7Mod163Factor1Binary38Step3 hs
theorem h252Fiber7Mod163Factor1Binary38Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r4Coeffs h252Fiber7Mod163Factor1b38r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs) 10 h252Fiber7Mod163Factor1Binary38Step4 hs
theorem h252Fiber7Mod163Factor1Binary38Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r5Coeffs h252Fiber7Mod163Factor1b38r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs) 20 h252Fiber7Mod163Factor1Binary38Step5 hs
theorem h252Fiber7Mod163Factor1Binary38Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r6Coeffs h252Fiber7Mod163Factor1b38r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r7Coeffs) 40 h252Fiber7Mod163Factor1Binary38Step6 hs
theorem h252Fiber7Mod163Factor1Binary38Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r7Coeffs h252Fiber7Mod163Factor1r37Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r7Coeffs)*(h252Fiber7Mod163Factor1r37)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r7Coeffs)*(h252Fiber7Mod163Factor1r37)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs) 80 h252Fiber7Mod163Factor1Binary38Step7 hs
theorem h252Fiber7Mod163Factor1Binary38Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r8Coeffs h252Fiber7Mod163Factor1b38r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r9Coeffs) 81 h252Fiber7Mod163Factor1Binary38Step8 hs
theorem h252Fiber7Mod163Factor1Binary38Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b38r9Coeffs h252Fiber7Mod163Factor1r37Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b38r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b38q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b38r9Coeffs)*(h252Fiber7Mod163Factor1r37)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b38q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r37] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b38r9Coeffs)*(h252Fiber7Mod163Factor1r37)-(integerCoefficientEval X h252Fiber7Mod163Factor1b38r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b38q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r37 (integerCoefficientEval X h252Fiber7Mod163Factor1b38r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b38r10Coeffs) 162 h252Fiber7Mod163Factor1Binary38Step9 hs
theorem h252Fiber7Mod163Factor1Step38 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r37^163-h252Fiber7Mod163Factor1r38 := by
  have he : h252Fiber7Mod163Factor1b38r10Coeffs = h252Fiber7Mod163Factor1r38Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r38] using h252Fiber7Mod163Factor1Binary38Step10
theorem h252Fiber7Mod163Factor1Frob38 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 38-h252Fiber7Mod163Factor1r38 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob37 h252Fiber7Mod163Factor1Step38
theorem h252Fiber7Mod163Factor1Binary39Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^1-h252Fiber7Mod163Factor1r38 := by simp
theorem h252Fiber7Mod163Factor1Binary39Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r38Coeffs h252Fiber7Mod163Factor1r38Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r38)*(h252Fiber7Mod163Factor1r38)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r38)*(h252Fiber7Mod163Factor1r38)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (h252Fiber7Mod163Factor1r38) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs) 1 h252Fiber7Mod163Factor1Binary39Step0 hs
theorem h252Fiber7Mod163Factor1Binary39Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r1Coeffs h252Fiber7Mod163Factor1b39r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r2Coeffs) 2 h252Fiber7Mod163Factor1Binary39Step1 hs
theorem h252Fiber7Mod163Factor1Binary39Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r2Coeffs h252Fiber7Mod163Factor1r38Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r2Coeffs)*(h252Fiber7Mod163Factor1r38)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r2Coeffs)*(h252Fiber7Mod163Factor1r38)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs) 4 h252Fiber7Mod163Factor1Binary39Step2 hs
theorem h252Fiber7Mod163Factor1Binary39Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r3Coeffs h252Fiber7Mod163Factor1b39r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs) 5 h252Fiber7Mod163Factor1Binary39Step3 hs
theorem h252Fiber7Mod163Factor1Binary39Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r4Coeffs h252Fiber7Mod163Factor1b39r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs) 10 h252Fiber7Mod163Factor1Binary39Step4 hs
theorem h252Fiber7Mod163Factor1Binary39Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r5Coeffs h252Fiber7Mod163Factor1b39r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs) 20 h252Fiber7Mod163Factor1Binary39Step5 hs
theorem h252Fiber7Mod163Factor1Binary39Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r6Coeffs h252Fiber7Mod163Factor1b39r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r7Coeffs) 40 h252Fiber7Mod163Factor1Binary39Step6 hs
theorem h252Fiber7Mod163Factor1Binary39Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r7Coeffs h252Fiber7Mod163Factor1r38Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r7Coeffs)*(h252Fiber7Mod163Factor1r38)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r7Coeffs)*(h252Fiber7Mod163Factor1r38)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs) 80 h252Fiber7Mod163Factor1Binary39Step7 hs
theorem h252Fiber7Mod163Factor1Binary39Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r8Coeffs h252Fiber7Mod163Factor1b39r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r9Coeffs) 81 h252Fiber7Mod163Factor1Binary39Step8 hs
theorem h252Fiber7Mod163Factor1Binary39Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b39r9Coeffs h252Fiber7Mod163Factor1r38Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b39r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b39q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b39r9Coeffs)*(h252Fiber7Mod163Factor1r38)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b39q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r38] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b39r9Coeffs)*(h252Fiber7Mod163Factor1r38)-(integerCoefficientEval X h252Fiber7Mod163Factor1b39r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b39q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r38 (integerCoefficientEval X h252Fiber7Mod163Factor1b39r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b39r10Coeffs) 162 h252Fiber7Mod163Factor1Binary39Step9 hs
theorem h252Fiber7Mod163Factor1Step39 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r38^163-h252Fiber7Mod163Factor1r39 := by
  have he : h252Fiber7Mod163Factor1b39r10Coeffs = h252Fiber7Mod163Factor1r39Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r39] using h252Fiber7Mod163Factor1Binary39Step10
theorem h252Fiber7Mod163Factor1Frob39 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 39-h252Fiber7Mod163Factor1r39 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob38 h252Fiber7Mod163Factor1Step39
theorem h252Fiber7Mod163Factor1Binary40Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^1-h252Fiber7Mod163Factor1r39 := by simp
theorem h252Fiber7Mod163Factor1Binary40Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r39Coeffs h252Fiber7Mod163Factor1r39Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r39)*(h252Fiber7Mod163Factor1r39)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r39)*(h252Fiber7Mod163Factor1r39)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (h252Fiber7Mod163Factor1r39) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs) 1 h252Fiber7Mod163Factor1Binary40Step0 hs
theorem h252Fiber7Mod163Factor1Binary40Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r1Coeffs h252Fiber7Mod163Factor1b40r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r2Coeffs) 2 h252Fiber7Mod163Factor1Binary40Step1 hs
theorem h252Fiber7Mod163Factor1Binary40Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r2Coeffs h252Fiber7Mod163Factor1r39Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r2Coeffs)*(h252Fiber7Mod163Factor1r39)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r2Coeffs)*(h252Fiber7Mod163Factor1r39)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs) 4 h252Fiber7Mod163Factor1Binary40Step2 hs
theorem h252Fiber7Mod163Factor1Binary40Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r3Coeffs h252Fiber7Mod163Factor1b40r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs) 5 h252Fiber7Mod163Factor1Binary40Step3 hs
theorem h252Fiber7Mod163Factor1Binary40Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r4Coeffs h252Fiber7Mod163Factor1b40r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs) 10 h252Fiber7Mod163Factor1Binary40Step4 hs
theorem h252Fiber7Mod163Factor1Binary40Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r5Coeffs h252Fiber7Mod163Factor1b40r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs) 20 h252Fiber7Mod163Factor1Binary40Step5 hs
theorem h252Fiber7Mod163Factor1Binary40Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r6Coeffs h252Fiber7Mod163Factor1b40r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r7Coeffs) 40 h252Fiber7Mod163Factor1Binary40Step6 hs
theorem h252Fiber7Mod163Factor1Binary40Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r7Coeffs h252Fiber7Mod163Factor1r39Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r7Coeffs)*(h252Fiber7Mod163Factor1r39)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r7Coeffs)*(h252Fiber7Mod163Factor1r39)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs) 80 h252Fiber7Mod163Factor1Binary40Step7 hs
theorem h252Fiber7Mod163Factor1Binary40Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r8Coeffs h252Fiber7Mod163Factor1b40r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r9Coeffs) 81 h252Fiber7Mod163Factor1Binary40Step8 hs
theorem h252Fiber7Mod163Factor1Binary40Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b40r9Coeffs h252Fiber7Mod163Factor1r39Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b40r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b40q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b40r9Coeffs)*(h252Fiber7Mod163Factor1r39)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b40q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r39] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b40r9Coeffs)*(h252Fiber7Mod163Factor1r39)-(integerCoefficientEval X h252Fiber7Mod163Factor1b40r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b40q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r39 (integerCoefficientEval X h252Fiber7Mod163Factor1b40r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b40r10Coeffs) 162 h252Fiber7Mod163Factor1Binary40Step9 hs
theorem h252Fiber7Mod163Factor1Step40 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r39^163-h252Fiber7Mod163Factor1r40 := by
  have he : h252Fiber7Mod163Factor1b40r10Coeffs = h252Fiber7Mod163Factor1r40Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r40] using h252Fiber7Mod163Factor1Binary40Step10
theorem h252Fiber7Mod163Factor1Frob40 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 40-h252Fiber7Mod163Factor1r40 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob39 h252Fiber7Mod163Factor1Step40
end
end Biunimodular.F11
