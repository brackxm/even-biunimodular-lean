/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor1Frobenius2

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor1Binary11Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^1-h252Fiber7Mod163Factor1r10 := by simp
theorem h252Fiber7Mod163Factor1Binary11Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r10Coeffs h252Fiber7Mod163Factor1r10Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r10)*(h252Fiber7Mod163Factor1r10)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r10)*(h252Fiber7Mod163Factor1r10)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (h252Fiber7Mod163Factor1r10) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs) 1 h252Fiber7Mod163Factor1Binary11Step0 hs
theorem h252Fiber7Mod163Factor1Binary11Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r1Coeffs h252Fiber7Mod163Factor1b11r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r2Coeffs) 2 h252Fiber7Mod163Factor1Binary11Step1 hs
theorem h252Fiber7Mod163Factor1Binary11Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r2Coeffs h252Fiber7Mod163Factor1r10Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r2Coeffs)*(h252Fiber7Mod163Factor1r10)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r2Coeffs)*(h252Fiber7Mod163Factor1r10)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs) 4 h252Fiber7Mod163Factor1Binary11Step2 hs
theorem h252Fiber7Mod163Factor1Binary11Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r3Coeffs h252Fiber7Mod163Factor1b11r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs) 5 h252Fiber7Mod163Factor1Binary11Step3 hs
theorem h252Fiber7Mod163Factor1Binary11Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r4Coeffs h252Fiber7Mod163Factor1b11r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs) 10 h252Fiber7Mod163Factor1Binary11Step4 hs
theorem h252Fiber7Mod163Factor1Binary11Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r5Coeffs h252Fiber7Mod163Factor1b11r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs) 20 h252Fiber7Mod163Factor1Binary11Step5 hs
theorem h252Fiber7Mod163Factor1Binary11Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r6Coeffs h252Fiber7Mod163Factor1b11r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r7Coeffs) 40 h252Fiber7Mod163Factor1Binary11Step6 hs
theorem h252Fiber7Mod163Factor1Binary11Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r7Coeffs h252Fiber7Mod163Factor1r10Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r7Coeffs)*(h252Fiber7Mod163Factor1r10)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r7Coeffs)*(h252Fiber7Mod163Factor1r10)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs) 80 h252Fiber7Mod163Factor1Binary11Step7 hs
theorem h252Fiber7Mod163Factor1Binary11Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r8Coeffs h252Fiber7Mod163Factor1b11r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r9Coeffs) 81 h252Fiber7Mod163Factor1Binary11Step8 hs
theorem h252Fiber7Mod163Factor1Binary11Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b11r9Coeffs h252Fiber7Mod163Factor1r10Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b11r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b11q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b11r9Coeffs)*(h252Fiber7Mod163Factor1r10)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b11q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b11r9Coeffs)*(h252Fiber7Mod163Factor1r10)-(integerCoefficientEval X h252Fiber7Mod163Factor1b11r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b11q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r10 (integerCoefficientEval X h252Fiber7Mod163Factor1b11r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b11r10Coeffs) 162 h252Fiber7Mod163Factor1Binary11Step9 hs
theorem h252Fiber7Mod163Factor1Step11 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r10^163-h252Fiber7Mod163Factor1r11 := by
  have he : h252Fiber7Mod163Factor1b11r10Coeffs = h252Fiber7Mod163Factor1r11Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r11] using h252Fiber7Mod163Factor1Binary11Step10
theorem h252Fiber7Mod163Factor1Frob11 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 11-h252Fiber7Mod163Factor1r11 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob10 h252Fiber7Mod163Factor1Step11
theorem h252Fiber7Mod163Factor1Binary12Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^1-h252Fiber7Mod163Factor1r11 := by simp
theorem h252Fiber7Mod163Factor1Binary12Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r11Coeffs h252Fiber7Mod163Factor1r11Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r11)*(h252Fiber7Mod163Factor1r11)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r11)*(h252Fiber7Mod163Factor1r11)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (h252Fiber7Mod163Factor1r11) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs) 1 h252Fiber7Mod163Factor1Binary12Step0 hs
theorem h252Fiber7Mod163Factor1Binary12Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r1Coeffs h252Fiber7Mod163Factor1b12r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r2Coeffs) 2 h252Fiber7Mod163Factor1Binary12Step1 hs
theorem h252Fiber7Mod163Factor1Binary12Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r2Coeffs h252Fiber7Mod163Factor1r11Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r2Coeffs)*(h252Fiber7Mod163Factor1r11)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r2Coeffs)*(h252Fiber7Mod163Factor1r11)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs) 4 h252Fiber7Mod163Factor1Binary12Step2 hs
theorem h252Fiber7Mod163Factor1Binary12Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r3Coeffs h252Fiber7Mod163Factor1b12r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs) 5 h252Fiber7Mod163Factor1Binary12Step3 hs
theorem h252Fiber7Mod163Factor1Binary12Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r4Coeffs h252Fiber7Mod163Factor1b12r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs) 10 h252Fiber7Mod163Factor1Binary12Step4 hs
theorem h252Fiber7Mod163Factor1Binary12Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r5Coeffs h252Fiber7Mod163Factor1b12r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs) 20 h252Fiber7Mod163Factor1Binary12Step5 hs
theorem h252Fiber7Mod163Factor1Binary12Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r6Coeffs h252Fiber7Mod163Factor1b12r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r7Coeffs) 40 h252Fiber7Mod163Factor1Binary12Step6 hs
theorem h252Fiber7Mod163Factor1Binary12Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r7Coeffs h252Fiber7Mod163Factor1r11Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r7Coeffs)*(h252Fiber7Mod163Factor1r11)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r7Coeffs)*(h252Fiber7Mod163Factor1r11)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs) 80 h252Fiber7Mod163Factor1Binary12Step7 hs
theorem h252Fiber7Mod163Factor1Binary12Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r8Coeffs h252Fiber7Mod163Factor1b12r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r9Coeffs) 81 h252Fiber7Mod163Factor1Binary12Step8 hs
theorem h252Fiber7Mod163Factor1Binary12Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b12r9Coeffs h252Fiber7Mod163Factor1r11Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b12r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b12q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b12r9Coeffs)*(h252Fiber7Mod163Factor1r11)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b12q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r11] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b12r9Coeffs)*(h252Fiber7Mod163Factor1r11)-(integerCoefficientEval X h252Fiber7Mod163Factor1b12r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b12q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r11 (integerCoefficientEval X h252Fiber7Mod163Factor1b12r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b12r10Coeffs) 162 h252Fiber7Mod163Factor1Binary12Step9 hs
theorem h252Fiber7Mod163Factor1Step12 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r11^163-h252Fiber7Mod163Factor1r12 := by
  have he : h252Fiber7Mod163Factor1b12r10Coeffs = h252Fiber7Mod163Factor1r12Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r12] using h252Fiber7Mod163Factor1Binary12Step10
theorem h252Fiber7Mod163Factor1Frob12 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 12-h252Fiber7Mod163Factor1r12 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob11 h252Fiber7Mod163Factor1Step12
theorem h252Fiber7Mod163Factor1Binary13Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^1-h252Fiber7Mod163Factor1r12 := by simp
theorem h252Fiber7Mod163Factor1Binary13Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r12Coeffs h252Fiber7Mod163Factor1r12Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r12)*(h252Fiber7Mod163Factor1r12)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r12)*(h252Fiber7Mod163Factor1r12)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (h252Fiber7Mod163Factor1r12) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs) 1 h252Fiber7Mod163Factor1Binary13Step0 hs
theorem h252Fiber7Mod163Factor1Binary13Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r1Coeffs h252Fiber7Mod163Factor1b13r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r2Coeffs) 2 h252Fiber7Mod163Factor1Binary13Step1 hs
theorem h252Fiber7Mod163Factor1Binary13Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r2Coeffs h252Fiber7Mod163Factor1r12Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r2Coeffs)*(h252Fiber7Mod163Factor1r12)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r2Coeffs)*(h252Fiber7Mod163Factor1r12)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs) 4 h252Fiber7Mod163Factor1Binary13Step2 hs
theorem h252Fiber7Mod163Factor1Binary13Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r3Coeffs h252Fiber7Mod163Factor1b13r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs) 5 h252Fiber7Mod163Factor1Binary13Step3 hs
theorem h252Fiber7Mod163Factor1Binary13Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r4Coeffs h252Fiber7Mod163Factor1b13r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs) 10 h252Fiber7Mod163Factor1Binary13Step4 hs
theorem h252Fiber7Mod163Factor1Binary13Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r5Coeffs h252Fiber7Mod163Factor1b13r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs) 20 h252Fiber7Mod163Factor1Binary13Step5 hs
theorem h252Fiber7Mod163Factor1Binary13Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r6Coeffs h252Fiber7Mod163Factor1b13r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r7Coeffs) 40 h252Fiber7Mod163Factor1Binary13Step6 hs
theorem h252Fiber7Mod163Factor1Binary13Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r7Coeffs h252Fiber7Mod163Factor1r12Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r7Coeffs)*(h252Fiber7Mod163Factor1r12)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r7Coeffs)*(h252Fiber7Mod163Factor1r12)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs) 80 h252Fiber7Mod163Factor1Binary13Step7 hs
theorem h252Fiber7Mod163Factor1Binary13Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r8Coeffs h252Fiber7Mod163Factor1b13r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r9Coeffs) 81 h252Fiber7Mod163Factor1Binary13Step8 hs
theorem h252Fiber7Mod163Factor1Binary13Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b13r9Coeffs h252Fiber7Mod163Factor1r12Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b13r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b13q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b13r9Coeffs)*(h252Fiber7Mod163Factor1r12)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b13q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r12] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b13r9Coeffs)*(h252Fiber7Mod163Factor1r12)-(integerCoefficientEval X h252Fiber7Mod163Factor1b13r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b13q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r12 (integerCoefficientEval X h252Fiber7Mod163Factor1b13r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b13r10Coeffs) 162 h252Fiber7Mod163Factor1Binary13Step9 hs
theorem h252Fiber7Mod163Factor1Step13 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r12^163-h252Fiber7Mod163Factor1r13 := by
  have he : h252Fiber7Mod163Factor1b13r10Coeffs = h252Fiber7Mod163Factor1r13Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r13] using h252Fiber7Mod163Factor1Binary13Step10
theorem h252Fiber7Mod163Factor1Frob13 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 13-h252Fiber7Mod163Factor1r13 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob12 h252Fiber7Mod163Factor1Step13
theorem h252Fiber7Mod163Factor1Binary14Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^1-h252Fiber7Mod163Factor1r13 := by simp
theorem h252Fiber7Mod163Factor1Binary14Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r13Coeffs h252Fiber7Mod163Factor1r13Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r13)*(h252Fiber7Mod163Factor1r13)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r13)*(h252Fiber7Mod163Factor1r13)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (h252Fiber7Mod163Factor1r13) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs) 1 h252Fiber7Mod163Factor1Binary14Step0 hs
theorem h252Fiber7Mod163Factor1Binary14Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r1Coeffs h252Fiber7Mod163Factor1b14r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r2Coeffs) 2 h252Fiber7Mod163Factor1Binary14Step1 hs
theorem h252Fiber7Mod163Factor1Binary14Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r2Coeffs h252Fiber7Mod163Factor1r13Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r2Coeffs)*(h252Fiber7Mod163Factor1r13)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r2Coeffs)*(h252Fiber7Mod163Factor1r13)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs) 4 h252Fiber7Mod163Factor1Binary14Step2 hs
theorem h252Fiber7Mod163Factor1Binary14Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r3Coeffs h252Fiber7Mod163Factor1b14r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs) 5 h252Fiber7Mod163Factor1Binary14Step3 hs
theorem h252Fiber7Mod163Factor1Binary14Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r4Coeffs h252Fiber7Mod163Factor1b14r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs) 10 h252Fiber7Mod163Factor1Binary14Step4 hs
theorem h252Fiber7Mod163Factor1Binary14Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r5Coeffs h252Fiber7Mod163Factor1b14r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs) 20 h252Fiber7Mod163Factor1Binary14Step5 hs
theorem h252Fiber7Mod163Factor1Binary14Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r6Coeffs h252Fiber7Mod163Factor1b14r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r7Coeffs) 40 h252Fiber7Mod163Factor1Binary14Step6 hs
theorem h252Fiber7Mod163Factor1Binary14Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r7Coeffs h252Fiber7Mod163Factor1r13Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r7Coeffs)*(h252Fiber7Mod163Factor1r13)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r7Coeffs)*(h252Fiber7Mod163Factor1r13)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs) 80 h252Fiber7Mod163Factor1Binary14Step7 hs
theorem h252Fiber7Mod163Factor1Binary14Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r8Coeffs h252Fiber7Mod163Factor1b14r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r9Coeffs) 81 h252Fiber7Mod163Factor1Binary14Step8 hs
theorem h252Fiber7Mod163Factor1Binary14Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b14r9Coeffs h252Fiber7Mod163Factor1r13Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b14r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b14q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b14r9Coeffs)*(h252Fiber7Mod163Factor1r13)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b14q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r13] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b14r9Coeffs)*(h252Fiber7Mod163Factor1r13)-(integerCoefficientEval X h252Fiber7Mod163Factor1b14r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b14q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r13 (integerCoefficientEval X h252Fiber7Mod163Factor1b14r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b14r10Coeffs) 162 h252Fiber7Mod163Factor1Binary14Step9 hs
theorem h252Fiber7Mod163Factor1Step14 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r13^163-h252Fiber7Mod163Factor1r14 := by
  have he : h252Fiber7Mod163Factor1b14r10Coeffs = h252Fiber7Mod163Factor1r14Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r14] using h252Fiber7Mod163Factor1Binary14Step10
theorem h252Fiber7Mod163Factor1Frob14 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 14-h252Fiber7Mod163Factor1r14 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob13 h252Fiber7Mod163Factor1Step14
theorem h252Fiber7Mod163Factor1Binary15Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^1-h252Fiber7Mod163Factor1r14 := by simp
theorem h252Fiber7Mod163Factor1Binary15Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r14Coeffs h252Fiber7Mod163Factor1r14Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r14)*(h252Fiber7Mod163Factor1r14)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r14)*(h252Fiber7Mod163Factor1r14)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (h252Fiber7Mod163Factor1r14) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs) 1 h252Fiber7Mod163Factor1Binary15Step0 hs
theorem h252Fiber7Mod163Factor1Binary15Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r1Coeffs h252Fiber7Mod163Factor1b15r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r2Coeffs) 2 h252Fiber7Mod163Factor1Binary15Step1 hs
theorem h252Fiber7Mod163Factor1Binary15Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r2Coeffs h252Fiber7Mod163Factor1r14Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r2Coeffs)*(h252Fiber7Mod163Factor1r14)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r2Coeffs)*(h252Fiber7Mod163Factor1r14)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs) 4 h252Fiber7Mod163Factor1Binary15Step2 hs
theorem h252Fiber7Mod163Factor1Binary15Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r3Coeffs h252Fiber7Mod163Factor1b15r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs) 5 h252Fiber7Mod163Factor1Binary15Step3 hs
theorem h252Fiber7Mod163Factor1Binary15Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r4Coeffs h252Fiber7Mod163Factor1b15r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs) 10 h252Fiber7Mod163Factor1Binary15Step4 hs
theorem h252Fiber7Mod163Factor1Binary15Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r5Coeffs h252Fiber7Mod163Factor1b15r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs) 20 h252Fiber7Mod163Factor1Binary15Step5 hs
theorem h252Fiber7Mod163Factor1Binary15Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r6Coeffs h252Fiber7Mod163Factor1b15r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r7Coeffs) 40 h252Fiber7Mod163Factor1Binary15Step6 hs
theorem h252Fiber7Mod163Factor1Binary15Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r7Coeffs h252Fiber7Mod163Factor1r14Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r7Coeffs)*(h252Fiber7Mod163Factor1r14)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r7Coeffs)*(h252Fiber7Mod163Factor1r14)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs) 80 h252Fiber7Mod163Factor1Binary15Step7 hs
theorem h252Fiber7Mod163Factor1Binary15Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r8Coeffs h252Fiber7Mod163Factor1b15r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r9Coeffs) 81 h252Fiber7Mod163Factor1Binary15Step8 hs
theorem h252Fiber7Mod163Factor1Binary15Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b15r9Coeffs h252Fiber7Mod163Factor1r14Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b15r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b15q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b15r9Coeffs)*(h252Fiber7Mod163Factor1r14)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b15q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r14] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b15r9Coeffs)*(h252Fiber7Mod163Factor1r14)-(integerCoefficientEval X h252Fiber7Mod163Factor1b15r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b15q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r14 (integerCoefficientEval X h252Fiber7Mod163Factor1b15r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b15r10Coeffs) 162 h252Fiber7Mod163Factor1Binary15Step9 hs
theorem h252Fiber7Mod163Factor1Step15 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r14^163-h252Fiber7Mod163Factor1r15 := by
  have he : h252Fiber7Mod163Factor1b15r10Coeffs = h252Fiber7Mod163Factor1r15Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r15] using h252Fiber7Mod163Factor1Binary15Step10
theorem h252Fiber7Mod163Factor1Frob15 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 15-h252Fiber7Mod163Factor1r15 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob14 h252Fiber7Mod163Factor1Step15
end
end Biunimodular.F11
