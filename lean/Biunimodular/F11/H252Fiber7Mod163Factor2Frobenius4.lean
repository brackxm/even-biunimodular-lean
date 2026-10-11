/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor2Frobenius3

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor2Binary16Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^1-h252Fiber7Mod163Factor2r15 := by simp
theorem h252Fiber7Mod163Factor2Binary16Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r15Coeffs h252Fiber7Mod163Factor2r15Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r15)*(h252Fiber7Mod163Factor2r15)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r15)*(h252Fiber7Mod163Factor2r15)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (h252Fiber7Mod163Factor2r15) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs) 1 h252Fiber7Mod163Factor2Binary16Step0 hs
theorem h252Fiber7Mod163Factor2Binary16Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r1Coeffs h252Fiber7Mod163Factor2b16r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r2Coeffs) 2 h252Fiber7Mod163Factor2Binary16Step1 hs
theorem h252Fiber7Mod163Factor2Binary16Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r2Coeffs h252Fiber7Mod163Factor2r15Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r2Coeffs)*(h252Fiber7Mod163Factor2r15)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r2Coeffs)*(h252Fiber7Mod163Factor2r15)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs) 4 h252Fiber7Mod163Factor2Binary16Step2 hs
theorem h252Fiber7Mod163Factor2Binary16Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r3Coeffs h252Fiber7Mod163Factor2b16r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs) 5 h252Fiber7Mod163Factor2Binary16Step3 hs
theorem h252Fiber7Mod163Factor2Binary16Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r4Coeffs h252Fiber7Mod163Factor2b16r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs) 10 h252Fiber7Mod163Factor2Binary16Step4 hs
theorem h252Fiber7Mod163Factor2Binary16Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r5Coeffs h252Fiber7Mod163Factor2b16r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs) 20 h252Fiber7Mod163Factor2Binary16Step5 hs
theorem h252Fiber7Mod163Factor2Binary16Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r6Coeffs h252Fiber7Mod163Factor2b16r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r7Coeffs) 40 h252Fiber7Mod163Factor2Binary16Step6 hs
theorem h252Fiber7Mod163Factor2Binary16Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r7Coeffs h252Fiber7Mod163Factor2r15Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r7Coeffs)*(h252Fiber7Mod163Factor2r15)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r7Coeffs)*(h252Fiber7Mod163Factor2r15)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs) 80 h252Fiber7Mod163Factor2Binary16Step7 hs
theorem h252Fiber7Mod163Factor2Binary16Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r8Coeffs h252Fiber7Mod163Factor2b16r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r9Coeffs) 81 h252Fiber7Mod163Factor2Binary16Step8 hs
theorem h252Fiber7Mod163Factor2Binary16Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b16r9Coeffs h252Fiber7Mod163Factor2r15Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b16r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b16q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b16r9Coeffs)*(h252Fiber7Mod163Factor2r15)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b16q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r15] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b16r9Coeffs)*(h252Fiber7Mod163Factor2r15)-(integerCoefficientEval X h252Fiber7Mod163Factor2b16r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b16q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r15 (integerCoefficientEval X h252Fiber7Mod163Factor2b16r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b16r10Coeffs) 162 h252Fiber7Mod163Factor2Binary16Step9 hs
theorem h252Fiber7Mod163Factor2Step16 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r15^163-h252Fiber7Mod163Factor2r16 := by
  have he : h252Fiber7Mod163Factor2b16r10Coeffs = h252Fiber7Mod163Factor2r16Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r16] using h252Fiber7Mod163Factor2Binary16Step10
theorem h252Fiber7Mod163Factor2Frob16 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 16-h252Fiber7Mod163Factor2r16 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob15 h252Fiber7Mod163Factor2Step16
theorem h252Fiber7Mod163Factor2Binary17Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^1-h252Fiber7Mod163Factor2r16 := by simp
theorem h252Fiber7Mod163Factor2Binary17Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r16Coeffs h252Fiber7Mod163Factor2r16Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r16)*(h252Fiber7Mod163Factor2r16)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r16)*(h252Fiber7Mod163Factor2r16)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (h252Fiber7Mod163Factor2r16) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs) 1 h252Fiber7Mod163Factor2Binary17Step0 hs
theorem h252Fiber7Mod163Factor2Binary17Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r1Coeffs h252Fiber7Mod163Factor2b17r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r2Coeffs) 2 h252Fiber7Mod163Factor2Binary17Step1 hs
theorem h252Fiber7Mod163Factor2Binary17Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r2Coeffs h252Fiber7Mod163Factor2r16Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r2Coeffs)*(h252Fiber7Mod163Factor2r16)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r2Coeffs)*(h252Fiber7Mod163Factor2r16)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs) 4 h252Fiber7Mod163Factor2Binary17Step2 hs
theorem h252Fiber7Mod163Factor2Binary17Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r3Coeffs h252Fiber7Mod163Factor2b17r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs) 5 h252Fiber7Mod163Factor2Binary17Step3 hs
theorem h252Fiber7Mod163Factor2Binary17Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r4Coeffs h252Fiber7Mod163Factor2b17r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs) 10 h252Fiber7Mod163Factor2Binary17Step4 hs
theorem h252Fiber7Mod163Factor2Binary17Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r5Coeffs h252Fiber7Mod163Factor2b17r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs) 20 h252Fiber7Mod163Factor2Binary17Step5 hs
theorem h252Fiber7Mod163Factor2Binary17Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r6Coeffs h252Fiber7Mod163Factor2b17r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r7Coeffs) 40 h252Fiber7Mod163Factor2Binary17Step6 hs
theorem h252Fiber7Mod163Factor2Binary17Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r7Coeffs h252Fiber7Mod163Factor2r16Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r7Coeffs)*(h252Fiber7Mod163Factor2r16)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r7Coeffs)*(h252Fiber7Mod163Factor2r16)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs) 80 h252Fiber7Mod163Factor2Binary17Step7 hs
theorem h252Fiber7Mod163Factor2Binary17Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r8Coeffs h252Fiber7Mod163Factor2b17r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r9Coeffs) 81 h252Fiber7Mod163Factor2Binary17Step8 hs
theorem h252Fiber7Mod163Factor2Binary17Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b17r9Coeffs h252Fiber7Mod163Factor2r16Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b17r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b17q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b17r9Coeffs)*(h252Fiber7Mod163Factor2r16)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b17q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r16] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b17r9Coeffs)*(h252Fiber7Mod163Factor2r16)-(integerCoefficientEval X h252Fiber7Mod163Factor2b17r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b17q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r16 (integerCoefficientEval X h252Fiber7Mod163Factor2b17r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b17r10Coeffs) 162 h252Fiber7Mod163Factor2Binary17Step9 hs
theorem h252Fiber7Mod163Factor2Step17 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r16^163-h252Fiber7Mod163Factor2r17 := by
  have he : h252Fiber7Mod163Factor2b17r10Coeffs = h252Fiber7Mod163Factor2r17Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r17] using h252Fiber7Mod163Factor2Binary17Step10
theorem h252Fiber7Mod163Factor2Frob17 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 17-h252Fiber7Mod163Factor2r17 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob16 h252Fiber7Mod163Factor2Step17
theorem h252Fiber7Mod163Factor2Binary18Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^1-h252Fiber7Mod163Factor2r17 := by simp
theorem h252Fiber7Mod163Factor2Binary18Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r17Coeffs h252Fiber7Mod163Factor2r17Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r17)*(h252Fiber7Mod163Factor2r17)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r17)*(h252Fiber7Mod163Factor2r17)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (h252Fiber7Mod163Factor2r17) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs) 1 h252Fiber7Mod163Factor2Binary18Step0 hs
theorem h252Fiber7Mod163Factor2Binary18Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r1Coeffs h252Fiber7Mod163Factor2b18r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r2Coeffs) 2 h252Fiber7Mod163Factor2Binary18Step1 hs
theorem h252Fiber7Mod163Factor2Binary18Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r2Coeffs h252Fiber7Mod163Factor2r17Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r2Coeffs)*(h252Fiber7Mod163Factor2r17)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r2Coeffs)*(h252Fiber7Mod163Factor2r17)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs) 4 h252Fiber7Mod163Factor2Binary18Step2 hs
theorem h252Fiber7Mod163Factor2Binary18Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r3Coeffs h252Fiber7Mod163Factor2b18r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs) 5 h252Fiber7Mod163Factor2Binary18Step3 hs
theorem h252Fiber7Mod163Factor2Binary18Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r4Coeffs h252Fiber7Mod163Factor2b18r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs) 10 h252Fiber7Mod163Factor2Binary18Step4 hs
theorem h252Fiber7Mod163Factor2Binary18Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r5Coeffs h252Fiber7Mod163Factor2b18r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs) 20 h252Fiber7Mod163Factor2Binary18Step5 hs
theorem h252Fiber7Mod163Factor2Binary18Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r6Coeffs h252Fiber7Mod163Factor2b18r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r7Coeffs) 40 h252Fiber7Mod163Factor2Binary18Step6 hs
theorem h252Fiber7Mod163Factor2Binary18Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r7Coeffs h252Fiber7Mod163Factor2r17Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r7Coeffs)*(h252Fiber7Mod163Factor2r17)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r7Coeffs)*(h252Fiber7Mod163Factor2r17)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs) 80 h252Fiber7Mod163Factor2Binary18Step7 hs
theorem h252Fiber7Mod163Factor2Binary18Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r8Coeffs h252Fiber7Mod163Factor2b18r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r9Coeffs) 81 h252Fiber7Mod163Factor2Binary18Step8 hs
theorem h252Fiber7Mod163Factor2Binary18Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b18r9Coeffs h252Fiber7Mod163Factor2r17Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b18r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b18q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b18r9Coeffs)*(h252Fiber7Mod163Factor2r17)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b18q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r17] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b18r9Coeffs)*(h252Fiber7Mod163Factor2r17)-(integerCoefficientEval X h252Fiber7Mod163Factor2b18r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b18q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r17 (integerCoefficientEval X h252Fiber7Mod163Factor2b18r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b18r10Coeffs) 162 h252Fiber7Mod163Factor2Binary18Step9 hs
theorem h252Fiber7Mod163Factor2Step18 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r17^163-h252Fiber7Mod163Factor2r18 := by
  have he : h252Fiber7Mod163Factor2b18r10Coeffs = h252Fiber7Mod163Factor2r18Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r18] using h252Fiber7Mod163Factor2Binary18Step10
theorem h252Fiber7Mod163Factor2Frob18 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 18-h252Fiber7Mod163Factor2r18 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob17 h252Fiber7Mod163Factor2Step18
theorem h252Fiber7Mod163Factor2Binary19Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^1-h252Fiber7Mod163Factor2r18 := by simp
theorem h252Fiber7Mod163Factor2Binary19Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r18Coeffs h252Fiber7Mod163Factor2r18Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r18)*(h252Fiber7Mod163Factor2r18)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r18)*(h252Fiber7Mod163Factor2r18)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (h252Fiber7Mod163Factor2r18) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs) 1 h252Fiber7Mod163Factor2Binary19Step0 hs
theorem h252Fiber7Mod163Factor2Binary19Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r1Coeffs h252Fiber7Mod163Factor2b19r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r2Coeffs) 2 h252Fiber7Mod163Factor2Binary19Step1 hs
theorem h252Fiber7Mod163Factor2Binary19Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r2Coeffs h252Fiber7Mod163Factor2r18Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r2Coeffs)*(h252Fiber7Mod163Factor2r18)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r2Coeffs)*(h252Fiber7Mod163Factor2r18)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs) 4 h252Fiber7Mod163Factor2Binary19Step2 hs
theorem h252Fiber7Mod163Factor2Binary19Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r3Coeffs h252Fiber7Mod163Factor2b19r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs) 5 h252Fiber7Mod163Factor2Binary19Step3 hs
theorem h252Fiber7Mod163Factor2Binary19Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r4Coeffs h252Fiber7Mod163Factor2b19r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs) 10 h252Fiber7Mod163Factor2Binary19Step4 hs
theorem h252Fiber7Mod163Factor2Binary19Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r5Coeffs h252Fiber7Mod163Factor2b19r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs) 20 h252Fiber7Mod163Factor2Binary19Step5 hs
theorem h252Fiber7Mod163Factor2Binary19Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r6Coeffs h252Fiber7Mod163Factor2b19r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r7Coeffs) 40 h252Fiber7Mod163Factor2Binary19Step6 hs
theorem h252Fiber7Mod163Factor2Binary19Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r7Coeffs h252Fiber7Mod163Factor2r18Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r7Coeffs)*(h252Fiber7Mod163Factor2r18)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r7Coeffs)*(h252Fiber7Mod163Factor2r18)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs) 80 h252Fiber7Mod163Factor2Binary19Step7 hs
theorem h252Fiber7Mod163Factor2Binary19Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r8Coeffs h252Fiber7Mod163Factor2b19r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r9Coeffs) 81 h252Fiber7Mod163Factor2Binary19Step8 hs
theorem h252Fiber7Mod163Factor2Binary19Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b19r9Coeffs h252Fiber7Mod163Factor2r18Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b19r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b19q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b19r9Coeffs)*(h252Fiber7Mod163Factor2r18)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b19q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r18] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b19r9Coeffs)*(h252Fiber7Mod163Factor2r18)-(integerCoefficientEval X h252Fiber7Mod163Factor2b19r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b19q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r18 (integerCoefficientEval X h252Fiber7Mod163Factor2b19r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b19r10Coeffs) 162 h252Fiber7Mod163Factor2Binary19Step9 hs
theorem h252Fiber7Mod163Factor2Step19 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r18^163-h252Fiber7Mod163Factor2r19 := by
  have he : h252Fiber7Mod163Factor2b19r10Coeffs = h252Fiber7Mod163Factor2r19Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r19] using h252Fiber7Mod163Factor2Binary19Step10
theorem h252Fiber7Mod163Factor2Frob19 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 19-h252Fiber7Mod163Factor2r19 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob18 h252Fiber7Mod163Factor2Step19
theorem h252Fiber7Mod163Factor2Binary20Step0 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^1-h252Fiber7Mod163Factor2r19 := by simp
theorem h252Fiber7Mod163Factor2Binary20Step1 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^2-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2r19Coeffs h252Fiber7Mod163Factor2r19Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor2r19)*(h252Fiber7Mod163Factor2r19)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q1Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (h252Fiber7Mod163Factor2r19)*(h252Fiber7Mod163Factor2r19)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (h252Fiber7Mod163Factor2r19) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs) 1 h252Fiber7Mod163Factor2Binary20Step0 hs
theorem h252Fiber7Mod163Factor2Binary20Step2 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^4-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r1Coeffs h252Fiber7Mod163Factor2b20r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q2Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q2Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r2Coeffs) 2 h252Fiber7Mod163Factor2Binary20Step1 hs
theorem h252Fiber7Mod163Factor2Binary20Step3 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^5-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r2Coeffs h252Fiber7Mod163Factor2r19Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q3Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r2Coeffs)*(h252Fiber7Mod163Factor2r19)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q3Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r2Coeffs)*(h252Fiber7Mod163Factor2r19)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs) 4 h252Fiber7Mod163Factor2Binary20Step2 hs
theorem h252Fiber7Mod163Factor2Binary20Step4 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^10-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r3Coeffs h252Fiber7Mod163Factor2b20r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q4Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q4Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs) 5 h252Fiber7Mod163Factor2Binary20Step3 hs
theorem h252Fiber7Mod163Factor2Binary20Step5 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^20-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r4Coeffs h252Fiber7Mod163Factor2b20r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q5Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q5Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs) 10 h252Fiber7Mod163Factor2Binary20Step4 hs
theorem h252Fiber7Mod163Factor2Binary20Step6 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^40-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r5Coeffs h252Fiber7Mod163Factor2b20r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q6Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q6Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs) 20 h252Fiber7Mod163Factor2Binary20Step5 hs
theorem h252Fiber7Mod163Factor2Binary20Step7 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^80-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r6Coeffs h252Fiber7Mod163Factor2b20r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q7Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q7Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r7Coeffs) 40 h252Fiber7Mod163Factor2Binary20Step6 hs
theorem h252Fiber7Mod163Factor2Binary20Step8 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^81-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r7Coeffs h252Fiber7Mod163Factor2r19Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q8Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r7Coeffs)*(h252Fiber7Mod163Factor2r19)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q8Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r7Coeffs)*(h252Fiber7Mod163Factor2r19)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs) 80 h252Fiber7Mod163Factor2Binary20Step7 hs
theorem h252Fiber7Mod163Factor2Binary20Step9 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^162-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r8Coeffs h252Fiber7Mod163Factor2b20r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q9Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q9Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r9Coeffs) 81 h252Fiber7Mod163Factor2Binary20Step8 hs
theorem h252Fiber7Mod163Factor2Binary20Step10 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^163-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2b20r9Coeffs h252Fiber7Mod163Factor2r19Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor2b20r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor2b20q10Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor2b20r9Coeffs)*(h252Fiber7Mod163Factor2r19)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor2b20q10Coeffs * h252Fiber7Mod163Factor2 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r19] using h
  have hs : h252Fiber7Mod163Factor2 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor2b20r9Coeffs)*(h252Fiber7Mod163Factor2r19)-(integerCoefficientEval X h252Fiber7Mod163Factor2b20r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor2b20q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor2 h252Fiber7Mod163Factor2r19 (integerCoefficientEval X h252Fiber7Mod163Factor2b20r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor2b20r10Coeffs) 162 h252Fiber7Mod163Factor2Binary20Step9 hs
theorem h252Fiber7Mod163Factor2Step20 : h252Fiber7Mod163Factor2 ∣ h252Fiber7Mod163Factor2r19^163-h252Fiber7Mod163Factor2r20 := by
  have he : h252Fiber7Mod163Factor2b20r10Coeffs = h252Fiber7Mod163Factor2r20Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor2r20] using h252Fiber7Mod163Factor2Binary20Step10
theorem h252Fiber7Mod163Factor2Frob20 : h252Fiber7Mod163Factor2 ∣ frobeniusIter 163 20-h252Fiber7Mod163Factor2r20 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor2Frob19 h252Fiber7Mod163Factor2Step20
end
end Biunimodular.F11
