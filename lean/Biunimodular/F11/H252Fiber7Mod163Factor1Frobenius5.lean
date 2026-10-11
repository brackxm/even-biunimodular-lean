/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor1Frobenius4

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor1Binary21Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^1-h252Fiber7Mod163Factor1r20 := by simp
theorem h252Fiber7Mod163Factor1Binary21Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r20Coeffs h252Fiber7Mod163Factor1r20Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r20)*(h252Fiber7Mod163Factor1r20)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r20)*(h252Fiber7Mod163Factor1r20)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (h252Fiber7Mod163Factor1r20) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs) 1 h252Fiber7Mod163Factor1Binary21Step0 hs
theorem h252Fiber7Mod163Factor1Binary21Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r1Coeffs h252Fiber7Mod163Factor1b21r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r2Coeffs) 2 h252Fiber7Mod163Factor1Binary21Step1 hs
theorem h252Fiber7Mod163Factor1Binary21Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r2Coeffs h252Fiber7Mod163Factor1r20Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r2Coeffs)*(h252Fiber7Mod163Factor1r20)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r2Coeffs)*(h252Fiber7Mod163Factor1r20)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs) 4 h252Fiber7Mod163Factor1Binary21Step2 hs
theorem h252Fiber7Mod163Factor1Binary21Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r3Coeffs h252Fiber7Mod163Factor1b21r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs) 5 h252Fiber7Mod163Factor1Binary21Step3 hs
theorem h252Fiber7Mod163Factor1Binary21Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r4Coeffs h252Fiber7Mod163Factor1b21r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs) 10 h252Fiber7Mod163Factor1Binary21Step4 hs
theorem h252Fiber7Mod163Factor1Binary21Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r5Coeffs h252Fiber7Mod163Factor1b21r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs) 20 h252Fiber7Mod163Factor1Binary21Step5 hs
theorem h252Fiber7Mod163Factor1Binary21Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r6Coeffs h252Fiber7Mod163Factor1b21r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r7Coeffs) 40 h252Fiber7Mod163Factor1Binary21Step6 hs
theorem h252Fiber7Mod163Factor1Binary21Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r7Coeffs h252Fiber7Mod163Factor1r20Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r7Coeffs)*(h252Fiber7Mod163Factor1r20)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r7Coeffs)*(h252Fiber7Mod163Factor1r20)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs) 80 h252Fiber7Mod163Factor1Binary21Step7 hs
theorem h252Fiber7Mod163Factor1Binary21Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r8Coeffs h252Fiber7Mod163Factor1b21r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r9Coeffs) 81 h252Fiber7Mod163Factor1Binary21Step8 hs
theorem h252Fiber7Mod163Factor1Binary21Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b21r9Coeffs h252Fiber7Mod163Factor1r20Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b21r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b21q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b21r9Coeffs)*(h252Fiber7Mod163Factor1r20)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b21q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b21r9Coeffs)*(h252Fiber7Mod163Factor1r20)-(integerCoefficientEval X h252Fiber7Mod163Factor1b21r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b21q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r20 (integerCoefficientEval X h252Fiber7Mod163Factor1b21r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b21r10Coeffs) 162 h252Fiber7Mod163Factor1Binary21Step9 hs
theorem h252Fiber7Mod163Factor1Step21 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r20^163-h252Fiber7Mod163Factor1r21 := by
  have he : h252Fiber7Mod163Factor1b21r10Coeffs = h252Fiber7Mod163Factor1r21Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r21] using h252Fiber7Mod163Factor1Binary21Step10
theorem h252Fiber7Mod163Factor1Frob21 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 21-h252Fiber7Mod163Factor1r21 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob20 h252Fiber7Mod163Factor1Step21
theorem h252Fiber7Mod163Factor1Binary22Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^1-h252Fiber7Mod163Factor1r21 := by simp
theorem h252Fiber7Mod163Factor1Binary22Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r21Coeffs h252Fiber7Mod163Factor1r21Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r21)*(h252Fiber7Mod163Factor1r21)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r21)*(h252Fiber7Mod163Factor1r21)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (h252Fiber7Mod163Factor1r21) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs) 1 h252Fiber7Mod163Factor1Binary22Step0 hs
theorem h252Fiber7Mod163Factor1Binary22Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r1Coeffs h252Fiber7Mod163Factor1b22r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r2Coeffs) 2 h252Fiber7Mod163Factor1Binary22Step1 hs
theorem h252Fiber7Mod163Factor1Binary22Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r2Coeffs h252Fiber7Mod163Factor1r21Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r2Coeffs)*(h252Fiber7Mod163Factor1r21)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r2Coeffs)*(h252Fiber7Mod163Factor1r21)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs) 4 h252Fiber7Mod163Factor1Binary22Step2 hs
theorem h252Fiber7Mod163Factor1Binary22Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r3Coeffs h252Fiber7Mod163Factor1b22r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs) 5 h252Fiber7Mod163Factor1Binary22Step3 hs
theorem h252Fiber7Mod163Factor1Binary22Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r4Coeffs h252Fiber7Mod163Factor1b22r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs) 10 h252Fiber7Mod163Factor1Binary22Step4 hs
theorem h252Fiber7Mod163Factor1Binary22Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r5Coeffs h252Fiber7Mod163Factor1b22r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs) 20 h252Fiber7Mod163Factor1Binary22Step5 hs
theorem h252Fiber7Mod163Factor1Binary22Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r6Coeffs h252Fiber7Mod163Factor1b22r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r7Coeffs) 40 h252Fiber7Mod163Factor1Binary22Step6 hs
theorem h252Fiber7Mod163Factor1Binary22Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r7Coeffs h252Fiber7Mod163Factor1r21Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r7Coeffs)*(h252Fiber7Mod163Factor1r21)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r7Coeffs)*(h252Fiber7Mod163Factor1r21)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs) 80 h252Fiber7Mod163Factor1Binary22Step7 hs
theorem h252Fiber7Mod163Factor1Binary22Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r8Coeffs h252Fiber7Mod163Factor1b22r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r9Coeffs) 81 h252Fiber7Mod163Factor1Binary22Step8 hs
theorem h252Fiber7Mod163Factor1Binary22Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b22r9Coeffs h252Fiber7Mod163Factor1r21Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b22r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b22q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b22r9Coeffs)*(h252Fiber7Mod163Factor1r21)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b22q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r21] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b22r9Coeffs)*(h252Fiber7Mod163Factor1r21)-(integerCoefficientEval X h252Fiber7Mod163Factor1b22r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b22q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r21 (integerCoefficientEval X h252Fiber7Mod163Factor1b22r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b22r10Coeffs) 162 h252Fiber7Mod163Factor1Binary22Step9 hs
theorem h252Fiber7Mod163Factor1Step22 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r21^163-h252Fiber7Mod163Factor1r22 := by
  have he : h252Fiber7Mod163Factor1b22r10Coeffs = h252Fiber7Mod163Factor1r22Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r22] using h252Fiber7Mod163Factor1Binary22Step10
theorem h252Fiber7Mod163Factor1Frob22 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 22-h252Fiber7Mod163Factor1r22 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob21 h252Fiber7Mod163Factor1Step22
theorem h252Fiber7Mod163Factor1Binary23Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^1-h252Fiber7Mod163Factor1r22 := by simp
theorem h252Fiber7Mod163Factor1Binary23Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r22Coeffs h252Fiber7Mod163Factor1r22Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r22)*(h252Fiber7Mod163Factor1r22)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r22)*(h252Fiber7Mod163Factor1r22)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (h252Fiber7Mod163Factor1r22) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs) 1 h252Fiber7Mod163Factor1Binary23Step0 hs
theorem h252Fiber7Mod163Factor1Binary23Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r1Coeffs h252Fiber7Mod163Factor1b23r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r2Coeffs) 2 h252Fiber7Mod163Factor1Binary23Step1 hs
theorem h252Fiber7Mod163Factor1Binary23Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r2Coeffs h252Fiber7Mod163Factor1r22Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r2Coeffs)*(h252Fiber7Mod163Factor1r22)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r2Coeffs)*(h252Fiber7Mod163Factor1r22)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs) 4 h252Fiber7Mod163Factor1Binary23Step2 hs
theorem h252Fiber7Mod163Factor1Binary23Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r3Coeffs h252Fiber7Mod163Factor1b23r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs) 5 h252Fiber7Mod163Factor1Binary23Step3 hs
theorem h252Fiber7Mod163Factor1Binary23Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r4Coeffs h252Fiber7Mod163Factor1b23r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs) 10 h252Fiber7Mod163Factor1Binary23Step4 hs
theorem h252Fiber7Mod163Factor1Binary23Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r5Coeffs h252Fiber7Mod163Factor1b23r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs) 20 h252Fiber7Mod163Factor1Binary23Step5 hs
theorem h252Fiber7Mod163Factor1Binary23Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r6Coeffs h252Fiber7Mod163Factor1b23r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r7Coeffs) 40 h252Fiber7Mod163Factor1Binary23Step6 hs
theorem h252Fiber7Mod163Factor1Binary23Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r7Coeffs h252Fiber7Mod163Factor1r22Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r7Coeffs)*(h252Fiber7Mod163Factor1r22)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r7Coeffs)*(h252Fiber7Mod163Factor1r22)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs) 80 h252Fiber7Mod163Factor1Binary23Step7 hs
theorem h252Fiber7Mod163Factor1Binary23Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r8Coeffs h252Fiber7Mod163Factor1b23r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r9Coeffs) 81 h252Fiber7Mod163Factor1Binary23Step8 hs
theorem h252Fiber7Mod163Factor1Binary23Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b23r9Coeffs h252Fiber7Mod163Factor1r22Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b23r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b23q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b23r9Coeffs)*(h252Fiber7Mod163Factor1r22)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b23q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r22] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b23r9Coeffs)*(h252Fiber7Mod163Factor1r22)-(integerCoefficientEval X h252Fiber7Mod163Factor1b23r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b23q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r22 (integerCoefficientEval X h252Fiber7Mod163Factor1b23r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b23r10Coeffs) 162 h252Fiber7Mod163Factor1Binary23Step9 hs
theorem h252Fiber7Mod163Factor1Step23 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r22^163-h252Fiber7Mod163Factor1r23 := by
  have he : h252Fiber7Mod163Factor1b23r10Coeffs = h252Fiber7Mod163Factor1r23Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r23] using h252Fiber7Mod163Factor1Binary23Step10
theorem h252Fiber7Mod163Factor1Frob23 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 23-h252Fiber7Mod163Factor1r23 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob22 h252Fiber7Mod163Factor1Step23
theorem h252Fiber7Mod163Factor1Binary24Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^1-h252Fiber7Mod163Factor1r23 := by simp
theorem h252Fiber7Mod163Factor1Binary24Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r23Coeffs h252Fiber7Mod163Factor1r23Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r23)*(h252Fiber7Mod163Factor1r23)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r23)*(h252Fiber7Mod163Factor1r23)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (h252Fiber7Mod163Factor1r23) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs) 1 h252Fiber7Mod163Factor1Binary24Step0 hs
theorem h252Fiber7Mod163Factor1Binary24Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r1Coeffs h252Fiber7Mod163Factor1b24r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r2Coeffs) 2 h252Fiber7Mod163Factor1Binary24Step1 hs
theorem h252Fiber7Mod163Factor1Binary24Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r2Coeffs h252Fiber7Mod163Factor1r23Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r2Coeffs)*(h252Fiber7Mod163Factor1r23)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r2Coeffs)*(h252Fiber7Mod163Factor1r23)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs) 4 h252Fiber7Mod163Factor1Binary24Step2 hs
theorem h252Fiber7Mod163Factor1Binary24Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r3Coeffs h252Fiber7Mod163Factor1b24r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs) 5 h252Fiber7Mod163Factor1Binary24Step3 hs
theorem h252Fiber7Mod163Factor1Binary24Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r4Coeffs h252Fiber7Mod163Factor1b24r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs) 10 h252Fiber7Mod163Factor1Binary24Step4 hs
theorem h252Fiber7Mod163Factor1Binary24Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r5Coeffs h252Fiber7Mod163Factor1b24r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs) 20 h252Fiber7Mod163Factor1Binary24Step5 hs
theorem h252Fiber7Mod163Factor1Binary24Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r6Coeffs h252Fiber7Mod163Factor1b24r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r7Coeffs) 40 h252Fiber7Mod163Factor1Binary24Step6 hs
theorem h252Fiber7Mod163Factor1Binary24Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r7Coeffs h252Fiber7Mod163Factor1r23Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r7Coeffs)*(h252Fiber7Mod163Factor1r23)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r7Coeffs)*(h252Fiber7Mod163Factor1r23)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs) 80 h252Fiber7Mod163Factor1Binary24Step7 hs
theorem h252Fiber7Mod163Factor1Binary24Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r8Coeffs h252Fiber7Mod163Factor1b24r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r9Coeffs) 81 h252Fiber7Mod163Factor1Binary24Step8 hs
theorem h252Fiber7Mod163Factor1Binary24Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b24r9Coeffs h252Fiber7Mod163Factor1r23Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b24r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b24q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b24r9Coeffs)*(h252Fiber7Mod163Factor1r23)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b24q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r23] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b24r9Coeffs)*(h252Fiber7Mod163Factor1r23)-(integerCoefficientEval X h252Fiber7Mod163Factor1b24r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b24q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r23 (integerCoefficientEval X h252Fiber7Mod163Factor1b24r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b24r10Coeffs) 162 h252Fiber7Mod163Factor1Binary24Step9 hs
theorem h252Fiber7Mod163Factor1Step24 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r23^163-h252Fiber7Mod163Factor1r24 := by
  have he : h252Fiber7Mod163Factor1b24r10Coeffs = h252Fiber7Mod163Factor1r24Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r24] using h252Fiber7Mod163Factor1Binary24Step10
theorem h252Fiber7Mod163Factor1Frob24 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 24-h252Fiber7Mod163Factor1r24 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob23 h252Fiber7Mod163Factor1Step24
theorem h252Fiber7Mod163Factor1Binary25Step0 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^1-h252Fiber7Mod163Factor1r24 := by simp
theorem h252Fiber7Mod163Factor1Binary25Step1 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^2-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1r24Coeffs h252Fiber7Mod163Factor1r24Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r1Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q1Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (h252Fiber7Mod163Factor1r24)*(h252Fiber7Mod163Factor1r24)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q1Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (h252Fiber7Mod163Factor1r24)*(h252Fiber7Mod163Factor1r24)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q1Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (h252Fiber7Mod163Factor1r24) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs) 1 h252Fiber7Mod163Factor1Binary25Step0 hs
theorem h252Fiber7Mod163Factor1Binary25Step2 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^4-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r2Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r1Coeffs h252Fiber7Mod163Factor1b25r1Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r2Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q2Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r2Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q2Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r2Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q2Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r1Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r2Coeffs) 2 h252Fiber7Mod163Factor1Binary25Step1 hs
theorem h252Fiber7Mod163Factor1Binary25Step3 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^5-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r2Coeffs h252Fiber7Mod163Factor1r24Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r3Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q3Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r2Coeffs)*(h252Fiber7Mod163Factor1r24)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q3Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r2Coeffs)*(h252Fiber7Mod163Factor1r24)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q3Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r2Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs) 4 h252Fiber7Mod163Factor1Binary25Step2 hs
theorem h252Fiber7Mod163Factor1Binary25Step4 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^10-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r3Coeffs h252Fiber7Mod163Factor1b25r3Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r4Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q4Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q4Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q4Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r3Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs) 5 h252Fiber7Mod163Factor1Binary25Step3 hs
theorem h252Fiber7Mod163Factor1Binary25Step5 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^20-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r4Coeffs h252Fiber7Mod163Factor1b25r4Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r5Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q5Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q5Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q5Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r4Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs) 10 h252Fiber7Mod163Factor1Binary25Step4 hs
theorem h252Fiber7Mod163Factor1Binary25Step6 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^40-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r5Coeffs h252Fiber7Mod163Factor1b25r5Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r6Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q6Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q6Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q6Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r5Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs) 20 h252Fiber7Mod163Factor1Binary25Step5 hs
theorem h252Fiber7Mod163Factor1Binary25Step7 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^80-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r7Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r6Coeffs h252Fiber7Mod163Factor1b25r6Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r7Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q7Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r7Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q7Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r7Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q7Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r6Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r7Coeffs) 40 h252Fiber7Mod163Factor1Binary25Step6 hs
theorem h252Fiber7Mod163Factor1Binary25Step8 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^81-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r7Coeffs h252Fiber7Mod163Factor1r24Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r8Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q8Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r7Coeffs)*(h252Fiber7Mod163Factor1r24)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q8Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r7Coeffs)*(h252Fiber7Mod163Factor1r24)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q8Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r7Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs) 80 h252Fiber7Mod163Factor1Binary25Step7 hs
theorem h252Fiber7Mod163Factor1Binary25Step9 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^162-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r9Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r8Coeffs h252Fiber7Mod163Factor1b25r8Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r9Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q9Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r9Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q9Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs)*(integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r9Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q9Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_double h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r8Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r9Coeffs) 81 h252Fiber7Mod163Factor1Binary25Step8 hs
theorem h252Fiber7Mod163Factor1Binary25Step10 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^163-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r10Coeffs) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1b25r9Coeffs h252Fiber7Mod163Factor1r24Coeffs) (integerCoefficientScale (-1) h252Fiber7Mod163Factor1b25r10Coeffs)) (integerCoefficientMul h252Fiber7Mod163Factor1b25q10Coeffs h252Fiber7Mod163Factor1Coeffs) = true := by native_decide
  have he : (integerCoefficientEval X h252Fiber7Mod163Factor1b25r9Coeffs)*(h252Fiber7Mod163Factor1r24)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r10Coeffs) =
      integerCoefficientEval X h252Fiber7Mod163Factor1b25q10Coeffs * h252Fiber7Mod163Factor1 := by
    have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
    simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_scale,
      Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r24] using h
  have hs : h252Fiber7Mod163Factor1 ∣ (integerCoefficientEval X h252Fiber7Mod163Factor1b25r9Coeffs)*(h252Fiber7Mod163Factor1r24)-(integerCoefficientEval X h252Fiber7Mod163Factor1b25r10Coeffs) :=
    ⟨integerCoefficientEval X h252Fiber7Mod163Factor1b25q10Coeffs, by rw [he]; ring⟩
  exact binaryPowerRemainder_add_one h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor1r24 (integerCoefficientEval X h252Fiber7Mod163Factor1b25r9Coeffs) (integerCoefficientEval X h252Fiber7Mod163Factor1b25r10Coeffs) 162 h252Fiber7Mod163Factor1Binary25Step9 hs
theorem h252Fiber7Mod163Factor1Step25 : h252Fiber7Mod163Factor1 ∣ h252Fiber7Mod163Factor1r24^163-h252Fiber7Mod163Factor1r25 := by
  have he : h252Fiber7Mod163Factor1b25r10Coeffs = h252Fiber7Mod163Factor1r25Coeffs := by native_decide
  simpa only [he, h252Fiber7Mod163Factor1r25] using h252Fiber7Mod163Factor1Binary25Step10
theorem h252Fiber7Mod163Factor1Frob25 : h252Fiber7Mod163Factor1 ∣ frobeniusIter 163 25-h252Fiber7Mod163Factor1r25 :=
  frobeniusIter_dvd_next h252Fiber7Mod163Factor1Frob24 h252Fiber7Mod163Factor1Step25
end
end Biunimodular.F11
