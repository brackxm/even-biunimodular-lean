/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusFiberGeneratorsData
import Biunimodular.F11.RurInverseGeneratorSemantics

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
variable {R : Type*} [CommRing R]

theorem torusFiberOriginal1_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal1 z1 z2 z3 z4 w z5 x =
      h252TorusS z1 z2 z3 z4 w z5 := by
  simp only [torusFiberOriginal1, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, Int.cast_neg, mul_one, one_mul,
    h252TorusS, h252TorusD]
  ring

theorem torusFiberOriginal2_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal2 z1 z2 z3 z4 w z5 x =
      h252TorusS z1 z2 z3 z4 w z5 := by
  simp only [torusFiberOriginal2, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, Int.cast_neg, mul_one, one_mul,
    h252TorusS, h252TorusD]
  ring

theorem torusFiberOriginal3_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal3 z1 z2 z3 z4 w z5 x =
      h252TorusS z1 z2 z3 z4 w z5 := by
  simp only [torusFiberOriginal3, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, Int.cast_neg, mul_one, one_mul,
    h252TorusS, h252TorusD]
  ring

theorem torusFiberOriginal4_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal4 z1 z2 z3 z4 w z5 x =
      h252TorusS z1 z2 z3 z4 w z5 := by
  simp only [torusFiberOriginal4, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, Int.cast_neg, mul_one, one_mul,
    h252TorusS, h252TorusD]
  ring

theorem torusFiberOriginal5_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal5 z1 z2 z3 z4 w z5 x =
      h252TorusS z1 z2 z3 z4 w z5 := by
  simp only [torusFiberOriginal5, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, Int.cast_neg, mul_one, one_mul,
    h252TorusS, h252TorusD]
  ring

theorem torusFiberOriginal6_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal6 z1 z2 z3 z4 w z5 x =
      w * h252TorusF1 z1 z2 z3 z4 z5 - h252TorusS z1 z2 z3 z4 w z5 * (1 + z1) := by
  simp only [torusFiberOriginal6, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, mul_one, one_mul,
    h252TorusS, h252TorusD, h252TorusF1]
  ring

theorem torusFiberOriginal7_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal7 z1 z2 z3 z4 w z5 x =
      w * h252TorusF2 z1 z2 z3 z4 z5 - h252TorusS z1 z2 z3 z4 w z5 * (1 + z2) := by
  simp only [torusFiberOriginal7, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, mul_one, one_mul,
    h252TorusS, h252TorusD, h252TorusF2]
  ring

theorem torusFiberOriginal8_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal8 z1 z2 z3 z4 w z5 x =
      w * h252TorusF3 z1 z2 z3 z4 z5 - h252TorusS z1 z2 z3 z4 w z5 * (1 + z3) := by
  simp only [torusFiberOriginal8, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, mul_one, one_mul,
    h252TorusS, h252TorusD, h252TorusF3]
  ring

theorem torusFiberOriginal9_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal9 z1 z2 z3 z4 w z5 x =
      w * h252TorusF4 z1 z2 z3 z4 z5 - h252TorusS z1 z2 z3 z4 w z5 * (1 + z4) := by
  simp only [torusFiberOriginal9, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, mul_one, one_mul,
    h252TorusS, h252TorusD, h252TorusF4]
  ring

theorem torusFiberOriginal10_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval torusFiberOriginal10 z1 z2 z3 z4 w z5 x =
      w * h252TorusF5 z1 z2 z3 z4 z5 - h252TorusS z1 z2 z3 z4 w z5 * (1 + z5) := by
  simp only [torusFiberOriginal10, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, Int.cast_one, mul_one, one_mul,
    h252TorusS, h252TorusD, h252TorusF5]
  ring

noncomputable section

theorem torusFiberOriginal1_quotient_zero :
    rurInverseSparseEval torusFiberOriginal1 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal1_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  exact hs

theorem torusFiberOriginal2_quotient_zero :
    rurInverseSparseEval torusFiberOriginal2 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal2_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  exact hs

theorem torusFiberOriginal3_quotient_zero :
    rurInverseSparseEval torusFiberOriginal3 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal3_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  exact hs

theorem torusFiberOriginal4_quotient_zero :
    rurInverseSparseEval torusFiberOriginal4 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal4_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  exact hs

theorem torusFiberOriginal5_quotient_zero :
    rurInverseSparseEval torusFiberOriginal5 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal5_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  exact hs

theorem torusFiberOriginal6_quotient_zero :
    rurInverseSparseEval torusFiberOriginal6 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal6_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  have hf := rurInverseGenerator1_quotient_zero
  rw [rurInverseGenerator1_eval] at hf
  rw [hs, hf, mul_zero, zero_mul, sub_self]

theorem torusFiberOriginal7_quotient_zero :
    rurInverseSparseEval torusFiberOriginal7 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal7_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  have hf := rurInverseGenerator2_quotient_zero
  rw [rurInverseGenerator2_eval] at hf
  rw [hs, hf, mul_zero, zero_mul, sub_self]

theorem torusFiberOriginal8_quotient_zero :
    rurInverseSparseEval torusFiberOriginal8 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal8_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  have hf := rurInverseGenerator3_quotient_zero
  rw [rurInverseGenerator3_eval] at hf
  rw [hs, hf, mul_zero, zero_mul, sub_self]

theorem torusFiberOriginal9_quotient_zero :
    rurInverseSparseEval torusFiberOriginal9 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal9_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  have hf := rurInverseGenerator4_quotient_zero
  rw [rurInverseGenerator4_eval] at hf
  rw [hs, hf, mul_zero, zero_mul, sub_self]

theorem torusFiberOriginal10_quotient_zero :
    rurInverseSparseEval torusFiberOriginal10 (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [torusFiberOriginal10_eval]
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  have hf := rurInverseGenerator5_quotient_zero
  rw [rurInverseGenerator5_eval] at hf
  rw [hs, hf, mul_zero, zero_mul, sub_self]


end
end Biunimodular.F11
