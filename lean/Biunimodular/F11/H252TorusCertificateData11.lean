/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252TorusCertificateData11Literals171

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Biunimodular.F11

open Polynomial

private theorem h252TorusEliminant_circleFactor_coefficients11 :
    h252CoefficientMulZ h252TorusEliminantCoeffs11
        h252CircleQuotientCoeffs11 =
      h252CircleLiftCoeffs11 := by
  native_decide

private theorem h252TorusEliminant_saturated_identity_coefficients11 :
    h252SparseNormalize11
        (h252SparseMul11 h252TorusD5Sparse11
          (h252SparseOfZ5Coefficients11 h252TorusEliminantCoeffs11)) =
      h252SparseAdd11 (h252SparseMul11 h252TorusMultiplier1Sparse11 h252TorusGenerator1Sparse11) (h252SparseAdd11 (h252SparseMul11 h252TorusMultiplier2Sparse11 h252TorusGenerator2Sparse11) (h252SparseAdd11 (h252SparseMul11 h252TorusMultiplier3Sparse11 h252TorusGenerator3Sparse11) (h252SparseAdd11 (h252SparseMul11 h252TorusMultiplier4Sparse11 h252TorusGenerator4Sparse11) (h252SparseMul11 h252TorusMultiplier5Sparse11 h252TorusGenerator5Sparse11)))) := by
  native_decide

noncomputable section

/-! Generated exact certificate data. -/

def h252TorusEliminantEval11 (z5 : ℂ) : ℂ :=
  h252EvalCoefficientsC h252TorusEliminantCoeffs11 z5

def h252CircleQuotientEval11 (z5 : ℂ) : ℂ :=
  h252EvalCoefficientsC h252CircleQuotientCoeffs11 z5

def h252TorusMultiplier1Eval11
    (z1 z2 z3 z4 w z5 : ℂ) : ℂ :=
  h252SparseEval11 h252TorusMultiplier1Sparse11 z1 z2 z3 z4 w z5

def h252TorusMultiplier2Eval11
    (z1 z2 z3 z4 w z5 : ℂ) : ℂ :=
  h252SparseEval11 h252TorusMultiplier2Sparse11 z1 z2 z3 z4 w z5

def h252TorusMultiplier3Eval11
    (z1 z2 z3 z4 w z5 : ℂ) : ℂ :=
  h252SparseEval11 h252TorusMultiplier3Sparse11 z1 z2 z3 z4 w z5

def h252TorusMultiplier4Eval11
    (z1 z2 z3 z4 w z5 : ℂ) : ℂ :=
  h252SparseEval11 h252TorusMultiplier4Sparse11 z1 z2 z3 z4 w z5

def h252TorusMultiplier5Eval11
    (z1 z2 z3 z4 w z5 : ℂ) : ℂ :=
  h252SparseEval11 h252TorusMultiplier5Sparse11 z1 z2 z3 z4 w z5


private theorem h252TorusD5_eval11 (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 h252TorusD5Sparse11 z1 z2 z3 z4 w z5 =
      h252TorusD z1 z2 z3 z4 z5 := by
  simp [h252TorusD5Sparse11, h252SparseEval11,
    h252SparseTermEval11, h252TorusD]

private theorem h252TorusGenerator1_eval11
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 h252TorusGenerator1Sparse11 z1 z2 z3 z4 w z5 =
      h252TorusF1 z1 z2 z3 z4 z5 := by
  simp only [h252TorusGenerator1Sparse11, h252SparseEval11,
    h252SparseTermEval11, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, pow_zero, pow_one, mul_one, Int.cast_one,
    h252TorusF1]
  ring

private theorem h252TorusGenerator2_eval11
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 h252TorusGenerator2Sparse11 z1 z2 z3 z4 w z5 =
      h252TorusF2 z1 z2 z3 z4 z5 := by
  simp only [h252TorusGenerator2Sparse11, h252SparseEval11,
    h252SparseTermEval11, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, pow_zero, pow_one, mul_one, Int.cast_one,
    h252TorusF2]
  ring

private theorem h252TorusGenerator3_eval11
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 h252TorusGenerator3Sparse11 z1 z2 z3 z4 w z5 =
      h252TorusF3 z1 z2 z3 z4 z5 := by
  simp only [h252TorusGenerator3Sparse11, h252SparseEval11,
    h252SparseTermEval11, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, pow_zero, pow_one, mul_one, Int.cast_one,
    h252TorusF3]
  ring

private theorem h252TorusGenerator4_eval11
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 h252TorusGenerator4Sparse11 z1 z2 z3 z4 w z5 =
      h252TorusF4 z1 z2 z3 z4 z5 := by
  simp only [h252TorusGenerator4Sparse11, h252SparseEval11,
    h252SparseTermEval11, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, pow_zero, pow_one, mul_one, Int.cast_one,
    h252TorusF4]
  ring

private theorem h252TorusGenerator5_eval11
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 h252TorusGenerator5Sparse11 z1 z2 z3 z4 w z5 =
      h252TorusF5 z1 z2 z3 z4 z5 := by
  simp only [h252TorusGenerator5Sparse11, h252SparseEval11,
    h252SparseTermEval11, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, pow_zero, pow_one, mul_one, Int.cast_one,
    h252TorusF5]
  ring


theorem h252TorusEliminant_saturated_identity11
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252TorusD z1 z2 z3 z4 z5 * h252TorusEliminantEval11 z5 =
      h252TorusMultiplier1Eval11 z1 z2 z3 z4 w z5 * h252TorusF1 z1 z2 z3 z4 z5 +
      (h252TorusMultiplier2Eval11 z1 z2 z3 z4 w z5 * h252TorusF2 z1 z2 z3 z4 z5 +
      (h252TorusMultiplier3Eval11 z1 z2 z3 z4 w z5 * h252TorusF3 z1 z2 z3 z4 z5 +
      (h252TorusMultiplier4Eval11 z1 z2 z3 z4 w z5 * h252TorusF4 z1 z2 z3 z4 z5 +
      (h252TorusMultiplier5Eval11 z1 z2 z3 z4 w z5 * h252TorusF5 z1 z2 z3 z4 z5)))) := by
  have h := congrArg
    (fun terms => h252SparseEval11 terms z1 z2 z3 z4 w z5)
    h252TorusEliminant_saturated_identity_coefficients11
  simp only [h252SparseEval_normalize11, h252SparseEval_add11,
    h252SparseEval_mul11, h252SparseEval_ofZ5Coefficients11] at h
  rw [h252TorusD5_eval11,
    h252TorusGenerator1_eval11, h252TorusGenerator2_eval11,
    h252TorusGenerator3_eval11, h252TorusGenerator4_eval11,
    h252TorusGenerator5_eval11] at h
  simpa only [h252TorusEliminantEval11,
    h252TorusMultiplier1Eval11, h252TorusMultiplier2Eval11,
    h252TorusMultiplier3Eval11, h252TorusMultiplier4Eval11,
    h252TorusMultiplier5Eval11] using h

theorem h252TorusEliminant_zero11 (z1 z2 z3 z4 w z5 : ℂ)
    (h1 : h252TorusF1 z1 z2 z3 z4 z5 = 0)
    (h2 : h252TorusF2 z1 z2 z3 z4 z5 = 0)
    (h3 : h252TorusF3 z1 z2 z3 z4 z5 = 0)
    (h4 : h252TorusF4 z1 z2 z3 z4 z5 = 0)
    (h5 : h252TorusF5 z1 z2 z3 z4 z5 = 0)
    (h6 : h252TorusS z1 z2 z3 z4 w z5 = 0) :
    h252TorusEliminantEval11 z5 = 0 := by
  have hD : h252TorusD z1 z2 z3 z4 z5 ≠ 0 := by
    intro hzero
    simp [h252TorusS, hzero] at h6
  have hid := h252TorusEliminant_saturated_identity11 z1 z2 z3 z4 w z5
  simp only [h1, h2, h3, h4, h5, mul_zero, add_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_left hD

theorem h252TorusEliminant_circleFactor11 (z5 : ℂ) :
    h252TorusEliminantEval11 z5 * h252CircleQuotientEval11 z5 =
      (1 : ℂ) * h252CircleLiftEval11 z5 := by
  calc
    h252TorusEliminantEval11 z5 * h252CircleQuotientEval11 z5 =
        h252EvalCoefficientsC
          (h252CoefficientMulZ h252TorusEliminantCoeffs11
            h252CircleQuotientCoeffs11) z5 := by
          rw [h252EvalCoefficients_mul11]
          rfl
    _ = h252EvalCoefficientsC h252CircleLiftCoeffs11 z5 := by
          rw [h252TorusEliminant_circleFactor_coefficients11]
    _ = (1 : ℂ) * h252CircleLiftEval11 z5 := by
          simp [h252CircleLiftEval11]

end

end Biunimodular.F11
