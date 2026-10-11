/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurBezout
import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

open Polynomial

theorem h252RurBezoutHDen_pos : 0 < h252RurBezoutHDen := by native_decide
theorem h252RurBezoutDDen_pos : 0 < h252RurBezoutDDen := by native_decide

noncomputable section

def h252RurComplexPolynomial : ℂ[X] :=
  integerCoefficientEval X h252RurHCoeffs

def h252RurDenominator (x : ℂ) : ℂ :=
  integerCoefficientEval x h252RurDCoeffs

theorem h252RurBezout_eval (x : ℂ) :
    (h252RurBezoutDDen : ℂ) *
        (integerCoefficientEval x h252RurBezoutHCoeffs *
          integerCoefficientEval x h252RurHCoeffs) +
      (h252RurBezoutHDen : ℂ) *
        (integerCoefficientEval x h252RurBezoutDCoeffs *
          integerCoefficientEval x h252RurDCoeffs) =
      (h252RurCommonDen * h252RurBezoutHDen * h252RurBezoutDDen : ℤ) := by
  have h := integerCoefficientEval_eq_of_equal x _ _ h252RurBezout_coefficients
  simpa only [integerCoefficientEval_sum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
    integerCoefficientEval_mul, integerCoefficientEval_singleton, mul_zero,
    add_zero] using h

theorem h252RurDenominator_ne_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) : h252RurDenominator x ≠ 0 := by
  have hx0 : integerCoefficientEval x h252RurHCoeffs = 0 := by
    simpa [h252RurComplexPolynomial, integerCoefficientPolynomial_eval] using hx
  intro hd
  have h := h252RurBezout_eval x
  change integerCoefficientEval x h252RurDCoeffs = 0 at hd
  rw [hx0, hd, mul_zero, mul_zero, mul_zero, mul_zero, zero_add] at h
  have ht : 0 < h252RurCommonDen * h252RurBezoutHDen * h252RurBezoutDDen :=
    mul_pos (mul_pos h252RurCommonDen_pos h252RurBezoutHDen_pos) h252RurBezoutDDen_pos
  have hn : (h252RurCommonDen * h252RurBezoutHDen * h252RurBezoutDDen : ℤ) ≠ 0 :=
    ne_of_gt ht
  exact hn (by exact_mod_cast h.symm)

theorem h252RurComplexPolynomial_separable : h252RurComplexPolynomial.Separable := by
  let t : ℤ := h252RurCommonDen * h252RurBezoutHDen * h252RurBezoutDDen
  have ht : (t : ℂ) ≠ 0 := by
    have hpos : 0 < t :=
      mul_pos (mul_pos h252RurCommonDen_pos h252RurBezoutHDen_pos) h252RurBezoutDDen_pos
    exact_mod_cast ne_of_gt hpos
  have hd : derivative h252RurComplexPolynomial =
      integerCoefficientEval X h252RurDCoeffs := by
    rw [h252RurComplexPolynomial, integerCoefficientPolynomial_derivative,
      h252RurD_derivative_coefficients]
  have h := integerCoefficientEval_eq_of_equal (X : ℂ[X]) _ _ h252RurBezout_coefficients
  simp only [integerCoefficientEval_sum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
    integerCoefficientEval_mul, integerCoefficientEval_singleton, add_zero] at h
  apply (Polynomial.separable_def' _).mpr
  refine ⟨C ((t : ℂ)⁻¹) * (h252RurBezoutDDen : ℂ[X]) *
      integerCoefficientEval X h252RurBezoutHCoeffs,
    C ((t : ℂ)⁻¹) * (h252RurBezoutHDen : ℂ[X]) *
      integerCoefficientEval X h252RurBezoutDCoeffs, ?_⟩
  rw [hd]
  change _ * integerCoefficientEval X h252RurHCoeffs + _ = 1
  calc
    _ = C ((t : ℂ)⁻¹) *
        ((h252RurBezoutDDen : ℂ[X]) *
            (integerCoefficientEval X h252RurBezoutHCoeffs *
              integerCoefficientEval X h252RurHCoeffs) +
          (h252RurBezoutHDen : ℂ[X]) *
            (integerCoefficientEval X h252RurBezoutDCoeffs *
              integerCoefficientEval X h252RurDCoeffs)) := by ring
    _ = C ((t : ℂ)⁻¹) * (t : ℂ[X]) := by rw [h]
    _ = 1 := by
      change C ((t : ℂ)⁻¹) * C (t : ℂ) = 1
      rw [← C_mul, inv_mul_cancel₀ ht, C_1]

end

end Biunimodular.F11
