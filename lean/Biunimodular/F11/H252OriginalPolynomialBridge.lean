/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurCircleLiftCoefficients
import Biunimodular.F11.H252RurSeparable
import Biunimodular.F11.P150PolynomialData11
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

/-- Substitute minus the square of the variable, using only integral lists. -/
def integerCoefficientNegativeSquare : List ℤ → List ℤ
  | [] => []
  | a :: as => a :: 0 :: integerCoefficientScale (-1) (integerCoefficientNegativeSquare as)

theorem integerCoefficientNegativeSquare_eval {R : Type*} [CommRing R]
    (x : R) (a : List ℤ) :
    integerCoefficientEval x (integerCoefficientNegativeSquare a) =
      integerCoefficientEval (-x ^ 2) a := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    rw [integerCoefficientNegativeSquare]
    simp only [integerCoefficientEval, Int.cast_zero, zero_add,
      integerCoefficientEval_scale, Int.cast_neg, Int.cast_one, ih]
    ring

def h252OriginalSquaredCoeffs : List ℤ :=
  integerCoefficientMul
    (integerCoefficientMul (integerCoefficientMul p150G5Coeffs11 p150F30Coeffs11)
      p150F40Coeffs11) r102SquaredCoeffs11

/-- Exact identification with the original factorized H252. -/
theorem h252Rur_original_coefficients :
    integerCoefficientEqual
      (integerCoefficientScale h252RurOriginalLeading h252RurHCoeffs)
      (integerCoefficientScale h252RurCommonDen
        (integerCoefficientNegativeSquare h252OriginalSquaredCoeffs)) = true := by
  native_decide

open Polynomial
noncomputable section

def h252KComplex : ℂ[X] := h252K11.map (Int.castRingHom ℂ)

theorem polynomialOfCoefficientsZ_map_eval (a : List ℤ) (x : ℂ) :
    ((polynomialOfCoefficientsZ a).map (Int.castRingHom ℂ)).eval x =
      integerCoefficientEval x a := by
  induction a with
  | nil => simp [polynomialOfCoefficientsZ, integerCoefficientEval]
  | cons a as ih =>
    simpa [polynomialOfCoefficientsZ, integerCoefficientEval] using
      congrArg (fun t : ℂ ↦ (a : ℂ) + x * t) ih

theorem h252KComplex_eval (k : ℂ) :
    h252KComplex.eval k = integerCoefficientEval (k ^ 2) h252OriginalSquaredCoeffs := by
  simp only [h252KComplex, h252K11, p150K11, r102K11, p150SquaredY11,
    p150G5Y11, p150F30Y11, p150F40Y11, r102SquaredY11,
    Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, polynomialOfCoefficientsZ_map_eval,
    h252OriginalSquaredCoeffs, integerCoefficientEval_mul]

theorem h252Rur_original_eval (k : ℂ) :
    (h252RurOriginalLeading : ℂ) * h252RurComplexPolynomial.eval (Complex.I * k) =
      (h252RurCommonDen : ℂ) * h252KComplex.eval k := by
  have h := integerCoefficientEval_eq_of_equal (Complex.I * k) _ _
    h252Rur_original_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale,
    integerCoefficientNegativeSquare_eval] at h
  have hs : -(Complex.I * k) ^ 2 = k ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  simpa only [hs, h252KComplex_eval, h252RurComplexPolynomial,
    integerCoefficientPolynomial_eval] using h

theorem h252Rur_original_polynomial :
    C (h252RurOriginalLeading : ℂ) *
        h252RurComplexPolynomial.comp (C Complex.I * X) =
      C (h252RurCommonDen : ℂ) * h252KComplex := by
  apply Polynomial.funext
  intro k
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_X] using h252Rur_original_eval k

theorem h252KComplex_root_iff (k : ℂ) :
    h252KComplex.IsRoot k ↔ h252RurComplexPolynomial.IsRoot (Complex.I * k) := by
  have h := h252Rur_original_eval k
  have hL : (h252RurOriginalLeading : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurOriginalLeading_pos
  have hD : (h252RurCommonDen : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurCommonDen_pos
  change h252KComplex.eval k = 0 ↔ h252RurComplexPolynomial.eval (Complex.I * k) = 0
  constructor
  · intro hk
    rw [hk, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hL
  · intro hx
    rw [hx, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hD

/-- Nonzero linear changes of variable preserve separability. -/
theorem polynomial_separable_comp_scalar (p : ℂ[X]) (hp : p.Separable)
    (a : ℂ) (ha : a ≠ 0) : (p.comp (C a * X)).Separable := by
  obtain ⟨u, v, huv⟩ := (Polynomial.separable_def' p).mp hp
  apply (Polynomial.separable_def' _).mpr
  refine ⟨u.comp (C a * X), C a⁻¹ * v.comp (C a * X), ?_⟩
  have h := congrArg (fun t : ℂ[X] ↦ t.comp (C a * X)) huv
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.one_comp] at h
  rw [Polynomial.derivative_comp]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, mul_one, zero_add]
  calc
    _ = u.comp (C a * X) * p.comp (C a * X) +
        (C a⁻¹ * C a) * (v.comp (C a * X) * p.derivative.comp (C a * X)) := by ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]; exact h

theorem h252KComplex_separable : h252KComplex.Separable := by
  have hL : (h252RurOriginalLeading : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurOriginalLeading_pos
  have hu : IsUnit (C (h252RurOriginalLeading : ℂ)) :=
    (isUnit_iff_ne_zero.mpr hL).map C
  have hs := Polynomial.Separable.unit_mul hu
    (polynomial_separable_comp_scalar h252RurComplexPolynomial
      h252RurComplexPolynomial_separable Complex.I Complex.I_ne_zero)
  rw [h252Rur_original_polynomial] at hs
  exact hs.of_mul_right

end
end Biunimodular.F11
