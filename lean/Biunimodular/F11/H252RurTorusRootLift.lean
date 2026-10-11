/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurIdentity1
import Biunimodular.F11.H252RurIdentity2
import Biunimodular.F11.H252RurIdentity3
import Biunimodular.F11.H252RurIdentity4
import Biunimodular.F11.H252RurIdentity5
import Biunimodular.F11.H252RurIdentity6
import Biunimodular.F11.H252RurIdentity7
import Biunimodular.F11.H252RurSeparable
import Biunimodular.F11.H252PhaseElimination11

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

noncomputable section

theorem h252RurQ1Den_pos : 0 < h252RurQ1Den := by native_decide

theorem h252RurP1_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    integerCoefficientEval x h252RurP1Coeffs = 0 := by
  have hx0 : integerCoefficientEval x h252RurHCoeffs = 0 := by
    simpa [h252RurComplexPolynomial, integerCoefficientPolynomial_eval] using hx
  have h := integerCoefficientEval_eq_of_equal x _ _ h252RurIdentity1_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale,
    integerCoefficientEval_mul, hx0, mul_zero, mul_zero] at h
  have hd : (h252RurQ1Den : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurQ1Den_pos
  exact (mul_eq_zero.mp h).resolve_left hd

theorem h252RurQ2Den_pos : 0 < h252RurQ2Den := by native_decide

theorem h252RurP2_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    integerCoefficientEval x h252RurP2Coeffs = 0 := by
  have hx0 : integerCoefficientEval x h252RurHCoeffs = 0 := by
    simpa [h252RurComplexPolynomial, integerCoefficientPolynomial_eval] using hx
  have h := integerCoefficientEval_eq_of_equal x _ _ h252RurIdentity2_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale,
    integerCoefficientEval_mul, hx0, mul_zero, mul_zero] at h
  have hd : (h252RurQ2Den : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurQ2Den_pos
  exact (mul_eq_zero.mp h).resolve_left hd

theorem h252RurQ3Den_pos : 0 < h252RurQ3Den := by native_decide

theorem h252RurP3_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    integerCoefficientEval x h252RurP3Coeffs = 0 := by
  have hx0 : integerCoefficientEval x h252RurHCoeffs = 0 := by
    simpa [h252RurComplexPolynomial, integerCoefficientPolynomial_eval] using hx
  have h := integerCoefficientEval_eq_of_equal x _ _ h252RurIdentity3_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale,
    integerCoefficientEval_mul, hx0, mul_zero, mul_zero] at h
  have hd : (h252RurQ3Den : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurQ3Den_pos
  exact (mul_eq_zero.mp h).resolve_left hd

theorem h252RurQ4Den_pos : 0 < h252RurQ4Den := by native_decide

theorem h252RurP4_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    integerCoefficientEval x h252RurP4Coeffs = 0 := by
  have hx0 : integerCoefficientEval x h252RurHCoeffs = 0 := by
    simpa [h252RurComplexPolynomial, integerCoefficientPolynomial_eval] using hx
  have h := integerCoefficientEval_eq_of_equal x _ _ h252RurIdentity4_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale,
    integerCoefficientEval_mul, hx0, mul_zero, mul_zero] at h
  have hd : (h252RurQ4Den : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurQ4Den_pos
  exact (mul_eq_zero.mp h).resolve_left hd

theorem h252RurQ5Den_pos : 0 < h252RurQ5Den := by native_decide

theorem h252RurP5_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    integerCoefficientEval x h252RurP5Coeffs = 0 := by
  have hx0 : integerCoefficientEval x h252RurHCoeffs = 0 := by
    simpa [h252RurComplexPolynomial, integerCoefficientPolynomial_eval] using hx
  have h := integerCoefficientEval_eq_of_equal x _ _ h252RurIdentity5_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale,
    integerCoefficientEval_mul, hx0, mul_zero, mul_zero] at h
  have hd : (h252RurQ5Den : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurQ5Den_pos
  exact (mul_eq_zero.mp h).resolve_left hd

theorem h252RurQ6Den_pos : 0 < h252RurQ6Den := by native_decide

theorem h252RurP6_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    integerCoefficientEval x h252RurP6Coeffs = 0 := by
  have hx0 : integerCoefficientEval x h252RurHCoeffs = 0 := by
    simpa [h252RurComplexPolynomial, integerCoefficientPolynomial_eval] using hx
  have h := integerCoefficientEval_eq_of_equal x _ _ h252RurIdentity6_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale,
    integerCoefficientEval_mul, hx0, mul_zero, mul_zero] at h
  have hd : (h252RurQ6Den : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurQ6Den_pos
  exact (mul_eq_zero.mp h).resolve_left hd

theorem h252RurQ7Den_pos : 0 < h252RurQ7Den := by native_decide

theorem h252RurP7_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    integerCoefficientEval x h252RurP7Coeffs = 0 := by
  have hx0 : integerCoefficientEval x h252RurHCoeffs = 0 := by
    simpa [h252RurComplexPolynomial, integerCoefficientPolynomial_eval] using hx
  have h := integerCoefficientEval_eq_of_equal x _ _ h252RurIdentity7_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale,
    integerCoefficientEval_mul, hx0, mul_zero, mul_zero] at h
  have hd : (h252RurQ7Den : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurQ7Den_pos
  exact (mul_eq_zero.mp h).resolve_left hd

theorem h252RurF1_homogeneous (n1 n2 n3 n4 n5 d : ℂ)
    (hd : d ≠ 0) :
    d ^ 6 * h252TorusF1 (n1 / d) (n2 / d) (n3 / d) (n4 / d) (n5 / d) =
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 2 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 +
      (1) * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 2 +
      (1) * (n1) ^ 2 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n2) ^ 2 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 2 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n3) ^ 2 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 2 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n4) ^ 2 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 2 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n5) ^ 2 * (d) ^ 1 := by
  simp only [h252TorusF1]
  field_simp [hd]
  ring

theorem h252RurF1_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    h252TorusF1 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) = 0 := by
  have hd : integerCoefficientEval x h252RurDCoeffs ≠ 0 := h252RurDenominator_ne_zero x hx
  have he : integerCoefficientEval x h252RurP1Coeffs =
      (integerCoefficientEval x h252RurDCoeffs) ^ 6 * h252TorusF1 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) := by
    simp only [h252RurP1Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
      integerCoefficientEval_mul, integerCoefficientEval_pow,
      integerCoefficientEval_singleton,
      Int.cast_one,  add_zero]
    calc
      _ = (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 2 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 := by ring
      _ = _ := (h252RurF1_homogeneous _ _ _ _ _ _ hd).symm
  have hzero := h252RurP1_zero x hx
  rw [he] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 6 hd)

theorem h252RurF2_homogeneous (n1 n2 n3 n4 n5 d : ℂ)
    (hd : d ≠ 0) :
    d ^ 6 * h252TorusF2 (n1 / d) (n2 / d) (n3 / d) (n4 / d) (n5 / d) =
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 2 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 +
      (1) * (n1) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 2 +
      (1) * (n1) ^ 2 * (n2) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n2) ^ 1 * (n3) ^ 2 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 2 * (n3) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n3) ^ 1 * (n4) ^ 2 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 2 * (n4) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n4) ^ 1 * (n5) ^ 2 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 2 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n5) ^ 2 * (d) ^ 1 := by
  simp only [h252TorusF2]
  field_simp [hd]
  ring

theorem h252RurF2_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    h252TorusF2 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) = 0 := by
  have hd : integerCoefficientEval x h252RurDCoeffs ≠ 0 := h252RurDenominator_ne_zero x hx
  have he : integerCoefficientEval x h252RurP2Coeffs =
      (integerCoefficientEval x h252RurDCoeffs) ^ 6 * h252TorusF2 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) := by
    simp only [h252RurP2Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
      integerCoefficientEval_mul, integerCoefficientEval_pow,
      integerCoefficientEval_singleton,
      Int.cast_one,  add_zero]
    calc
      _ = (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 2 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 := by ring
      _ = _ := (h252RurF2_homogeneous _ _ _ _ _ _ hd).symm
  have hzero := h252RurP2_zero x hx
  rw [he] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 6 hd)

theorem h252RurF3_homogeneous (n1 n2 n3 n4 n5 d : ℂ)
    (hd : d ≠ 0) :
    d ^ 6 * h252TorusF3 (n1 / d) (n2 / d) (n3 / d) (n4 / d) (n5 / d) =
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 2 * (n4) ^ 1 * (n5) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 2 +
      (1) * (n1) ^ 2 * (n2) ^ 1 * (n3) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 2 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 2 * (n3) ^ 1 * (n4) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 2 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 2 * (n4) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n4) ^ 1 * (n5) ^ 2 * (d) ^ 1 +
      (1) * (n1) ^ 2 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n2) ^ 2 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 := by
  simp only [h252TorusF3]
  field_simp [hd]
  ring

theorem h252RurF3_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    h252TorusF3 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) = 0 := by
  have hd : integerCoefficientEval x h252RurDCoeffs ≠ 0 := h252RurDenominator_ne_zero x hx
  have he : integerCoefficientEval x h252RurP3Coeffs =
      (integerCoefficientEval x h252RurDCoeffs) ^ 6 * h252TorusF3 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) := by
    simp only [h252RurP3Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
      integerCoefficientEval_mul, integerCoefficientEval_pow,
      integerCoefficientEval_singleton,
      Int.cast_one,  add_zero]
    calc
      _ = (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 2 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 := by ring
      _ = _ := (h252RurF3_homogeneous _ _ _ _ _ _ hd).symm
  have hzero := h252RurP3_zero x hx
  rw [he] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 6 hd)

theorem h252RurF4_homogeneous (n1 n2 n3 n4 n5 d : ℂ)
    (hd : d ≠ 0) :
    d ^ 6 * h252TorusF4 (n1 / d) (n2 / d) (n3 / d) (n4 / d) (n5 / d) =
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 2 * (n5) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n5) ^ 1 * (d) ^ 2 +
      (1) * (n1) ^ 2 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (d) ^ 1 +
      (1) * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 2 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 2 * (n3) ^ 1 * (n4) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 2 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 2 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n4) ^ 2 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 2 * (n2) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n2) ^ 1 * (n3) ^ 2 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 := by
  simp only [h252TorusF4]
  field_simp [hd]
  ring

theorem h252RurF4_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    h252TorusF4 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) = 0 := by
  have hd : integerCoefficientEval x h252RurDCoeffs ≠ 0 := h252RurDenominator_ne_zero x hx
  have he : integerCoefficientEval x h252RurP4Coeffs =
      (integerCoefficientEval x h252RurDCoeffs) ^ 6 * h252TorusF4 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) := by
    simp only [h252RurP4Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
      integerCoefficientEval_mul, integerCoefficientEval_pow,
      integerCoefficientEval_singleton,
      Int.cast_one,  add_zero]
    calc
      _ = (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 2 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 := by ring
      _ = _ := (h252RurF4_homogeneous _ _ _ _ _ _ hd).symm
  have hzero := h252RurP4_zero x hx
  rw [he] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 6 hd)

theorem h252RurF5_homogeneous (n1 n2 n3 n4 n5 d : ℂ)
    (hd : d ≠ 0) :
    d ^ 6 * h252TorusF5 (n1 / d) (n2 / d) (n3 / d) (n4 / d) (n5 / d) =
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 2 +
      (1) * (n1) ^ 1 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (d) ^ 2 +
      (1) * (n1) ^ 2 * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (d) ^ 1 +
      (1) * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 1 * (n5) ^ 2 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 2 * (n3) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n3) ^ 1 * (n4) ^ 2 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 2 * (n2) ^ 1 * (n3) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n2) ^ 1 * (n3) ^ 1 * (n4) ^ 2 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n2) ^ 2 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 +
      (1) * (n1) ^ 1 * (n3) ^ 2 * (n4) ^ 1 * (n5) ^ 1 * (d) ^ 1 := by
  simp only [h252TorusF5]
  field_simp [hd]
  ring

theorem h252RurF5_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    h252TorusF5 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) = 0 := by
  have hd : integerCoefficientEval x h252RurDCoeffs ≠ 0 := h252RurDenominator_ne_zero x hx
  have he : integerCoefficientEval x h252RurP5Coeffs =
      (integerCoefficientEval x h252RurDCoeffs) ^ 6 * h252TorusF5 (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) := by
    simp only [h252RurP5Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
      integerCoefficientEval_mul, integerCoefficientEval_pow,
      integerCoefficientEval_singleton,
      Int.cast_one,  add_zero]
    calc
      _ = (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 2 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 2 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 2 * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN2Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 1 * (integerCoefficientEval x h252RurN4Coeffs) ^ 2 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN2Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 +
      (1) * (integerCoefficientEval x h252RurN1Coeffs) ^ 1 * (integerCoefficientEval x h252RurN3Coeffs) ^ 2 * (integerCoefficientEval x h252RurN4Coeffs) ^ 1 * (integerCoefficientEval x h252RurN5Coeffs) ^ 1 * (integerCoefficientEval x h252RurDCoeffs) ^ 1 := by ring
      _ = _ := (h252RurF5_homogeneous _ _ _ _ _ _ hd).symm
  have hzero := h252RurP5_zero x hx
  rw [he] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 6 hd)

theorem h252RurCoordinate_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) ^ 2 - 2 * x * (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) - 1 = 0 := by
  have hd : integerCoefficientEval x h252RurDCoeffs ≠ 0 := h252RurDenominator_ne_zero x hx
  have he : integerCoefficientEval x h252RurP6Coeffs =
      (integerCoefficientEval x h252RurN5Coeffs) ^ 2 - 2 * x * (integerCoefficientEval x h252RurN5Coeffs) * (integerCoefficientEval x h252RurDCoeffs) - (integerCoefficientEval x h252RurDCoeffs) ^ 2 := by
    simp only [h252RurP6Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
      integerCoefficientEval_mul, integerCoefficientEval_pow,
      integerCoefficientEval_singleton, integerCoefficientEval_variable,
      Int.cast_one, Int.cast_neg, Int.cast_ofNat, add_zero]
    ring
  calc
    _ = integerCoefficientEval x h252RurP6Coeffs / (integerCoefficientEval x h252RurDCoeffs) ^ 2 := by
      rw [he]
      field_simp [hd]
    _ = 0 := by rw [h252RurP6_zero x hx]; simp

theorem h252RurSaturation_zero (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    (integerCoefficientEval x h252RurN6Coeffs / integerCoefficientEval x h252RurDCoeffs) *
      (integerCoefficientEval x h252RurN1Coeffs / integerCoefficientEval x h252RurDCoeffs) * (integerCoefficientEval x h252RurN2Coeffs / integerCoefficientEval x h252RurDCoeffs) * (integerCoefficientEval x h252RurN3Coeffs / integerCoefficientEval x h252RurDCoeffs) * (integerCoefficientEval x h252RurN4Coeffs / integerCoefficientEval x h252RurDCoeffs) * (integerCoefficientEval x h252RurN5Coeffs / integerCoefficientEval x h252RurDCoeffs) - 1 = 0 := by
  have hd : integerCoefficientEval x h252RurDCoeffs ≠ 0 := h252RurDenominator_ne_zero x hx
  have he : integerCoefficientEval x h252RurP7Coeffs =
      (integerCoefficientEval x h252RurN6Coeffs) * (integerCoefficientEval x h252RurN1Coeffs) * (integerCoefficientEval x h252RurN2Coeffs) * (integerCoefficientEval x h252RurN3Coeffs) * (integerCoefficientEval x h252RurN4Coeffs) * (integerCoefficientEval x h252RurN5Coeffs) - (integerCoefficientEval x h252RurDCoeffs) ^ 6 := by
    simp only [h252RurP7Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, integerCoefficientEval_scale,
      integerCoefficientEval_mul, integerCoefficientEval_pow,
      integerCoefficientEval_singleton,
      Int.cast_one, Int.cast_neg,  add_zero]
    ring
  calc
    _ = integerCoefficientEval x h252RurP7Coeffs / (integerCoefficientEval x h252RurDCoeffs) ^ 6 := by
      rw [he]
      field_simp [hd]
    _ = 0 := by rw [h252RurP7_zero x hx]; simp

end

end Biunimodular.F11
