/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientDegree
import Biunimodular.F11.IntegerCoefficientRescale
import Biunimodular.F11.H252OriginalPolynomialBridge

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial
noncomputable section

theorem p150G5Y11_nonzero_degree : p150G5Y11 ≠ 0 ∧ p150G5Y11.natDegree = 5 := by
  have hlist : p150G5Coeffs11.take 5 ++ [(Int.ofNat 1024)] = p150G5Coeffs11 := by native_decide
  have hc : (1024 : ℤ) ≠ 0 := by native_decide
  have h := integerCoefficientPolynomial_append_degree (R := ℤ) (p150G5Coeffs11.take 5) (Int.ofNat 1024) hc
  rw [hlist] at h
  have hlen : (p150G5Coeffs11.take 5).length = 5 := by native_decide
  simpa only [p150G5Y11, polynomialOfCoefficientsZ_eq_integerCoefficient, hlen] using h

theorem p150F30Y11_nonzero_degree : p150F30Y11 ≠ 0 ∧ p150F30Y11.natDegree = 30 := by
  have hlist : p150F30Coeffs11.take 30 ++ [(Int.ofNat 1152921504606846976)] = p150F30Coeffs11 := by native_decide
  have hc : (1152921504606846976 : ℤ) ≠ 0 := by native_decide
  have h := integerCoefficientPolynomial_append_degree (R := ℤ) (p150F30Coeffs11.take 30) (Int.ofNat 1152921504606846976) hc
  rw [hlist] at h
  have hlen : (p150F30Coeffs11.take 30).length = 30 := by native_decide
  simpa only [p150F30Y11, polynomialOfCoefficientsZ_eq_integerCoefficient, hlen] using h

theorem p150F40Y11_nonzero_degree : p150F40Y11 ≠ 0 ∧ p150F40Y11.natDegree = 40 := by
  have hlist : p150F40Coeffs11.take 40 ++ [(Int.ofNat 50081579022735243701732230378735796224)] = p150F40Coeffs11 := by native_decide
  have hc : (50081579022735243701732230378735796224 : ℤ) ≠ 0 := by native_decide
  have h := integerCoefficientPolynomial_append_degree (R := ℤ) (p150F40Coeffs11.take 40) (Int.ofNat 50081579022735243701732230378735796224) hc
  rw [hlist] at h
  have hlen : (p150F40Coeffs11.take 40).length = 40 := by native_decide
  simpa only [p150F40Y11, polynomialOfCoefficientsZ_eq_integerCoefficient, hlen] using h

theorem r102SquaredY11_nonzero_degree : r102SquaredY11 ≠ 0 ∧ r102SquaredY11.natDegree = 51 := by
  have hlist : r102SquaredCoeffs11.take 51 ++ [(Int.ofNat 316912650057057350374175801344)] = r102SquaredCoeffs11 := by native_decide
  have hc : (316912650057057350374175801344 : ℤ) ≠ 0 := by native_decide
  have h := integerCoefficientPolynomial_append_degree (R := ℤ) (r102SquaredCoeffs11.take 51) (Int.ofNat 316912650057057350374175801344) hc
  rw [hlist] at h
  have hlen : (r102SquaredCoeffs11.take 51).length = 51 := by native_decide
  simpa only [r102SquaredY11, polynomialOfCoefficientsZ_eq_integerCoefficient, hlen] using h

theorem p150SquaredY11_nonzero_degree :
    p150SquaredY11 ≠ 0 ∧ p150SquaredY11.natDegree = 75 := by
  have h1 := p150G5Y11_nonzero_degree
  have h2 := p150F30Y11_nonzero_degree
  have h3 := p150F40Y11_nonzero_degree
  refine ⟨mul_ne_zero (mul_ne_zero h1.1 h2.1) h3.1, ?_⟩
  simp only [p150SquaredY11, natDegree_mul h1.1 h2.1,
    natDegree_mul (mul_ne_zero h1.1 h2.1) h3.1, h1.2, h2.2, h3.2]

theorem p150K11_degree : p150K11.natDegree = 150 := by
  rw [p150K11, natDegree_comp, p150SquaredY11_nonzero_degree.2, natDegree_X_pow]

theorem r102K11_degree : r102K11.natDegree = 102 := by
  rw [r102K11, natDegree_comp, r102SquaredY11_nonzero_degree.2, natDegree_X_pow]

theorem h252K11_degree : h252K11.natDegree = 252 := by
  have hp : p150K11 ≠ 0 := by
    intro h
    have hd := p150K11_degree
    rw [h, natDegree_zero] at hd
    omega
  have hr : r102K11 ≠ 0 := by
    intro h
    have hd := r102K11_degree
    rw [h, natDegree_zero] at hd
    omega
  rw [h252K11, natDegree_mul hp hr, p150K11_degree, r102K11_degree]

theorem h252KComplex_even (k : ℂ) :
    h252KComplex.eval (-k) = h252KComplex.eval k := by
  simp [h252KComplex, h252K11, p150K11, r102K11, Polynomial.map_comp,
    Polynomial.eval_comp]

end
end Biunimodular.F11
