/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorQ80MonicIrreducibility
import Biunimodular.F11.IntegerCoefficientRescale
import Biunimodular.F11.IntegerCoefficientPolynomialNaturality

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
open Polynomial

def bSectorG40LeadingScale : ℤ := 23 ^ 10

theorem bSectorG40_original_coefficients :
    integerCoefficientEqual
      (integerCoefficientScale (bSectorG40LeadingScale ^ 39) p150F40Coeffs11)
      (integerCoefficientRescale (4 * bSectorG40LeadingScale) bSectorG40MonicCoeffs) = true := by
  native_decide

noncomputable section

theorem bSectorG40_original_polynomial :
    C (bSectorG40LeadingScale ^ 39 : ℚ) * p150F40Y11.map (Int.castRingHom ℚ) =
      (bSectorG40Monic.map (Int.castRingHom ℚ)).comp
        (C (4 * bSectorG40LeadingScale : ℚ) * X) := by
  have h := integerCoefficientEval_eq_of_equal (X : ℚ[X]) _ _ bSectorG40_original_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientRescale_eval] at h
  have hcast (a : ℤ) : (a : ℚ[X]) = C (a : ℚ) := by simp
  simp only [hcast, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] at h
  simp only [p150F40Y11, polynomialOfCoefficientsZ_eq_integerCoefficient,
    bSectorG40Monic, integerCoefficientPolynomial_map, integerCoefficientPolynomial_comp]
  exact h

/-- The the degree-eighty phase coordinate factor. -/
def p150Q80KQ11 : ℚ[X] := (p150F40Y11.comp (X ^ 2)).map (Int.castRingHom ℚ)

theorem p150Q80KQ11_eq_scaled_G80 :
    C (bSectorG40LeadingScale ^ 39 : ℚ) * p150Q80KQ11 =
      (bSectorG80Monic.map (Int.castRingHom ℚ)).comp (C (2 * 23 ^ 5 : ℚ) * X) := by
  have h := congrArg (fun p : ℚ[X] ↦ p.comp (X ^ 2)) bSectorG40_original_polynomial
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc] at h
  rw [p150Q80KQ11, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  rw [h]
  simp only [bSectorG80Monic, Polynomial.map_comp, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.X_comp,
    Polynomial.pow_comp, mul_pow, ← C_pow]
  norm_num [bSectorG40LeadingScale]

theorem p150Q80KQ11_irreducible : Irreducible p150Q80KQ11 := by
  let s : ℚ := 2 * 23 ^ 5
  have hs : s ≠ 0 := by norm_num [s]
  let := invertibleOfNonzero hs
  let e := Polynomial.algEquivCMulXAddC s 0
  have hi := (MulEquiv.irreducible_iff e).mpr bSectorG80Monic_irreducible_Q
  have hscaled : Irreducible (C (bSectorG40LeadingScale ^ 39 : ℚ) * p150Q80KQ11) := by
    rw [p150Q80KQ11_eq_scaled_G80]
    simpa only [e, s, Polynomial.algEquivCMulXAddC_apply, Polynomial.C_0, add_zero,
      ← Polynomial.comp_eq_aeval] using hi
  have hu : IsUnit (C (bSectorG40LeadingScale ^ 39 : ℚ)) := by
    apply IsUnit.map C
    exact isUnit_iff_ne_zero.mpr (by norm_num [bSectorG40LeadingScale])
  exact (irreducible_isUnit_mul hu).mp hscaled

end
end Biunimodular.F11
