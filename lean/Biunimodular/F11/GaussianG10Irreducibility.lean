/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.P150PolynomialData11
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial
noncomputable section

def gaussianG10Monic : ℤ[X] := X ^ 10 - 11 * X ^ 8 + 44 * X ^ 6 - 77 * X ^ 4 + 55 * X ^ 2 - 11

theorem gaussianG10Monic_monic : gaussianG10Monic.Monic := by
  have hlow : (-11 * X ^ 8 + 44 * X ^ 6 - 77 * X ^ 4 + 55 * X ^ 2 - 11 : ℤ[X]).degree < 10 := by
    compute_degree; norm_num
  convert monic_X_pow_add hlow using 1; simp only [gaussianG10Monic]; ring

theorem gaussianG10Monic_natDegree : gaussianG10Monic.natDegree = 10 := by
  simp only [gaussianG10Monic]
  compute_degree <;> norm_num

theorem gaussianG10Monic_irreducible : Irreducible gaussianG10Monic := by
  let P : Ideal ℤ := Ideal.span {11}
  apply Polynomial.irreducible_of_eisenstein_criterion (P := P)
  · exact (Ideal.span_singleton_prime (by norm_num : (11 : ℤ) ≠ 0)).mpr (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 11))
  · rw [gaussianG10Monic_monic.leadingCoeff]
    norm_num [P, Ideal.mem_span_singleton]
  · intro n hn
    have hlt : n < 10 := by
      have hdeg : gaussianG10Monic.degree = 10 :=
        (degree_eq_natDegree gaussianG10Monic_monic.ne_zero).trans
          (by rw [gaussianG10Monic_natDegree]; norm_num)
      rw [hdeg] at hn
      exact_mod_cast hn
    interval_cases n <;> norm_num [gaussianG10Monic, P, Ideal.mem_span_singleton, coeff_mul]
  · rw [← natDegree_pos_iff_degree_pos]
    rw [gaussianG10Monic_natDegree]
    norm_num
  · rw [Ideal.span_singleton_pow]
    norm_num [P, gaussianG10Monic, Ideal.mem_span_singleton, coeff_mul]
  · exact gaussianG10Monic_monic.isPrimitive

def p150G10KQ11 : ℚ[X] := (p150G5Y11.comp (X ^ 2)).map (Int.castRingHom ℚ)

theorem p150G10KQ11_eq_scaled_monic :
    p150G10KQ11 = (gaussianG10Monic.map (Int.castRingHom ℚ)).comp (C 2 * X) := by
  norm_num [p150G10KQ11, p150G5Y11, polynomialOfCoefficientsZ,
    p150G5Coeffs11, gaussianG10Monic]
  simp only [map_ofNat]
  ring

theorem p150G10KQ11_irreducible : Irreducible p150G10KQ11 := by
  have hi : Irreducible (gaussianG10Monic.map (Int.castRingHom ℚ)) :=
    (gaussianG10Monic_monic.irreducible_iff_irreducible_map_fraction_map).mp
      gaussianG10Monic_irreducible
  let := invertibleOfNonzero (by norm_num : (2 : ℚ) ≠ 0)
  let e := Polynomial.algEquivCMulXAddC (2 : ℚ) 0
  have h := (MulEquiv.irreducible_iff e).mpr hi
  simpa only [e, Polynomial.algEquivCMulXAddC_apply, Polynomial.C_0, add_zero,
    ← Polynomial.comp_eq_aeval, ← p150G10KQ11_eq_scaled_monic] using h

end
end Biunimodular.F11
