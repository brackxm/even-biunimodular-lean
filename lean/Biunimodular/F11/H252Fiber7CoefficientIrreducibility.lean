/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7MonicTransform
import Biunimodular.F11.MonicModularConstantConstraints
import Biunimodular.F11.PrimePowerDivisorModularConstants
import Biunimodular.F11.H252Fiber7Mod163Factor1Irreducibility
import Biunimodular.F11.H252Fiber7Mod163Factor2Irreducibility

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
open Polynomial
noncomputable section
def h252Fiber7PolynomialZ : ℤ[X] := integerCoefficientEval X h252Fiber7MonicCoeffs
def h252Fiber7PolynomialQ : ℚ[X] := (h252Fiber7PolynomialZ).map (Int.castRingHom ℚ)
theorem h252Fiber7Polynomial_monic : h252Fiber7PolynomialZ.Monic := (integerCoefficientPolynomial_monic_degree _).1
theorem h252Fiber7Polynomial_degree : h252Fiber7PolynomialZ.natDegree = 80 := (integerCoefficientPolynomial_monic_degree _).2
set_option exponentiation.threshold 400 in
theorem h252Fiber7Polynomial_constant : h252Fiber7PolynomialZ.coeff 0 = (23:ℤ)^400 := by
  norm_num [h252Fiber7PolynomialZ, h252Fiber7MonicCoeffs, integerCoefficientEval]
theorem h252Fiber7Polynomial_modular : (h252Fiber7PolynomialZ).map (Int.castRingHom (ZMod 163)) = h252Fiber7Mod163Factor1*h252Fiber7Mod163Factor2 := by
  have hc : integerCoefficientEqualMod 163 h252Fiber7MonicCoeffs
      (integerCoefficientMul h252Fiber7Mod163Factor1Coeffs h252Fiber7Mod163Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  change (Polynomial.mapRingHom (Int.castRingHom (ZMod 163)))
    (integerCoefficientEval X h252Fiber7MonicCoeffs) = _
  rw [integerCoefficientEval_map]
  simpa only [coe_mapRingHom, Polynomial.map_X, integerCoefficientEval_mul, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor2] using h
theorem h252Fiber7Polynomial_irreducible_Z : Irreducible h252Fiber7PolynomialZ := by
  apply monic_irreducible_of_two_modular_constant_constraints (h252Fiber7PolynomialZ) h252Fiber7Polynomial_monic
    40 163 (by decide) h252Fiber7Polynomial_degree h252Fiber7Mod163Factor1 h252Fiber7Mod163Factor2
    ⟨h252Fiber7Mod163Factor1_monic, h252Fiber7Mod163Factor1_irreducible⟩ ⟨h252Fiber7Mod163Factor2_monic, h252Fiber7Mod163Factor2_irreducible⟩
    h252Fiber7Mod163Factor1_degree h252Fiber7Mod163Factor2_degree (fun c => c^18 = 1)
  · intro g hgm hg
    obtain ⟨r,hr⟩ := hg
    have hprod : g.coeff 0 * r.coeff 0 = (23:ℤ)^400 := by
      rw [← Polynomial.mul_coeff_zero, ← hr, h252Fiber7Polynomial_constant]
    have hdiv : g.coeff 0 ∣ (23:ℤ)^400 := ⟨r.coeff 0,hprod.symm⟩
    have h := primePowerDivisor_modular_power 23 400 163 18 (by decide) (by decide) (by decide) _ hdiv
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using h
  · norm_num [h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1Coeffs, integerCoefficientEval]; decide
  · norm_num [h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2Coeffs, integerCoefficientEval]; decide
  · exact h252Fiber7Polynomial_modular
theorem h252Fiber7Polynomial_irreducible_Q : Irreducible h252Fiber7PolynomialQ :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast h252Fiber7Polynomial_monic.isPrimitive).mp h252Fiber7Polynomial_irreducible_Z
end

end Biunimodular.F11
