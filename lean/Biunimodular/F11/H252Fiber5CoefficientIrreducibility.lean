/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.MonicModularConstantIrreducibility
import Biunimodular.F11.H252FiberCRTFactor5Data
import Biunimodular.F11.H252Fiber5Mod3Factor1Irreducibility
import Mathlib.Algebra.Polynomial.Eval.Irreducible

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
open Polynomial
noncomputable section
def h252Fiber5PolynomialZ : ℤ[X] := integerCoefficientEval X h252FiberCRTQ5
def h252Fiber5PolynomialQ : ℚ[X] := (h252Fiber5PolynomialZ).map (Int.castRingHom ℚ)
theorem h252Fiber5Polynomial_coefficients : h252FiberCRTQ5 = [1, -18, -89, 4288, -37002, 94975, 391145, -2696123, -1628253, 64054364, -254534434, 317562022, 859300144, -4088566633, 5204480804, 6057684154, -29400243975, 34701903270, 9174538112, -75083478382, 95226464839, -46495037501, -34034737712, 87284009000, -55199648848, -30112515373, 44709045596, 7654817085, -16740839424, -3872363003, 3494548409, 839205532, -212818474, -54815718, 4142409, 1368104, -6906, -12850, -375, 26] ++ [1] := by native_decide
theorem h252Fiber5Polynomial_monic : h252Fiber5PolynomialZ.Monic := by
  rw [h252Fiber5PolynomialZ, h252Fiber5Polynomial_coefficients]
  exact (integerCoefficientPolynomial_monic_degree _).1
theorem h252Fiber5Polynomial_degree : h252Fiber5PolynomialZ.natDegree = 40 := by
  rw [h252Fiber5PolynomialZ, h252Fiber5Polynomial_coefficients]
  exact (integerCoefficientPolynomial_monic_degree _).2
theorem h252Fiber5Polynomial_modular : (h252Fiber5PolynomialZ).map (Int.castRingHom (ZMod 3)) = h252Fiber5Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 h252FiberCRTQ5 h252Fiber5Mod3Factor1Coeffs = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  change (Polynomial.mapRingHom (Int.castRingHom (ZMod 3))) (integerCoefficientEval X h252FiberCRTQ5) = _
  rw [integerCoefficientEval_map]
  simpa only [coe_mapRingHom, map_X, integerCoefficientEval_mul, h252Fiber5Mod3Factor1] using h
theorem h252Fiber5Polynomial_irreducible_Z : Irreducible h252Fiber5PolynomialZ := by
  apply h252Fiber5Polynomial_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3))
  rw [h252Fiber5Polynomial_modular]
  exact h252Fiber5Mod3Factor1_irreducible
theorem h252Fiber5Polynomial_irreducible_Q : Irreducible h252Fiber5PolynomialQ :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast h252Fiber5Polynomial_monic.isPrimitive).mp h252Fiber5Polynomial_irreducible_Z
end
end Biunimodular.F11
