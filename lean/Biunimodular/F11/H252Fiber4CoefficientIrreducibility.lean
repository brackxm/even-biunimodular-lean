/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.MonicModularConstantIrreducibility
import Biunimodular.F11.H252FiberCRTFactor4Data
import Biunimodular.F11.H252Fiber4Mod3Factor1Irreducibility
import Mathlib.Algebra.Polynomial.Eval.Irreducible

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
open Polynomial
noncomputable section
def h252Fiber4PolynomialZ : ℤ[X] := integerCoefficientEval X h252FiberCRTQ4
def h252Fiber4PolynomialQ : ℚ[X] := (h252Fiber4PolynomialZ).map (Int.castRingHom ℚ)
theorem h252Fiber4Polynomial_coefficients : h252FiberCRTQ4 = [1, 26, -375, -12850, -6906, 1368104, 4142409, -54815718, -212818474, 839205532, 3494548409, -3872363003, -16740839424, 7654817085, 44709045596, -30112515373, -55199648848, 87284009000, -34034737712, -46495037501, 95226464839, -75083478382, 9174538112, 34701903270, -29400243975, 6057684154, 5204480804, -4088566633, 859300144, 317562022, -254534434, 64054364, -1628253, -2696123, 391145, 94975, -37002, 4288, -89, -18] ++ [1] := by native_decide
theorem h252Fiber4Polynomial_monic : h252Fiber4PolynomialZ.Monic := by
  rw [h252Fiber4PolynomialZ, h252Fiber4Polynomial_coefficients]
  exact (integerCoefficientPolynomial_monic_degree _).1
theorem h252Fiber4Polynomial_degree : h252Fiber4PolynomialZ.natDegree = 40 := by
  rw [h252Fiber4PolynomialZ, h252Fiber4Polynomial_coefficients]
  exact (integerCoefficientPolynomial_monic_degree _).2
theorem h252Fiber4Polynomial_modular : (h252Fiber4PolynomialZ).map (Int.castRingHom (ZMod 3)) = h252Fiber4Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 h252FiberCRTQ4 h252Fiber4Mod3Factor1Coeffs = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  change (Polynomial.mapRingHom (Int.castRingHom (ZMod 3))) (integerCoefficientEval X h252FiberCRTQ4) = _
  rw [integerCoefficientEval_map]
  simpa only [coe_mapRingHom, map_X, integerCoefficientEval_mul, h252Fiber4Mod3Factor1] using h
theorem h252Fiber4Polynomial_irreducible_Z : Irreducible h252Fiber4PolynomialZ := by
  apply h252Fiber4Polynomial_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3))
  rw [h252Fiber4Polynomial_modular]
  exact h252Fiber4Mod3Factor1_irreducible
theorem h252Fiber4Polynomial_irreducible_Q : Irreducible h252Fiber4PolynomialQ :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast h252Fiber4Polynomial_monic.isPrimitive).mp h252Fiber4Polynomial_irreducible_Z
end
end Biunimodular.F11
