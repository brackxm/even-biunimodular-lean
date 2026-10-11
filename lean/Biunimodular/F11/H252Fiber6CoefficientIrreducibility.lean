/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.MonicModularConstantIrreducibility
import Biunimodular.F11.H252FiberCRTFactor6Data
import Biunimodular.F11.H252Fiber6Mod3Factor1Irreducibility
import Mathlib.Algebra.Polynomial.Eval.Irreducible

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
open Polynomial
noncomputable section
def h252Fiber6PolynomialZ : ℤ[X] := integerCoefficientEval X h252FiberCRTQ6
def h252Fiber6PolynomialQ : ℚ[X] := (h252Fiber6PolynomialZ).map (Int.castRingHom ℚ)
theorem h252Fiber6Polynomial_coefficients : h252FiberCRTQ6 = [1, -38, -13861, 815189, 27111078, -2519887426, 38215503634, 240482319561, -5211337318253, 4206505021081, 67315023110269, -12086618613866, -331569092214192, -178576060576942, 672376121351270, 806959819337658, -623531777996694, -1654937046966511, 6382856860688, 2271565901720269, 1108589192047414, -2200632949310719, -2290448917673280, 1327121982944807, 2850589923138013, -107386634438139, -2350324028027178, -442582000806428, 1612945318368076, 265957565028078, -1276040826067469, 265957565028078, 1612945318368076, -442582000806428, -2350324028027178, -107386634438139, 2850589923138013, 1327121982944807, -2290448917673280, -2200632949310719, 1108589192047414, 2271565901720269, 6382856860688, -1654937046966511, -623531777996694, 806959819337658, 672376121351270, -178576060576942, -331569092214192, -12086618613866, 67315023110269, 4206505021081, -5211337318253, 240482319561, 38215503634, -2519887426, 27111078, 815189, -13861, -38] ++ [1] := by native_decide
theorem h252Fiber6Polynomial_monic : h252Fiber6PolynomialZ.Monic := by
  rw [h252Fiber6PolynomialZ, h252Fiber6Polynomial_coefficients]
  exact (integerCoefficientPolynomial_monic_degree _).1
theorem h252Fiber6Polynomial_degree : h252Fiber6PolynomialZ.natDegree = 60 := by
  rw [h252Fiber6PolynomialZ, h252Fiber6Polynomial_coefficients]
  exact (integerCoefficientPolynomial_monic_degree _).2
theorem h252Fiber6Polynomial_modular : (h252Fiber6PolynomialZ).map (Int.castRingHom (ZMod 3)) = h252Fiber6Mod3Factor1 := by
  have hc : integerCoefficientEqualMod 3 h252FiberCRTQ6 h252Fiber6Mod3Factor1Coeffs = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  change (Polynomial.mapRingHom (Int.castRingHom (ZMod 3))) (integerCoefficientEval X h252FiberCRTQ6) = _
  rw [integerCoefficientEval_map]
  simpa only [coe_mapRingHom, map_X, integerCoefficientEval_mul, h252Fiber6Mod3Factor1] using h
theorem h252Fiber6Polynomial_irreducible_Z : Irreducible h252Fiber6PolynomialZ := by
  apply h252Fiber6Polynomial_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3))
  rw [h252Fiber6Polynomial_modular]
  exact h252Fiber6Mod3Factor1_irreducible
theorem h252Fiber6Polynomial_irreducible_Q : Irreducible h252Fiber6PolynomialQ :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast h252Fiber6Polynomial_monic.isPrimitive).mp h252Fiber6Polynomial_irreducible_Z
end
end Biunimodular.F11
