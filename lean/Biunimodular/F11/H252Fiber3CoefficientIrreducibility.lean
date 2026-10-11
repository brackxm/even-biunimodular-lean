/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.MonicModularConstantIrreducibility
import Biunimodular.F11.H252FiberCRTFactor3Data
import Biunimodular.F11.H252Fiber3Mod29Factor1Irreducibility
import Biunimodular.F11.H252Fiber3Mod29Factor2Irreducibility
import Mathlib.Algebra.Polynomial.Eval.Irreducible

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
open Polynomial
noncomputable section
def h252Fiber3PolynomialZ : ℤ[X] := integerCoefficientEval X h252FiberCRTQ3
def h252Fiber3PolynomialQ : ℚ[X] := (h252Fiber3PolynomialZ).map (Int.castRingHom ℚ)
theorem h252Fiber3Polynomial_coefficients : h252FiberCRTQ3 = [1, 2, 3, -117, 1072, -1666, -356, -1686, 15376, 27719, 43208, 27719, 15376, -1686, -356, -1666, 1072, -117, 3, 2] ++ [1] := by native_decide
theorem h252Fiber3Polynomial_monic : h252Fiber3PolynomialZ.Monic := by
  rw [h252Fiber3PolynomialZ, h252Fiber3Polynomial_coefficients]
  exact (integerCoefficientPolynomial_monic_degree _).1
theorem h252Fiber3Polynomial_degree : h252Fiber3PolynomialZ.natDegree = 20 := by
  rw [h252Fiber3PolynomialZ, h252Fiber3Polynomial_coefficients]
  exact (integerCoefficientPolynomial_monic_degree _).2
theorem h252Fiber3Polynomial_modular : (h252Fiber3PolynomialZ).map (Int.castRingHom (ZMod 29)) = h252Fiber3Mod29Factor1*h252Fiber3Mod29Factor2 := by
  have hc : integerCoefficientEqualMod 29 h252FiberCRTQ3 (integerCoefficientMul h252Fiber3Mod29Factor1Coeffs h252Fiber3Mod29Factor2Coeffs) = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  change (Polynomial.mapRingHom (Int.castRingHom (ZMod 29))) (integerCoefficientEval X h252FiberCRTQ3) = _
  rw [integerCoefficientEval_map]
  simpa only [coe_mapRingHom, map_X, integerCoefficientEval_mul, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor2] using h
theorem h252Fiber3Polynomial_irreducible_Z : Irreducible h252Fiber3PolynomialZ := by
  apply monic_irreducible_of_two_modular_constants (h252Fiber3PolynomialZ) h252Fiber3Polynomial_monic (by
    simp [h252Fiber3PolynomialZ, h252FiberCRTQ3, h252FiberCRTQ3Part001, integerCoefficientEval]) 10 29 (by decide) h252Fiber3Polynomial_degree h252Fiber3Mod29Factor1 h252Fiber3Mod29Factor2
  · exact ⟨h252Fiber3Mod29Factor1_monic, h252Fiber3Mod29Factor1_irreducible⟩
  · exact ⟨h252Fiber3Mod29Factor2_monic, h252Fiber3Mod29Factor2_irreducible⟩
  · exact h252Fiber3Mod29Factor1_degree
  · exact h252Fiber3Mod29Factor2_degree
  · constructor <;> norm_num [h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1Coeffs, integerCoefficientEval] <;> decide
  · constructor <;> norm_num [h252Fiber3Mod29Factor2, h252Fiber3Mod29Factor2Coeffs, integerCoefficientEval] <;> decide
  · exact h252Fiber3Polynomial_modular
theorem h252Fiber3Polynomial_irreducible_Q : Irreducible h252Fiber3PolynomialQ :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast h252Fiber3Polynomial_monic.isPrimitive).mp h252Fiber3Polynomial_irreducible_Z
end
end Biunimodular.F11
