/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor2Frobenius2

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor2Coprime1 : IsCoprime coordinateMod17Factor2 (coordinateMod17Factor2r1 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor2u1Coeffs coordinateMod17Factor2Coeffs) (integerCoefficientMul coordinateMod17Factor2v1Coeffs (integerCoefficientAdd coordinateMod17Factor2r1Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor2u1Coeffs, integerCoefficientEval X coordinateMod17Factor2v1Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r1] using h
theorem coordinateMod17Factor2Coprime2 : IsCoprime coordinateMod17Factor2 (coordinateMod17Factor2r2 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor2u2Coeffs coordinateMod17Factor2Coeffs) (integerCoefficientMul coordinateMod17Factor2v2Coeffs (integerCoefficientAdd coordinateMod17Factor2r2Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor2u2Coeffs, integerCoefficientEval X coordinateMod17Factor2v2Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r2] using h
theorem coordinateMod17Factor2Coprime5 : IsCoprime coordinateMod17Factor2 (coordinateMod17Factor2r5 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor2u5Coeffs coordinateMod17Factor2Coeffs) (integerCoefficientMul coordinateMod17Factor2v5Coeffs (integerCoefficientAdd coordinateMod17Factor2r5Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor2u5Coeffs, integerCoefficientEval X coordinateMod17Factor2v5Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor2, coordinateMod17Factor2r5] using h
theorem coordinateMod17Factor2_irreducible : Irreducible coordinateMod17Factor2 := by
  apply irreducible_of_frobeniusIter_certificate coordinateMod17Factor2_monic coordinateMod17Factor2_degree (by norm_num)
  · simpa only [coordinateMod17Factor2r10, coordinateMod17Factor2r10Coeffs, integerCoefficientEval_variable] using coordinateMod17Factor2Frob10
  · intro d hd hpos hlt
    have hset : Nat.divisors 10 = {1, 2, 5, 10} := by native_decide
    have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num : 10 ≠ 0)⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hcases : d = 1 ∨ d = 2 ∨ d = 5 := by omega
    rcases hcases with rfl | rfl | rfl
    · apply isCoprime_of_dvd_sub coordinateMod17Factor2Coprime1
      convert coordinateMod17Factor2Frob1 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor2Coprime2
      convert coordinateMod17Factor2Frob2 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor2Coprime5
      convert coordinateMod17Factor2Frob5 using 1; ring
end
end Biunimodular.F11
