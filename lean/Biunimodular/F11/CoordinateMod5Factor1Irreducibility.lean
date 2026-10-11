/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod5Factor1Frobenius8

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod5Factor1Coprime1 : IsCoprime coordinateMod5Factor1 (coordinateMod5Factor1r1 - X) := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientMul coordinateMod5Factor1u1Coeffs coordinateMod5Factor1Coeffs) (integerCoefficientMul coordinateMod5Factor1v1Coeffs (integerCoefficientAdd coordinateMod5Factor1r1Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 5)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod5Factor1u1Coeffs, integerCoefficientEval X coordinateMod5Factor1v1Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r1] using h
theorem coordinateMod5Factor1Coprime2 : IsCoprime coordinateMod5Factor1 (coordinateMod5Factor1r2 - X) := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientMul coordinateMod5Factor1u2Coeffs coordinateMod5Factor1Coeffs) (integerCoefficientMul coordinateMod5Factor1v2Coeffs (integerCoefficientAdd coordinateMod5Factor1r2Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 5)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod5Factor1u2Coeffs, integerCoefficientEval X coordinateMod5Factor1v2Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r2] using h
theorem coordinateMod5Factor1Coprime4 : IsCoprime coordinateMod5Factor1 (coordinateMod5Factor1r4 - X) := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientMul coordinateMod5Factor1u4Coeffs coordinateMod5Factor1Coeffs) (integerCoefficientMul coordinateMod5Factor1v4Coeffs (integerCoefficientAdd coordinateMod5Factor1r4Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 5)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod5Factor1u4Coeffs, integerCoefficientEval X coordinateMod5Factor1v4Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r4] using h
theorem coordinateMod5Factor1Coprime5 : IsCoprime coordinateMod5Factor1 (coordinateMod5Factor1r5 - X) := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientMul coordinateMod5Factor1u5Coeffs coordinateMod5Factor1Coeffs) (integerCoefficientMul coordinateMod5Factor1v5Coeffs (integerCoefficientAdd coordinateMod5Factor1r5Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 5)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod5Factor1u5Coeffs, integerCoefficientEval X coordinateMod5Factor1v5Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r5] using h
theorem coordinateMod5Factor1Coprime8 : IsCoprime coordinateMod5Factor1 (coordinateMod5Factor1r8 - X) := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientMul coordinateMod5Factor1u8Coeffs coordinateMod5Factor1Coeffs) (integerCoefficientMul coordinateMod5Factor1v8Coeffs (integerCoefficientAdd coordinateMod5Factor1r8Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 5)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod5Factor1u8Coeffs, integerCoefficientEval X coordinateMod5Factor1v8Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r8] using h
theorem coordinateMod5Factor1Coprime10 : IsCoprime coordinateMod5Factor1 (coordinateMod5Factor1r10 - X) := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientMul coordinateMod5Factor1u10Coeffs coordinateMod5Factor1Coeffs) (integerCoefficientMul coordinateMod5Factor1v10Coeffs (integerCoefficientAdd coordinateMod5Factor1r10Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 5)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod5Factor1u10Coeffs, integerCoefficientEval X coordinateMod5Factor1v10Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r10] using h
theorem coordinateMod5Factor1Coprime20 : IsCoprime coordinateMod5Factor1 (coordinateMod5Factor1r20 - X) := by
  have hc : integerCoefficientEqualMod 5 (integerCoefficientAdd (integerCoefficientMul coordinateMod5Factor1u20Coeffs coordinateMod5Factor1Coeffs) (integerCoefficientMul coordinateMod5Factor1v20Coeffs (integerCoefficientAdd coordinateMod5Factor1r20Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 5 (X : (ZMod 5)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 5)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod5Factor1u20Coeffs, integerCoefficientEval X coordinateMod5Factor1v20Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod5Factor1, coordinateMod5Factor1r20] using h
theorem coordinateMod5Factor1_irreducible : Irreducible coordinateMod5Factor1 := by
  apply irreducible_of_frobeniusIter_certificate coordinateMod5Factor1_monic coordinateMod5Factor1_degree (by norm_num)
  · simpa only [coordinateMod5Factor1r40, coordinateMod5Factor1r40Coeffs, integerCoefficientEval_variable] using coordinateMod5Factor1Frob40
  · intro d hd hpos hlt
    have hset : Nat.divisors 40 = {1, 2, 4, 5, 8, 10, 20, 40} := by native_decide
    have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num : 40 ≠ 0)⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hcases : d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 5 ∨ d = 8 ∨ d = 10 ∨ d = 20 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isCoprime_of_dvd_sub coordinateMod5Factor1Coprime1
      convert coordinateMod5Factor1Frob1 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod5Factor1Coprime2
      convert coordinateMod5Factor1Frob2 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod5Factor1Coprime4
      convert coordinateMod5Factor1Frob4 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod5Factor1Coprime5
      convert coordinateMod5Factor1Frob5 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod5Factor1Coprime8
      convert coordinateMod5Factor1Frob8 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod5Factor1Coprime10
      convert coordinateMod5Factor1Frob10 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod5Factor1Coprime20
      convert coordinateMod5Factor1Frob20 using 1; ring
end
end Biunimodular.F11
