/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor4Frobenius6

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor4Coprime1 : IsCoprime coordinateMod17Factor4 (coordinateMod17Factor4r1 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor4u1Coeffs coordinateMod17Factor4Coeffs) (integerCoefficientMul coordinateMod17Factor4v1Coeffs (integerCoefficientAdd coordinateMod17Factor4r1Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor4u1Coeffs, integerCoefficientEval X coordinateMod17Factor4v1Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r1] using h
theorem coordinateMod17Factor4Coprime2 : IsCoprime coordinateMod17Factor4 (coordinateMod17Factor4r2 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor4u2Coeffs coordinateMod17Factor4Coeffs) (integerCoefficientMul coordinateMod17Factor4v2Coeffs (integerCoefficientAdd coordinateMod17Factor4r2Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor4u2Coeffs, integerCoefficientEval X coordinateMod17Factor4v2Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r2] using h
theorem coordinateMod17Factor4Coprime3 : IsCoprime coordinateMod17Factor4 (coordinateMod17Factor4r3 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor4u3Coeffs coordinateMod17Factor4Coeffs) (integerCoefficientMul coordinateMod17Factor4v3Coeffs (integerCoefficientAdd coordinateMod17Factor4r3Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor4u3Coeffs, integerCoefficientEval X coordinateMod17Factor4v3Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r3] using h
theorem coordinateMod17Factor4Coprime5 : IsCoprime coordinateMod17Factor4 (coordinateMod17Factor4r5 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor4u5Coeffs coordinateMod17Factor4Coeffs) (integerCoefficientMul coordinateMod17Factor4v5Coeffs (integerCoefficientAdd coordinateMod17Factor4r5Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor4u5Coeffs, integerCoefficientEval X coordinateMod17Factor4v5Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r5] using h
theorem coordinateMod17Factor4Coprime6 : IsCoprime coordinateMod17Factor4 (coordinateMod17Factor4r6 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor4u6Coeffs coordinateMod17Factor4Coeffs) (integerCoefficientMul coordinateMod17Factor4v6Coeffs (integerCoefficientAdd coordinateMod17Factor4r6Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor4u6Coeffs, integerCoefficientEval X coordinateMod17Factor4v6Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r6] using h
theorem coordinateMod17Factor4Coprime10 : IsCoprime coordinateMod17Factor4 (coordinateMod17Factor4r10 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor4u10Coeffs coordinateMod17Factor4Coeffs) (integerCoefficientMul coordinateMod17Factor4v10Coeffs (integerCoefficientAdd coordinateMod17Factor4r10Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor4u10Coeffs, integerCoefficientEval X coordinateMod17Factor4v10Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r10] using h
theorem coordinateMod17Factor4Coprime15 : IsCoprime coordinateMod17Factor4 (coordinateMod17Factor4r15 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor4u15Coeffs coordinateMod17Factor4Coeffs) (integerCoefficientMul coordinateMod17Factor4v15Coeffs (integerCoefficientAdd coordinateMod17Factor4r15Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor4u15Coeffs, integerCoefficientEval X coordinateMod17Factor4v15Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor4, coordinateMod17Factor4r15] using h
theorem coordinateMod17Factor4_irreducible : Irreducible coordinateMod17Factor4 := by
  apply irreducible_of_frobeniusIter_certificate coordinateMod17Factor4_monic coordinateMod17Factor4_degree (by norm_num)
  · simpa only [coordinateMod17Factor4r30, coordinateMod17Factor4r30Coeffs, integerCoefficientEval_variable] using coordinateMod17Factor4Frob30
  · intro d hd hpos hlt
    have hset : Nat.divisors 30 = {1, 2, 3, 5, 6, 10, 15, 30} := by native_decide
    have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num : 30 ≠ 0)⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 6 ∨ d = 10 ∨ d = 15 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isCoprime_of_dvd_sub coordinateMod17Factor4Coprime1
      convert coordinateMod17Factor4Frob1 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor4Coprime2
      convert coordinateMod17Factor4Frob2 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor4Coprime3
      convert coordinateMod17Factor4Frob3 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor4Coprime5
      convert coordinateMod17Factor4Frob5 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor4Coprime6
      convert coordinateMod17Factor4Frob6 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor4Coprime10
      convert coordinateMod17Factor4Frob10 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor4Coprime15
      convert coordinateMod17Factor4Frob15 using 1; ring
end
end Biunimodular.F11
