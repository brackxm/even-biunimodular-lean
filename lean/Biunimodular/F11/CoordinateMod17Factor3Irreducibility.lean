/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor3Frobenius6

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem coordinateMod17Factor3Coprime1 : IsCoprime coordinateMod17Factor3 (coordinateMod17Factor3r1 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor3u1Coeffs coordinateMod17Factor3Coeffs) (integerCoefficientMul coordinateMod17Factor3v1Coeffs (integerCoefficientAdd coordinateMod17Factor3r1Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor3u1Coeffs, integerCoefficientEval X coordinateMod17Factor3v1Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r1] using h
theorem coordinateMod17Factor3Coprime2 : IsCoprime coordinateMod17Factor3 (coordinateMod17Factor3r2 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor3u2Coeffs coordinateMod17Factor3Coeffs) (integerCoefficientMul coordinateMod17Factor3v2Coeffs (integerCoefficientAdd coordinateMod17Factor3r2Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor3u2Coeffs, integerCoefficientEval X coordinateMod17Factor3v2Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r2] using h
theorem coordinateMod17Factor3Coprime3 : IsCoprime coordinateMod17Factor3 (coordinateMod17Factor3r3 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor3u3Coeffs coordinateMod17Factor3Coeffs) (integerCoefficientMul coordinateMod17Factor3v3Coeffs (integerCoefficientAdd coordinateMod17Factor3r3Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor3u3Coeffs, integerCoefficientEval X coordinateMod17Factor3v3Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r3] using h
theorem coordinateMod17Factor3Coprime5 : IsCoprime coordinateMod17Factor3 (coordinateMod17Factor3r5 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor3u5Coeffs coordinateMod17Factor3Coeffs) (integerCoefficientMul coordinateMod17Factor3v5Coeffs (integerCoefficientAdd coordinateMod17Factor3r5Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor3u5Coeffs, integerCoefficientEval X coordinateMod17Factor3v5Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r5] using h
theorem coordinateMod17Factor3Coprime6 : IsCoprime coordinateMod17Factor3 (coordinateMod17Factor3r6 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor3u6Coeffs coordinateMod17Factor3Coeffs) (integerCoefficientMul coordinateMod17Factor3v6Coeffs (integerCoefficientAdd coordinateMod17Factor3r6Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor3u6Coeffs, integerCoefficientEval X coordinateMod17Factor3v6Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r6] using h
theorem coordinateMod17Factor3Coprime10 : IsCoprime coordinateMod17Factor3 (coordinateMod17Factor3r10 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor3u10Coeffs coordinateMod17Factor3Coeffs) (integerCoefficientMul coordinateMod17Factor3v10Coeffs (integerCoefficientAdd coordinateMod17Factor3r10Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor3u10Coeffs, integerCoefficientEval X coordinateMod17Factor3v10Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r10] using h
theorem coordinateMod17Factor3Coprime15 : IsCoprime coordinateMod17Factor3 (coordinateMod17Factor3r15 - X) := by
  have hc : integerCoefficientEqualMod 17 (integerCoefficientAdd (integerCoefficientMul coordinateMod17Factor3u15Coeffs coordinateMod17Factor3Coeffs) (integerCoefficientMul coordinateMod17Factor3v15Coeffs (integerCoefficientAdd coordinateMod17Factor3r15Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 17 (X : (ZMod 17)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 17)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X coordinateMod17Factor3u15Coeffs, integerCoefficientEval X coordinateMod17Factor3v15Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, coordinateMod17Factor3, coordinateMod17Factor3r15] using h
theorem coordinateMod17Factor3_irreducible : Irreducible coordinateMod17Factor3 := by
  apply irreducible_of_frobeniusIter_certificate coordinateMod17Factor3_monic coordinateMod17Factor3_degree (by norm_num)
  · simpa only [coordinateMod17Factor3r30, coordinateMod17Factor3r30Coeffs, integerCoefficientEval_variable] using coordinateMod17Factor3Frob30
  · intro d hd hpos hlt
    have hset : Nat.divisors 30 = {1, 2, 3, 5, 6, 10, 15, 30} := by native_decide
    have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num : 30 ≠ 0)⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 6 ∨ d = 10 ∨ d = 15 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isCoprime_of_dvd_sub coordinateMod17Factor3Coprime1
      convert coordinateMod17Factor3Frob1 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor3Coprime2
      convert coordinateMod17Factor3Frob2 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor3Coprime3
      convert coordinateMod17Factor3Frob3 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor3Coprime5
      convert coordinateMod17Factor3Frob5 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor3Coprime6
      convert coordinateMod17Factor3Frob6 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor3Coprime10
      convert coordinateMod17Factor3Frob10 using 1; ring
    · apply isCoprime_of_dvd_sub coordinateMod17Factor3Coprime15
      convert coordinateMod17Factor3Frob15 using 1; ring
end
end Biunimodular.F11
