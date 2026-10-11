/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor2Frobenius8

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor2Coprime1 : IsCoprime h252Fiber7Mod163Factor2 (h252Fiber7Mod163Factor2r1 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2u1Coeffs h252Fiber7Mod163Factor2Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor2v1Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor2r1Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor2u1Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor2v1Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r1] using h
theorem h252Fiber7Mod163Factor2Coprime2 : IsCoprime h252Fiber7Mod163Factor2 (h252Fiber7Mod163Factor2r2 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2u2Coeffs h252Fiber7Mod163Factor2Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor2v2Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor2r2Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor2u2Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor2v2Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r2] using h
theorem h252Fiber7Mod163Factor2Coprime4 : IsCoprime h252Fiber7Mod163Factor2 (h252Fiber7Mod163Factor2r4 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2u4Coeffs h252Fiber7Mod163Factor2Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor2v4Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor2r4Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor2u4Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor2v4Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r4] using h
theorem h252Fiber7Mod163Factor2Coprime5 : IsCoprime h252Fiber7Mod163Factor2 (h252Fiber7Mod163Factor2r5 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2u5Coeffs h252Fiber7Mod163Factor2Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor2v5Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor2r5Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor2u5Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor2v5Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r5] using h
theorem h252Fiber7Mod163Factor2Coprime8 : IsCoprime h252Fiber7Mod163Factor2 (h252Fiber7Mod163Factor2r8 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2u8Coeffs h252Fiber7Mod163Factor2Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor2v8Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor2r8Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor2u8Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor2v8Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r8] using h
theorem h252Fiber7Mod163Factor2Coprime10 : IsCoprime h252Fiber7Mod163Factor2 (h252Fiber7Mod163Factor2r10 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2u10Coeffs h252Fiber7Mod163Factor2Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor2v10Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor2r10Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor2u10Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor2v10Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r10] using h
theorem h252Fiber7Mod163Factor2Coprime20 : IsCoprime h252Fiber7Mod163Factor2 (h252Fiber7Mod163Factor2r20 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor2u20Coeffs h252Fiber7Mod163Factor2Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor2v20Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor2r20Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor2u20Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor2v20Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor2, h252Fiber7Mod163Factor2r20] using h
theorem h252Fiber7Mod163Factor2_irreducible : Irreducible h252Fiber7Mod163Factor2 := by
  apply irreducible_of_frobeniusIter_certificate h252Fiber7Mod163Factor2_monic h252Fiber7Mod163Factor2_degree (by norm_num)
  · simpa only [h252Fiber7Mod163Factor2r40, h252Fiber7Mod163Factor2r40Coeffs, integerCoefficientEval_variable] using h252Fiber7Mod163Factor2Frob40
  · intro d hd hpos hlt
    have hset : Nat.divisors 40 = {1, 2, 4, 5, 8, 10, 20, 40} := by native_decide
    have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num : 40 ≠ 0)⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hcases : d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 5 ∨ d = 8 ∨ d = 10 ∨ d = 20 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor2Coprime1
      convert h252Fiber7Mod163Factor2Frob1 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor2Coprime2
      convert h252Fiber7Mod163Factor2Frob2 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor2Coprime4
      convert h252Fiber7Mod163Factor2Frob4 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor2Coprime5
      convert h252Fiber7Mod163Factor2Frob5 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor2Coprime8
      convert h252Fiber7Mod163Factor2Frob8 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor2Coprime10
      convert h252Fiber7Mod163Factor2Frob10 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor2Coprime20
      convert h252Fiber7Mod163Factor2Frob20 using 1; ring
end
end Biunimodular.F11
