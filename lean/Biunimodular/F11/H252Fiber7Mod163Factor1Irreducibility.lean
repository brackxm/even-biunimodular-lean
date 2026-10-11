/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7Mod163Factor1Frobenius8

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber7Mod163Factor1Coprime1 : IsCoprime h252Fiber7Mod163Factor1 (h252Fiber7Mod163Factor1r1 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1u1Coeffs h252Fiber7Mod163Factor1Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor1v1Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor1r1Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor1u1Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor1v1Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r1] using h
theorem h252Fiber7Mod163Factor1Coprime2 : IsCoprime h252Fiber7Mod163Factor1 (h252Fiber7Mod163Factor1r2 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1u2Coeffs h252Fiber7Mod163Factor1Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor1v2Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor1r2Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor1u2Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor1v2Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r2] using h
theorem h252Fiber7Mod163Factor1Coprime4 : IsCoprime h252Fiber7Mod163Factor1 (h252Fiber7Mod163Factor1r4 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1u4Coeffs h252Fiber7Mod163Factor1Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor1v4Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor1r4Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor1u4Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor1v4Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r4] using h
theorem h252Fiber7Mod163Factor1Coprime5 : IsCoprime h252Fiber7Mod163Factor1 (h252Fiber7Mod163Factor1r5 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1u5Coeffs h252Fiber7Mod163Factor1Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor1v5Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor1r5Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor1u5Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor1v5Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r5] using h
theorem h252Fiber7Mod163Factor1Coprime8 : IsCoprime h252Fiber7Mod163Factor1 (h252Fiber7Mod163Factor1r8 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1u8Coeffs h252Fiber7Mod163Factor1Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor1v8Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor1r8Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor1u8Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor1v8Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r8] using h
theorem h252Fiber7Mod163Factor1Coprime10 : IsCoprime h252Fiber7Mod163Factor1 (h252Fiber7Mod163Factor1r10 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1u10Coeffs h252Fiber7Mod163Factor1Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor1v10Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor1r10Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor1u10Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor1v10Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r10] using h
theorem h252Fiber7Mod163Factor1Coprime20 : IsCoprime h252Fiber7Mod163Factor1 (h252Fiber7Mod163Factor1r20 - X) := by
  have hc : integerCoefficientEqualMod 163 (integerCoefficientAdd (integerCoefficientMul h252Fiber7Mod163Factor1u20Coeffs h252Fiber7Mod163Factor1Coeffs) (integerCoefficientMul h252Fiber7Mod163Factor1v20Coeffs (integerCoefficientAdd h252Fiber7Mod163Factor1r20Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 163 (X : (ZMod 163)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 163)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber7Mod163Factor1u20Coeffs, integerCoefficientEval X h252Fiber7Mod163Factor1v20Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber7Mod163Factor1, h252Fiber7Mod163Factor1r20] using h
theorem h252Fiber7Mod163Factor1_irreducible : Irreducible h252Fiber7Mod163Factor1 := by
  apply irreducible_of_frobeniusIter_certificate h252Fiber7Mod163Factor1_monic h252Fiber7Mod163Factor1_degree (by norm_num)
  · simpa only [h252Fiber7Mod163Factor1r40, h252Fiber7Mod163Factor1r40Coeffs, integerCoefficientEval_variable] using h252Fiber7Mod163Factor1Frob40
  · intro d hd hpos hlt
    have hset : Nat.divisors 40 = {1, 2, 4, 5, 8, 10, 20, 40} := by native_decide
    have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num : 40 ≠ 0)⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hcases : d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 5 ∨ d = 8 ∨ d = 10 ∨ d = 20 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor1Coprime1
      convert h252Fiber7Mod163Factor1Frob1 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor1Coprime2
      convert h252Fiber7Mod163Factor1Frob2 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor1Coprime4
      convert h252Fiber7Mod163Factor1Frob4 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor1Coprime5
      convert h252Fiber7Mod163Factor1Frob5 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor1Coprime8
      convert h252Fiber7Mod163Factor1Frob8 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor1Coprime10
      convert h252Fiber7Mod163Factor1Frob10 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber7Mod163Factor1Coprime20
      convert h252Fiber7Mod163Factor1Frob20 using 1; ring
end
end Biunimodular.F11
