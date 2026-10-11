/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6Mod3Factor1Frobenius12

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber6Mod3Factor1Coprime1 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r1 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u1Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v1Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r1Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u1Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v1Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r1] using h
theorem h252Fiber6Mod3Factor1Coprime2 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r2 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u2Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v2Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r2Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u2Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v2Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r2] using h
theorem h252Fiber6Mod3Factor1Coprime3 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r3 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u3Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v3Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r3Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u3Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v3Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r3] using h
theorem h252Fiber6Mod3Factor1Coprime4 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r4 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u4Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v4Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r4Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u4Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v4Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r4] using h
theorem h252Fiber6Mod3Factor1Coprime5 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r5 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u5Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v5Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r5Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u5Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v5Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r5] using h
theorem h252Fiber6Mod3Factor1Coprime6 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r6 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u6Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v6Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r6Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u6Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v6Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r6] using h
theorem h252Fiber6Mod3Factor1Coprime10 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r10 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u10Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v10Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r10Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u10Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v10Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r10] using h
theorem h252Fiber6Mod3Factor1Coprime12 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r12 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u12Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v12Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r12Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u12Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v12Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r12] using h
theorem h252Fiber6Mod3Factor1Coprime15 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r15 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u15Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v15Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r15Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u15Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v15Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r15] using h
theorem h252Fiber6Mod3Factor1Coprime20 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r20 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u20Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v20Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r20Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u20Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v20Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r20] using h
theorem h252Fiber6Mod3Factor1Coprime30 : IsCoprime h252Fiber6Mod3Factor1 (h252Fiber6Mod3Factor1r30 - X) := by
  have hc : integerCoefficientEqualMod 3 (integerCoefficientAdd (integerCoefficientMul h252Fiber6Mod3Factor1u30Coeffs h252Fiber6Mod3Factor1Coeffs) (integerCoefficientMul h252Fiber6Mod3Factor1v30Coeffs (integerCoefficientAdd h252Fiber6Mod3Factor1r30Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 3 (X : (ZMod 3)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 3)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber6Mod3Factor1u30Coeffs, integerCoefficientEval X h252Fiber6Mod3Factor1v30Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber6Mod3Factor1, h252Fiber6Mod3Factor1r30] using h
theorem h252Fiber6Mod3Factor1_irreducible : Irreducible h252Fiber6Mod3Factor1 := by
  apply irreducible_of_frobeniusIter_certificate h252Fiber6Mod3Factor1_monic h252Fiber6Mod3Factor1_degree (by norm_num)
  · simpa only [h252Fiber6Mod3Factor1r60, h252Fiber6Mod3Factor1r60Coeffs, integerCoefficientEval_variable] using h252Fiber6Mod3Factor1Frob60
  · intro d hd hpos hlt
    have hset : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by native_decide
    have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num : 60 ≠ 0)⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 10 ∨ d = 12 ∨ d = 15 ∨ d = 20 ∨ d = 30 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime1
      convert h252Fiber6Mod3Factor1Frob1 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime2
      convert h252Fiber6Mod3Factor1Frob2 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime3
      convert h252Fiber6Mod3Factor1Frob3 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime4
      convert h252Fiber6Mod3Factor1Frob4 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime5
      convert h252Fiber6Mod3Factor1Frob5 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime6
      convert h252Fiber6Mod3Factor1Frob6 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime10
      convert h252Fiber6Mod3Factor1Frob10 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime12
      convert h252Fiber6Mod3Factor1Frob12 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime15
      convert h252Fiber6Mod3Factor1Frob15 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime20
      convert h252Fiber6Mod3Factor1Frob20 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber6Mod3Factor1Coprime30
      convert h252Fiber6Mod3Factor1Frob30 using 1; ring
end
end Biunimodular.F11
