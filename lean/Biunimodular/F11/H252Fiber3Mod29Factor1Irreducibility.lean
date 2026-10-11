/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3Mod29Factor1Frobenius2

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
noncomputable section
theorem h252Fiber3Mod29Factor1Coprime1 : IsCoprime h252Fiber3Mod29Factor1 (h252Fiber3Mod29Factor1r1 - X) := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientMul h252Fiber3Mod29Factor1u1Coeffs h252Fiber3Mod29Factor1Coeffs) (integerCoefficientMul h252Fiber3Mod29Factor1v1Coeffs (integerCoefficientAdd h252Fiber3Mod29Factor1r1Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 29)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber3Mod29Factor1u1Coeffs, integerCoefficientEval X h252Fiber3Mod29Factor1v1Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1r1] using h
theorem h252Fiber3Mod29Factor1Coprime2 : IsCoprime h252Fiber3Mod29Factor1 (h252Fiber3Mod29Factor1r2 - X) := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientMul h252Fiber3Mod29Factor1u2Coeffs h252Fiber3Mod29Factor1Coeffs) (integerCoefficientMul h252Fiber3Mod29Factor1v2Coeffs (integerCoefficientAdd h252Fiber3Mod29Factor1r2Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 29)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber3Mod29Factor1u2Coeffs, integerCoefficientEval X h252Fiber3Mod29Factor1v2Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1r2] using h
theorem h252Fiber3Mod29Factor1Coprime5 : IsCoprime h252Fiber3Mod29Factor1 (h252Fiber3Mod29Factor1r5 - X) := by
  have hc : integerCoefficientEqualMod 29 (integerCoefficientAdd (integerCoefficientMul h252Fiber3Mod29Factor1u5Coeffs h252Fiber3Mod29Factor1Coeffs) (integerCoefficientMul h252Fiber3Mod29Factor1v5Coeffs (integerCoefficientAdd h252Fiber3Mod29Factor1r5Coeffs [0,-1]))) [1] = true := by native_decide
  have h := integerCoefficientEval_eq_of_equal_mod 29 (X : (ZMod 29)[X]) _ _ hc
  have hvar : integerCoefficientEval (X : (ZMod 29)[X]) [0,-1] = -X := by simp [integerCoefficientEval]
  refine ⟨integerCoefficientEval X h252Fiber3Mod29Factor1u5Coeffs, integerCoefficientEval X h252Fiber3Mod29Factor1v5Coeffs, ?_⟩
  simpa only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton, hvar, Int.cast_one, ← sub_eq_add_neg, h252Fiber3Mod29Factor1, h252Fiber3Mod29Factor1r5] using h
theorem h252Fiber3Mod29Factor1_irreducible : Irreducible h252Fiber3Mod29Factor1 := by
  apply irreducible_of_frobeniusIter_certificate h252Fiber3Mod29Factor1_monic h252Fiber3Mod29Factor1_degree (by norm_num)
  · simpa only [h252Fiber3Mod29Factor1r10, h252Fiber3Mod29Factor1r10Coeffs, integerCoefficientEval_variable] using h252Fiber3Mod29Factor1Frob10
  · intro d hd hpos hlt
    have hset : Nat.divisors 10 = {1, 2, 5, 10} := by native_decide
    have hm := Nat.mem_divisors.mpr ⟨hd, (by norm_num : 10 ≠ 0)⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hcases : d = 1 ∨ d = 2 ∨ d = 5 := by omega
    rcases hcases with rfl | rfl | rfl
    · apply isCoprime_of_dvd_sub h252Fiber3Mod29Factor1Coprime1
      convert h252Fiber3Mod29Factor1Frob1 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber3Mod29Factor1Coprime2
      convert h252Fiber3Mod29Factor1Frob2 using 1; ring
    · apply isCoprime_of_dvd_sub h252Fiber3Mod29Factor1Coprime5
      convert h252Fiber3Mod29Factor1Frob5 using 1; ring
end
end Biunimodular.F11
