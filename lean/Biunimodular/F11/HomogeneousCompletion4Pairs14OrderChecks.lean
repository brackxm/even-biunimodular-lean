/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs14Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair5_8L : FixedSliceSparseExponent := ⟨0, 1, 1, 1, 1, 0⟩

theorem homogeneousCompletion4Pair5_8_monomials_check :
    homogeneousCompletion4Pair5_8U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair5_8V = rationalSparseMonomial ⟨0, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair5_8_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair5_8D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair5_8L := by
  native_decide

def homogeneousCompletion4Pair5_9L : FixedSliceSparseExponent := ⟨0, 2, 0, 1, 1, 0⟩

theorem homogeneousCompletion4Pair5_9_monomials_check :
    homogeneousCompletion4Pair5_9U = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair5_9V = rationalSparseMonomial ⟨0, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair5_9_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair5_9D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair5_9L := by
  native_decide

def homogeneousCompletion4Pair5_10L : FixedSliceSparseExponent := ⟨0, 2, 1, 1, 1, 0⟩

theorem homogeneousCompletion4Pair5_10_monomials_check :
    homogeneousCompletion4Pair5_10U = rationalSparseMonomial ⟨0, 1, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair5_10V = rationalSparseMonomial ⟨0, 0, 0, 1, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair5_10_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair5_10D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair5_10L := by
  native_decide

def homogeneousCompletion4Pair5_11L : FixedSliceSparseExponent := ⟨0, 1, 1, 2, 1, 0⟩

theorem homogeneousCompletion4Pair5_11_monomials_check :
    homogeneousCompletion4Pair5_11U = rationalSparseMonomial ⟨0, 0, 1, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair5_11V = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair5_11_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair5_11D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair5_11L := by
  native_decide

end Biunimodular.F11
