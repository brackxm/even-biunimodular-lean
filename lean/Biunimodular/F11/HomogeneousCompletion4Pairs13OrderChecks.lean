/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs13Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair4_14L : FixedSliceSparseExponent := ⟨1, 1, 3, 1, 0, 0⟩

theorem homogeneousCompletion4Pair4_14_monomials_check :
    homogeneousCompletion4Pair4_14U = rationalSparseMonomial ⟨0, 0, 3, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair4_14V = rationalSparseMonomial ⟨1, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_14_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_14L := by
  native_decide

def homogeneousCompletion4Pair4_15L : FixedSliceSparseExponent := ⟨1, 1, 0, 4, 1, 0⟩

theorem homogeneousCompletion4Pair4_15_monomials_check :
    homogeneousCompletion4Pair4_15U = rationalSparseMonomial ⟨0, 0, 0, 4, 1, 0⟩ ∧
      homogeneousCompletion4Pair4_15V = rationalSparseMonomial ⟨1, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_15L := by
  native_decide

def homogeneousCompletion4Pair5_6L : FixedSliceSparseExponent := ⟨0, 1, 1, 1, 1, 0⟩

theorem homogeneousCompletion4Pair5_6_monomials_check :
    homogeneousCompletion4Pair5_6U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair5_6V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair5_6_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair5_6D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair5_6L := by
  native_decide

def homogeneousCompletion4Pair5_7L : FixedSliceSparseExponent := ⟨0, 2, 0, 1, 1, 0⟩

theorem homogeneousCompletion4Pair5_7_monomials_check :
    homogeneousCompletion4Pair5_7U = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair5_7V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair5_7_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair5_7D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair5_7L := by
  native_decide

end Biunimodular.F11
