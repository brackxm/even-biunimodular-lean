/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs23Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair9_14L : FixedSliceSparseExponent := ⟨0, 2, 3, 1, 0, 0⟩

theorem homogeneousCompletion4Pair9_14_monomials_check :
    homogeneousCompletion4Pair9_14U = rationalSparseMonomial ⟨0, 0, 3, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair9_14V = rationalSparseMonomial ⟨0, 2, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair9_14_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair9_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair9_14L := by
  native_decide

def homogeneousCompletion4Pair9_15L : FixedSliceSparseExponent := ⟨0, 2, 0, 4, 1, 0⟩

theorem homogeneousCompletion4Pair9_15_monomials_check :
    homogeneousCompletion4Pair9_15U = rationalSparseMonomial ⟨0, 0, 0, 3, 1, 0⟩ ∧
      homogeneousCompletion4Pair9_15V = rationalSparseMonomial ⟨0, 2, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair9_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair9_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair9_15L := by
  native_decide

def homogeneousCompletion4Pair10_11L : FixedSliceSparseExponent := ⟨0, 2, 1, 2, 1, 0⟩

theorem homogeneousCompletion4Pair10_11_monomials_check :
    homogeneousCompletion4Pair10_11U = rationalSparseMonomial ⟨0, 0, 0, 2, 1, 0⟩ ∧
      homogeneousCompletion4Pair10_11V = rationalSparseMonomial ⟨0, 2, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair10_11_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair10_11D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair10_11L := by
  native_decide

def homogeneousCompletion4Pair10_12L : FixedSliceSparseExponent := ⟨0, 2, 2, 1, 1, 0⟩

theorem homogeneousCompletion4Pair10_12_monomials_check :
    homogeneousCompletion4Pair10_12U = rationalSparseMonomial ⟨0, 0, 1, 1, 1, 0⟩ ∧
      homogeneousCompletion4Pair10_12V = rationalSparseMonomial ⟨0, 2, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair10_12_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair10_12D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair10_12L := by
  native_decide

end Biunimodular.F11
