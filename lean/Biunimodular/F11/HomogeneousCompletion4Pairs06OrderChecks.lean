/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs06Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair2_9L : FixedSliceSparseExponent := ⟨1, 2, 0, 1, 0, 0⟩

theorem homogeneousCompletion4Pair2_9_monomials_check :
    homogeneousCompletion4Pair2_9U = rationalSparseMonomial ⟨0, 2, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair2_9V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_9_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_9D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_9L := by
  native_decide

def homogeneousCompletion4Pair2_10L : FixedSliceSparseExponent := ⟨1, 2, 1, 1, 0, 0⟩

theorem homogeneousCompletion4Pair2_10_monomials_check :
    homogeneousCompletion4Pair2_10U = rationalSparseMonomial ⟨0, 2, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair2_10V = rationalSparseMonomial ⟨1, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_10_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_10D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_10L := by
  native_decide

def homogeneousCompletion4Pair2_11L : FixedSliceSparseExponent := ⟨1, 0, 1, 2, 1, 0⟩

theorem homogeneousCompletion4Pair2_11_monomials_check :
    homogeneousCompletion4Pair2_11U = rationalSparseMonomial ⟨0, 0, 1, 1, 1, 0⟩ ∧
      homogeneousCompletion4Pair2_11V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_11_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_11D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_11L := by
  native_decide

def homogeneousCompletion4Pair2_12L : FixedSliceSparseExponent := ⟨1, 0, 2, 1, 1, 0⟩

theorem homogeneousCompletion4Pair2_12_monomials_check :
    homogeneousCompletion4Pair2_12U = rationalSparseMonomial ⟨0, 0, 2, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair2_12V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_12_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_12D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_12L := by
  native_decide

end Biunimodular.F11
