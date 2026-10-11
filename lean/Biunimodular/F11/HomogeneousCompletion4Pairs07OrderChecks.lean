/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs07Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair2_13L : FixedSliceSparseExponent := ⟨1, 0, 3, 1, 1, 0⟩

theorem homogeneousCompletion4Pair2_13_monomials_check :
    homogeneousCompletion4Pair2_13U = rationalSparseMonomial ⟨0, 0, 3, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair2_13V = rationalSparseMonomial ⟨1, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_13L := by
  native_decide

def homogeneousCompletion4Pair2_14L : FixedSliceSparseExponent := ⟨1, 0, 3, 1, 0, 0⟩

theorem homogeneousCompletion4Pair2_14_monomials_check :
    homogeneousCompletion4Pair2_14U = rationalSparseMonomial ⟨0, 0, 3, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair2_14V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_14_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_14L := by
  native_decide

def homogeneousCompletion4Pair2_15L : FixedSliceSparseExponent := ⟨1, 0, 0, 4, 1, 0⟩

theorem homogeneousCompletion4Pair2_15_monomials_check :
    homogeneousCompletion4Pair2_15U = rationalSparseMonomial ⟨0, 0, 0, 3, 1, 0⟩ ∧
      homogeneousCompletion4Pair2_15V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_15L := by
  native_decide

def homogeneousCompletion4Pair3_4L : FixedSliceSparseExponent := ⟨1, 1, 1, 0, 0, 0⟩

theorem homogeneousCompletion4Pair3_4_monomials_check :
    homogeneousCompletion4Pair3_4U = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair3_4V = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair3_4_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair3_4D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair3_4L := by
  native_decide

end Biunimodular.F11
