/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3Pairs03Data
import Biunimodular.F11.HomogeneousCompletion3LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion3Pair2_5L : FixedSliceSparseExponent := ⟨1, 1, 1, 1, 1, 0⟩

theorem homogeneousCompletion3Pair2_5_monomials_check :
    homogeneousCompletion3Pair2_5U = rationalSparseMonomial ⟨0, 1, 1, 0, 1, 0⟩ ∧
      homogeneousCompletion3Pair2_5V = rationalSparseMonomial ⟨1, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair2_5_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair2_5D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair2_5L := by
  native_decide

def homogeneousCompletion3Pair2_6L : FixedSliceSparseExponent := ⟨1, 1, 1, 1, 0, 0⟩

theorem homogeneousCompletion3Pair2_6_monomials_check :
    homogeneousCompletion3Pair2_6U = rationalSparseMonomial ⟨0, 1, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion3Pair2_6V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair2_6_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair2_6D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair2_6L := by
  native_decide

def homogeneousCompletion3Pair2_7L : FixedSliceSparseExponent := ⟨1, 0, 2, 1, 1, 0⟩

theorem homogeneousCompletion3Pair2_7_monomials_check :
    homogeneousCompletion3Pair2_7U = rationalSparseMonomial ⟨0, 0, 2, 0, 1, 0⟩ ∧
      homogeneousCompletion3Pair2_7V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair2_7_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair2_7D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair2_7L := by
  native_decide

def homogeneousCompletion3Pair3_4L : FixedSliceSparseExponent := ⟨1, 1, 1, 1, 1, 0⟩

theorem homogeneousCompletion3Pair3_4_monomials_check :
    homogeneousCompletion3Pair3_4U = rationalSparseMonomial ⟨0, 1, 0, 1, 1, 0⟩ ∧
      homogeneousCompletion3Pair3_4V = rationalSparseMonomial ⟨1, 0, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair3_4_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair3_4D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair3_4L := by
  native_decide

end Biunimodular.F11
