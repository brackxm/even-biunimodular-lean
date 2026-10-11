/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs10Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair3_13L : FixedSliceSparseExponent := ⟨1, 0, 3, 0, 1, 0⟩

theorem homogeneousCompletion4Pair3_13_monomials_check :
    homogeneousCompletion4Pair3_13U = rationalSparseMonomial ⟨0, 0, 2, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair3_13V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair3_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair3_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair3_13L := by
  native_decide

def homogeneousCompletion4Pair3_14L : FixedSliceSparseExponent := ⟨1, 0, 3, 1, 0, 0⟩

theorem homogeneousCompletion4Pair3_14_monomials_check :
    homogeneousCompletion4Pair3_14U = rationalSparseMonomial ⟨0, 0, 2, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair3_14V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair3_14_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair3_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair3_14L := by
  native_decide

def homogeneousCompletion4Pair3_15L : FixedSliceSparseExponent := ⟨1, 0, 1, 4, 1, 0⟩

theorem homogeneousCompletion4Pair3_15_monomials_check :
    homogeneousCompletion4Pair3_15U = rationalSparseMonomial ⟨0, 0, 0, 4, 1, 0⟩ ∧
      homogeneousCompletion4Pair3_15V = rationalSparseMonomial ⟨1, 0, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair3_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair3_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair3_15L := by
  native_decide

def homogeneousCompletion4Pair4_5L : FixedSliceSparseExponent := ⟨1, 1, 0, 1, 1, 0⟩

theorem homogeneousCompletion4Pair4_5_monomials_check :
    homogeneousCompletion4Pair4_5U = rationalSparseMonomial ⟨0, 0, 0, 1, 1, 0⟩ ∧
      homogeneousCompletion4Pair4_5V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_5_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_5D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_5L := by
  native_decide

end Biunimodular.F11
