/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs21Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair8_12L : FixedSliceSparseExponent := ⟨0, 1, 2, 1, 1, 0⟩

theorem homogeneousCompletion4Pair8_12_monomials_check :
    homogeneousCompletion4Pair8_12U = rationalSparseMonomial ⟨0, 0, 1, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair8_12V = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair8_12_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair8_12D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair8_12L := by
  native_decide

def homogeneousCompletion4Pair8_13L : FixedSliceSparseExponent := ⟨0, 1, 3, 1, 1, 0⟩

theorem homogeneousCompletion4Pair8_13_monomials_check :
    homogeneousCompletion4Pair8_13U = rationalSparseMonomial ⟨0, 0, 2, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair8_13V = rationalSparseMonomial ⟨0, 1, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair8_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair8_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair8_13L := by
  native_decide

def homogeneousCompletion4Pair8_14L : FixedSliceSparseExponent := ⟨0, 1, 3, 1, 0, 0⟩

theorem homogeneousCompletion4Pair8_14_monomials_check :
    homogeneousCompletion4Pair8_14U = rationalSparseMonomial ⟨0, 0, 2, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair8_14V = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair8_14_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair8_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair8_14L := by
  native_decide

def homogeneousCompletion4Pair8_15L : FixedSliceSparseExponent := ⟨0, 1, 1, 4, 1, 0⟩

theorem homogeneousCompletion4Pair8_15_monomials_check :
    homogeneousCompletion4Pair8_15U = rationalSparseMonomial ⟨0, 0, 0, 3, 1, 0⟩ ∧
      homogeneousCompletion4Pair8_15V = rationalSparseMonomial ⟨0, 1, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair8_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair8_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair8_15L := by
  native_decide

end Biunimodular.F11
