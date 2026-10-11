/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs25Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair11_13L : FixedSliceSparseExponent := ⟨0, 0, 3, 2, 1, 0⟩

theorem homogeneousCompletion4Pair11_13_monomials_check :
    homogeneousCompletion4Pair11_13U = rationalSparseMonomial ⟨0, 0, 2, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair11_13V = rationalSparseMonomial ⟨0, 0, 0, 2, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair11_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair11_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair11_13L := by
  native_decide

def homogeneousCompletion4Pair11_14L : FixedSliceSparseExponent := ⟨0, 0, 3, 2, 1, 0⟩

theorem homogeneousCompletion4Pair11_14_monomials_check :
    homogeneousCompletion4Pair11_14U = rationalSparseMonomial ⟨0, 0, 2, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair11_14V = rationalSparseMonomial ⟨0, 0, 0, 1, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair11_14_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair11_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair11_14L := by
  native_decide

def homogeneousCompletion4Pair11_15L : FixedSliceSparseExponent := ⟨0, 0, 1, 4, 1, 0⟩

theorem homogeneousCompletion4Pair11_15_monomials_check :
    homogeneousCompletion4Pair11_15U = rationalSparseMonomial ⟨0, 0, 0, 2, 0, 0⟩ ∧
      homogeneousCompletion4Pair11_15V = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair11_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair11_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair11_15L := by
  native_decide

def homogeneousCompletion4Pair12_13L : FixedSliceSparseExponent := ⟨0, 0, 3, 1, 1, 0⟩

theorem homogeneousCompletion4Pair12_13_monomials_check :
    homogeneousCompletion4Pair12_13U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair12_13V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair12_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair12_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair12_13L := by
  native_decide

end Biunimodular.F11
