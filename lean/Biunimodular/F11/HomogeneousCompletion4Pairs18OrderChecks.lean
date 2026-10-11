/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs18Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair6_15L : FixedSliceSparseExponent := ⟨0, 1, 1, 4, 1, 0⟩

theorem homogeneousCompletion4Pair6_15_monomials_check :
    homogeneousCompletion4Pair6_15U = rationalSparseMonomial ⟨0, 0, 0, 4, 0, 0⟩ ∧
      homogeneousCompletion4Pair6_15V = rationalSparseMonomial ⟨0, 1, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair6_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair6_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair6_15L := by
  native_decide

def homogeneousCompletion4Pair7_8L : FixedSliceSparseExponent := ⟨0, 2, 1, 1, 1, 0⟩

theorem homogeneousCompletion4Pair7_8_monomials_check :
    homogeneousCompletion4Pair7_8U = rationalSparseMonomial ⟨0, 0, 1, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair7_8V = rationalSparseMonomial ⟨0, 1, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair7_8_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair7_8D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair7_8L := by
  native_decide

def homogeneousCompletion4Pair7_9L : FixedSliceSparseExponent := ⟨0, 2, 0, 1, 1, 0⟩

theorem homogeneousCompletion4Pair7_9_monomials_check :
    homogeneousCompletion4Pair7_9U = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair7_9V = rationalSparseMonomial ⟨0, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair7_9_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair7_9D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair7_9L := by
  native_decide

def homogeneousCompletion4Pair7_10L : FixedSliceSparseExponent := ⟨0, 2, 1, 0, 1, 0⟩

theorem homogeneousCompletion4Pair7_10_monomials_check :
    homogeneousCompletion4Pair7_10U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair7_10V = rationalSparseMonomial ⟨0, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair7_10_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair7_10D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair7_10L := by
  native_decide

end Biunimodular.F11
