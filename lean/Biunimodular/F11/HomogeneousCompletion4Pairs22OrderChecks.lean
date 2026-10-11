/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs22Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair9_10L : FixedSliceSparseExponent := ⟨0, 2, 1, 1, 0, 0⟩

theorem homogeneousCompletion4Pair9_10_monomials_check :
    homogeneousCompletion4Pair9_10U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair9_10V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair9_10_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair9_10D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair9_10L := by
  native_decide

def homogeneousCompletion4Pair9_11L : FixedSliceSparseExponent := ⟨0, 2, 1, 2, 1, 0⟩

theorem homogeneousCompletion4Pair9_11_monomials_check :
    homogeneousCompletion4Pair9_11U = rationalSparseMonomial ⟨0, 0, 1, 1, 1, 0⟩ ∧
      homogeneousCompletion4Pair9_11V = rationalSparseMonomial ⟨0, 2, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair9_11_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair9_11D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair9_11L := by
  native_decide

def homogeneousCompletion4Pair9_12L : FixedSliceSparseExponent := ⟨0, 2, 2, 1, 1, 0⟩

theorem homogeneousCompletion4Pair9_12_monomials_check :
    homogeneousCompletion4Pair9_12U = rationalSparseMonomial ⟨0, 0, 2, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair9_12V = rationalSparseMonomial ⟨0, 2, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair9_12_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair9_12D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair9_12L := by
  native_decide

def homogeneousCompletion4Pair9_13L : FixedSliceSparseExponent := ⟨0, 2, 3, 1, 1, 0⟩

theorem homogeneousCompletion4Pair9_13_monomials_check :
    homogeneousCompletion4Pair9_13U = rationalSparseMonomial ⟨0, 0, 3, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair9_13V = rationalSparseMonomial ⟨0, 2, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair9_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair9_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair9_13L := by
  native_decide

end Biunimodular.F11
