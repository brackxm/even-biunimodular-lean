/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs12Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair4_10L : FixedSliceSparseExponent := ⟨1, 2, 1, 0, 0, 0⟩

theorem homogeneousCompletion4Pair4_10_monomials_check :
    homogeneousCompletion4Pair4_10U = rationalSparseMonomial ⟨0, 1, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair4_10V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_10_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_10D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_10L := by
  native_decide

def homogeneousCompletion4Pair4_11L : FixedSliceSparseExponent := ⟨1, 1, 1, 2, 1, 0⟩

theorem homogeneousCompletion4Pair4_11_monomials_check :
    homogeneousCompletion4Pair4_11U = rationalSparseMonomial ⟨0, 0, 1, 2, 1, 0⟩ ∧
      homogeneousCompletion4Pair4_11V = rationalSparseMonomial ⟨1, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_11_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_11D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_11L := by
  native_decide

def homogeneousCompletion4Pair4_12L : FixedSliceSparseExponent := ⟨1, 1, 2, 1, 1, 0⟩

theorem homogeneousCompletion4Pair4_12_monomials_check :
    homogeneousCompletion4Pair4_12U = rationalSparseMonomial ⟨0, 0, 2, 1, 1, 0⟩ ∧
      homogeneousCompletion4Pair4_12V = rationalSparseMonomial ⟨1, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_12_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_12D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_12L := by
  native_decide

def homogeneousCompletion4Pair4_13L : FixedSliceSparseExponent := ⟨1, 1, 3, 0, 1, 0⟩

theorem homogeneousCompletion4Pair4_13_monomials_check :
    homogeneousCompletion4Pair4_13U = rationalSparseMonomial ⟨0, 0, 3, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair4_13V = rationalSparseMonomial ⟨1, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_13L := by
  native_decide

end Biunimodular.F11
