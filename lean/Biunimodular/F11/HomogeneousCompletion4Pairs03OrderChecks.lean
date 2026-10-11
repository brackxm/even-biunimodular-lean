/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs03Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair1_10L : FixedSliceSparseExponent := ⟨1, 2, 1, 0, 1, 0⟩

theorem homogeneousCompletion4Pair1_10_monomials_check :
    homogeneousCompletion4Pair1_10U = rationalSparseMonomial ⟨0, 2, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair1_10V = rationalSparseMonomial ⟨1, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair1_10_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair1_10D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair1_10L := by
  native_decide

def homogeneousCompletion4Pair1_11L : FixedSliceSparseExponent := ⟨1, 0, 1, 2, 1, 0⟩

theorem homogeneousCompletion4Pair1_11_monomials_check :
    homogeneousCompletion4Pair1_11U = rationalSparseMonomial ⟨0, 0, 1, 2, 0, 0⟩ ∧
      homogeneousCompletion4Pair1_11V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair1_11_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair1_11D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair1_11L := by
  native_decide

def homogeneousCompletion4Pair1_12L : FixedSliceSparseExponent := ⟨1, 0, 2, 1, 1, 0⟩

theorem homogeneousCompletion4Pair1_12_monomials_check :
    homogeneousCompletion4Pair1_12U = rationalSparseMonomial ⟨0, 0, 2, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair1_12V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair1_12_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair1_12D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair1_12L := by
  native_decide

def homogeneousCompletion4Pair1_13L : FixedSliceSparseExponent := ⟨1, 0, 3, 0, 1, 0⟩

theorem homogeneousCompletion4Pair1_13_monomials_check :
    homogeneousCompletion4Pair1_13U = rationalSparseMonomial ⟨0, 0, 3, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair1_13V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair1_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair1_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair1_13L := by
  native_decide

end Biunimodular.F11
