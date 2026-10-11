/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3Pairs01Data
import Biunimodular.F11.HomogeneousCompletion3LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion3Pair1_2L : FixedSliceSparseExponent := ⟨1, 0, 0, 1, 1, 0⟩

theorem homogeneousCompletion3Pair1_2_monomials_check :
    homogeneousCompletion3Pair1_2U = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ ∧
      homogeneousCompletion3Pair1_2V = rationalSparseMonomial ⟨0, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair1_2_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair1_2D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair1_2L := by
  native_decide

def homogeneousCompletion3Pair1_3L : FixedSliceSparseExponent := ⟨1, 0, 1, 0, 1, 0⟩

theorem homogeneousCompletion3Pair1_3_monomials_check :
    homogeneousCompletion3Pair1_3U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion3Pair1_3V = rationalSparseMonomial ⟨0, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair1_3_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair1_3D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair1_3L := by
  native_decide

def homogeneousCompletion3Pair1_4L : FixedSliceSparseExponent := ⟨1, 1, 0, 1, 1, 0⟩

theorem homogeneousCompletion3Pair1_4_monomials_check :
    homogeneousCompletion3Pair1_4U = rationalSparseMonomial ⟨0, 1, 0, 1, 0, 0⟩ ∧
      homogeneousCompletion3Pair1_4V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair1_4_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair1_4D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair1_4L := by
  native_decide

def homogeneousCompletion3Pair1_5L : FixedSliceSparseExponent := ⟨1, 1, 1, 0, 1, 0⟩

theorem homogeneousCompletion3Pair1_5_monomials_check :
    homogeneousCompletion3Pair1_5U = rationalSparseMonomial ⟨0, 1, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion3Pair1_5V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair1_5_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair1_5D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair1_5L := by
  native_decide

end Biunimodular.F11
