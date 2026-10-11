/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3Pairs02Data
import Biunimodular.F11.HomogeneousCompletion3LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion3Pair1_6L : FixedSliceSparseExponent := ⟨1, 1, 1, 1, 1, 0⟩

theorem homogeneousCompletion3Pair1_6_monomials_check :
    homogeneousCompletion3Pair1_6U = rationalSparseMonomial ⟨0, 1, 1, 1, 0, 0⟩ ∧
      homogeneousCompletion3Pair1_6V = rationalSparseMonomial ⟨1, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair1_6_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair1_6D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair1_6L := by
  native_decide

def homogeneousCompletion3Pair1_7L : FixedSliceSparseExponent := ⟨1, 0, 2, 1, 1, 0⟩

theorem homogeneousCompletion3Pair1_7_monomials_check :
    homogeneousCompletion3Pair1_7U = rationalSparseMonomial ⟨0, 0, 2, 1, 0, 0⟩ ∧
      homogeneousCompletion3Pair1_7V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair1_7_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair1_7D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair1_7L := by
  native_decide

def homogeneousCompletion3Pair2_3L : FixedSliceSparseExponent := ⟨1, 0, 1, 1, 0, 0⟩

theorem homogeneousCompletion3Pair2_3_monomials_check :
    homogeneousCompletion3Pair2_3U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion3Pair2_3V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair2_3_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair2_3D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair2_3L := by
  native_decide

def homogeneousCompletion3Pair2_4L : FixedSliceSparseExponent := ⟨1, 1, 0, 1, 1, 0⟩

theorem homogeneousCompletion3Pair2_4_monomials_check :
    homogeneousCompletion3Pair2_4U = rationalSparseMonomial ⟨0, 1, 0, 0, 1, 0⟩ ∧
      homogeneousCompletion3Pair2_4V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair2_4_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair2_4D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair2_4L := by
  native_decide

end Biunimodular.F11
