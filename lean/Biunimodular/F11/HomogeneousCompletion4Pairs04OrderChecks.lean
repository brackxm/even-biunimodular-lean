/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs04Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair1_14L : FixedSliceSparseExponent := ⟨1, 0, 3, 1, 1, 0⟩

theorem homogeneousCompletion4Pair1_14_monomials_check :
    homogeneousCompletion4Pair1_14U = rationalSparseMonomial ⟨0, 0, 3, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair1_14V = rationalSparseMonomial ⟨1, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair1_14_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair1_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair1_14L := by
  native_decide

def homogeneousCompletion4Pair1_15L : FixedSliceSparseExponent := ⟨1, 0, 0, 4, 1, 0⟩

theorem homogeneousCompletion4Pair1_15_monomials_check :
    homogeneousCompletion4Pair1_15U = rationalSparseMonomial ⟨0, 0, 0, 4, 0, 0⟩ ∧
      homogeneousCompletion4Pair1_15V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair1_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair1_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair1_15L := by
  native_decide

def homogeneousCompletion4Pair2_3L : FixedSliceSparseExponent := ⟨1, 0, 1, 1, 0, 0⟩

theorem homogeneousCompletion4Pair2_3_monomials_check :
    homogeneousCompletion4Pair2_3U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair2_3V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_3_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_3D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_3L := by
  native_decide

def homogeneousCompletion4Pair2_4L : FixedSliceSparseExponent := ⟨1, 1, 0, 1, 0, 0⟩

theorem homogeneousCompletion4Pair2_4_monomials_check :
    homogeneousCompletion4Pair2_4U = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair2_4V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_4_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_4D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_4L := by
  native_decide

end Biunimodular.F11
