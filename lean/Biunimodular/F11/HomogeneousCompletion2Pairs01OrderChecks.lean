/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion2Pairs01Data
import Biunimodular.F11.HomogeneousCompletion2LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion2Pair1_2L : FixedSliceSparseExponent := ⟨1, 0, 0, 1, 1, 0⟩

theorem homogeneousCompletion2Pair1_2_monomials_check :
    homogeneousCompletion2Pair1_2U = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ ∧
      homogeneousCompletion2Pair1_2V = rationalSparseMonomial ⟨0, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion2Pair1_2_degree_bounds_check :
    ∀ k : Fin 3, ∀ t ∈ (homogeneousCompletion2Pair1_2D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion2Leading k)) homogeneousCompletion2Pair1_2L := by
  native_decide

def homogeneousCompletion2Pair1_3L : FixedSliceSparseExponent := ⟨1, 1, 0, 1, 1, 0⟩

theorem homogeneousCompletion2Pair1_3_monomials_check :
    homogeneousCompletion2Pair1_3U = rationalSparseMonomial ⟨0, 1, 0, 1, 0, 0⟩ ∧
      homogeneousCompletion2Pair1_3V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion2Pair1_3_degree_bounds_check :
    ∀ k : Fin 3, ∀ t ∈ (homogeneousCompletion2Pair1_3D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion2Leading k)) homogeneousCompletion2Pair1_3L := by
  native_decide

def homogeneousCompletion2Pair2_3L : FixedSliceSparseExponent := ⟨1, 1, 0, 1, 1, 0⟩

theorem homogeneousCompletion2Pair2_3_monomials_check :
    homogeneousCompletion2Pair2_3U = rationalSparseMonomial ⟨0, 1, 0, 0, 1, 0⟩ ∧
      homogeneousCompletion2Pair2_3V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion2Pair2_3_degree_bounds_check :
    ∀ k : Fin 3, ∀ t ∈ (homogeneousCompletion2Pair2_3D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion2Leading k)) homogeneousCompletion2Pair2_3L := by
  native_decide

end Biunimodular.F11
