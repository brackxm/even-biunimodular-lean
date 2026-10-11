/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs05Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair2_5L : FixedSliceSparseExponent := ⟨1, 1, 0, 1, 1, 0⟩

theorem homogeneousCompletion4Pair2_5_monomials_check :
    homogeneousCompletion4Pair2_5U = rationalSparseMonomial ⟨0, 1, 0, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair2_5V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_5_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_5D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_5L := by
  native_decide

def homogeneousCompletion4Pair2_6L : FixedSliceSparseExponent := ⟨1, 1, 1, 1, 1, 0⟩

theorem homogeneousCompletion4Pair2_6_monomials_check :
    homogeneousCompletion4Pair2_6U = rationalSparseMonomial ⟨0, 1, 1, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair2_6V = rationalSparseMonomial ⟨1, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_6_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_6D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_6L := by
  native_decide

def homogeneousCompletion4Pair2_7L : FixedSliceSparseExponent := ⟨1, 2, 0, 1, 1, 0⟩

theorem homogeneousCompletion4Pair2_7_monomials_check :
    homogeneousCompletion4Pair2_7U = rationalSparseMonomial ⟨0, 2, 0, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair2_7V = rationalSparseMonomial ⟨1, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_7_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_7D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_7L := by
  native_decide

def homogeneousCompletion4Pair2_8L : FixedSliceSparseExponent := ⟨1, 1, 1, 1, 0, 0⟩

theorem homogeneousCompletion4Pair2_8_monomials_check :
    homogeneousCompletion4Pair2_8U = rationalSparseMonomial ⟨0, 1, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair2_8V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair2_8_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair2_8D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair2_8L := by
  native_decide

end Biunimodular.F11
