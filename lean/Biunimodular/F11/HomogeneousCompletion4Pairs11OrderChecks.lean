/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs11Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair4_6L : FixedSliceSparseExponent := ⟨1, 1, 1, 0, 1, 0⟩

theorem homogeneousCompletion4Pair4_6_monomials_check :
    homogeneousCompletion4Pair4_6U = rationalSparseMonomial ⟨0, 0, 1, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair4_6V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_6_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_6D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_6L := by
  native_decide

def homogeneousCompletion4Pair4_7L : FixedSliceSparseExponent := ⟨1, 2, 0, 0, 1, 0⟩

theorem homogeneousCompletion4Pair4_7_monomials_check :
    homogeneousCompletion4Pair4_7U = rationalSparseMonomial ⟨0, 1, 0, 0, 1, 0⟩ ∧
      homogeneousCompletion4Pair4_7V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_7_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_7D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_7L := by
  native_decide

def homogeneousCompletion4Pair4_8L : FixedSliceSparseExponent := ⟨1, 1, 1, 1, 0, 0⟩

theorem homogeneousCompletion4Pair4_8_monomials_check :
    homogeneousCompletion4Pair4_8U = rationalSparseMonomial ⟨0, 0, 1, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair4_8V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_8_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_8D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_8L := by
  native_decide

def homogeneousCompletion4Pair4_9L : FixedSliceSparseExponent := ⟨1, 2, 0, 1, 0, 0⟩

theorem homogeneousCompletion4Pair4_9_monomials_check :
    homogeneousCompletion4Pair4_9U = rationalSparseMonomial ⟨0, 1, 0, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair4_9V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair4_9_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair4_9D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair4_9L := by
  native_decide

end Biunimodular.F11
