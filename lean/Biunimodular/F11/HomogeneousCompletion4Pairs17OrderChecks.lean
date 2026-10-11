/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs17Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair6_11L : FixedSliceSparseExponent := ⟨0, 1, 1, 2, 1, 0⟩

theorem homogeneousCompletion4Pair6_11_monomials_check :
    homogeneousCompletion4Pair6_11U = rationalSparseMonomial ⟨0, 0, 0, 2, 0, 0⟩ ∧
      homogeneousCompletion4Pair6_11V = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair6_11_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair6_11D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair6_11L := by
  native_decide

def homogeneousCompletion4Pair6_12L : FixedSliceSparseExponent := ⟨0, 1, 2, 1, 1, 0⟩

theorem homogeneousCompletion4Pair6_12_monomials_check :
    homogeneousCompletion4Pair6_12U = rationalSparseMonomial ⟨0, 0, 1, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair6_12V = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair6_12_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair6_12D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair6_12L := by
  native_decide

def homogeneousCompletion4Pair6_13L : FixedSliceSparseExponent := ⟨0, 1, 3, 0, 1, 0⟩

theorem homogeneousCompletion4Pair6_13_monomials_check :
    homogeneousCompletion4Pair6_13U = rationalSparseMonomial ⟨0, 0, 2, 0, 0, 0⟩ ∧
      homogeneousCompletion4Pair6_13V = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair6_13_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair6_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair6_13L := by
  native_decide

def homogeneousCompletion4Pair6_14L : FixedSliceSparseExponent := ⟨0, 1, 3, 1, 1, 0⟩

theorem homogeneousCompletion4Pair6_14_monomials_check :
    homogeneousCompletion4Pair6_14U = rationalSparseMonomial ⟨0, 0, 2, 1, 0, 0⟩ ∧
      homogeneousCompletion4Pair6_14V = rationalSparseMonomial ⟨0, 1, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair6_14_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair6_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair6_14L := by
  native_decide

end Biunimodular.F11
