/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5Pairs04Data
import Biunimodular.F11.HomogeneousCompletion5LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion5Pair1_14L : FixedSliceSparseExponent := ⟨1, 2, 1, 0, 1, 0⟩

theorem homogeneousCompletion5Pair1_14_monomials_check :
    homogeneousCompletion5Pair1_14U = rationalSparseMonomial ⟨0, 2, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair1_14V = rationalSparseMonomial ⟨1, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair1_14_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair1_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair1_14L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair1_14D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_14D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair1_14L) ∧
      True := by native_decide
  intro k
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


def homogeneousCompletion5Pair1_15L : FixedSliceSparseExponent := ⟨1, 3, 0, 0, 1, 0⟩

theorem homogeneousCompletion5Pair1_15_monomials_check :
    homogeneousCompletion5Pair1_15U = rationalSparseMonomial ⟨0, 3, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair1_15V = rationalSparseMonomial ⟨1, 0, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair1_15_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair1_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair1_15L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair1_15D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_15D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair1_15L) ∧
      True := by native_decide
  intro k
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


def homogeneousCompletion5Pair1_16L : FixedSliceSparseExponent := ⟨1, 0, 0, 2, 2, 0⟩

theorem homogeneousCompletion5Pair1_16_monomials_check :
    homogeneousCompletion5Pair1_16U = rationalSparseMonomial ⟨0, 0, 0, 2, 1, 0⟩ ∧
      homogeneousCompletion5Pair1_16V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair1_16_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair1_16D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair1_16L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair1_16D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_16D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair1_16L) ∧
      True := by native_decide
  intro k
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


def homogeneousCompletion5Pair1_17L : FixedSliceSparseExponent := ⟨1, 0, 1, 1, 2, 0⟩

theorem homogeneousCompletion5Pair1_17_monomials_check :
    homogeneousCompletion5Pair1_17U = rationalSparseMonomial ⟨0, 0, 1, 1, 1, 0⟩ ∧
      homogeneousCompletion5Pair1_17V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair1_17_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair1_17D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair1_17L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair1_17D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      (∀ t ∈ homogeneousCompletion5Pair1_17D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair1_17L) ∧
      True := by native_decide
  intro k
  fin_cases k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


end Biunimodular.F11
