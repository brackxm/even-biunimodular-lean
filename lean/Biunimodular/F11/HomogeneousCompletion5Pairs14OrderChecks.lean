/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5Pairs14Data
import Biunimodular.F11.HomogeneousCompletion5LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion5Pair3_5L : FixedSliceSparseExponent := ⟨2, 0, 1, 0, 0, 0⟩

theorem homogeneousCompletion5Pair3_5_monomials_check :
    homogeneousCompletion5Pair3_5U = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair3_5V = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair3_5_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair3_5D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair3_5L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair3_5D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair3_5L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_5D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair3_5L) ∧
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


def homogeneousCompletion5Pair3_6L : FixedSliceSparseExponent := ⟨1, 1, 1, 1, 1, 0⟩

theorem homogeneousCompletion5Pair3_6_monomials_check :
    homogeneousCompletion5Pair3_6U = rationalSparseMonomial ⟨0, 1, 0, 1, 1, 0⟩ ∧
      homogeneousCompletion5Pair3_6V = rationalSparseMonomial ⟨1, 0, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair3_6_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair3_6D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair3_6L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair3_6D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair3_6L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_6D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair3_6L) ∧
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


def homogeneousCompletion5Pair3_7L : FixedSliceSparseExponent := ⟨1, 0, 2, 0, 1, 0⟩

theorem homogeneousCompletion5Pair3_7_monomials_check :
    homogeneousCompletion5Pair3_7U = rationalSparseMonomial ⟨0, 0, 1, 0, 1, 0⟩ ∧
      homogeneousCompletion5Pair3_7V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair3_7_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair3_7D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair3_7L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair3_7D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair3_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_7D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair3_7L) ∧
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


def homogeneousCompletion5Pair3_8L : FixedSliceSparseExponent := ⟨1, 1, 1, 0, 1, 0⟩

theorem homogeneousCompletion5Pair3_8_monomials_check :
    homogeneousCompletion5Pair3_8U = rationalSparseMonomial ⟨0, 1, 0, 0, 1, 0⟩ ∧
      homogeneousCompletion5Pair3_8V = rationalSparseMonomial ⟨1, 0, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair3_8_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair3_8D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair3_8L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair3_8D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair3_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair3_8D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair3_8L) ∧
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
