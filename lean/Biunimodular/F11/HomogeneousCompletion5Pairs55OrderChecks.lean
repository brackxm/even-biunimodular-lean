/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5Pairs55Data
import Biunimodular.F11.HomogeneousCompletion5LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion5Pair11_13L : FixedSliceSparseExponent := ⟨0, 1, 2, 1, 0, 0⟩

theorem homogeneousCompletion5Pair11_13_monomials_check :
    homogeneousCompletion5Pair11_13U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair11_13V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair11_13_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair11_13D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair11_13L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair11_13D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair11_13L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_13D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair11_13L) ∧
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


def homogeneousCompletion5Pair11_14L : FixedSliceSparseExponent := ⟨0, 2, 1, 1, 0, 0⟩

theorem homogeneousCompletion5Pair11_14_monomials_check :
    homogeneousCompletion5Pair11_14U = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair11_14V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair11_14_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair11_14D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair11_14L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair11_14D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair11_14L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_14D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair11_14L) ∧
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


def homogeneousCompletion5Pair11_15L : FixedSliceSparseExponent := ⟨0, 3, 1, 1, 0, 0⟩

theorem homogeneousCompletion5Pair11_15_monomials_check :
    homogeneousCompletion5Pair11_15U = rationalSparseMonomial ⟨0, 2, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair11_15V = rationalSparseMonomial ⟨0, 0, 1, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair11_15_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair11_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair11_15L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair11_15D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair11_15L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_15D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair11_15L) ∧
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


def homogeneousCompletion5Pair11_16L : FixedSliceSparseExponent := ⟨0, 1, 1, 2, 2, 0⟩

theorem homogeneousCompletion5Pair11_16_monomials_check :
    homogeneousCompletion5Pair11_16U = rationalSparseMonomial ⟨0, 0, 0, 1, 2, 0⟩ ∧
      homogeneousCompletion5Pair11_16V = rationalSparseMonomial ⟨0, 1, 1, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair11_16_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair11_16D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair11_16L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair11_16D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair11_16L) ∧
      (∀ t ∈ homogeneousCompletion5Pair11_16D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair11_16L) ∧
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
