/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5Pairs88Data
import Biunimodular.F11.HomogeneousCompletion5LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion5Pair25_26L : FixedSliceSparseExponent := ⟨0, 1, 0, 5, 4, 0⟩

theorem homogeneousCompletion5Pair25_26_monomials_check :
    homogeneousCompletion5Pair25_26U = rationalSparseMonomial ⟨0, 0, 0, 5, 0, 0⟩ ∧
      homogeneousCompletion5Pair25_26V = rationalSparseMonomial ⟨0, 1, 0, 0, 4, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair25_26_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair25_26D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair25_26L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair25_26D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair25_26L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_26D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair25_26L) ∧
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


def homogeneousCompletion5Pair25_27L : FixedSliceSparseExponent := ⟨0, 1, 0, 0, 6, 0⟩

theorem homogeneousCompletion5Pair25_27_monomials_check :
    homogeneousCompletion5Pair25_27U = rationalSparseMonomial ⟨0, 0, 0, 0, 2, 0⟩ ∧
      homogeneousCompletion5Pair25_27V = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair25_27_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair25_27D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair25_27L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair25_27D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair25_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair25_27D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair25_27L) ∧
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


def homogeneousCompletion5Pair26_27L : FixedSliceSparseExponent := ⟨0, 0, 0, 5, 6, 0⟩

theorem homogeneousCompletion5Pair26_27_monomials_check :
    homogeneousCompletion5Pair26_27U = rationalSparseMonomial ⟨0, 0, 0, 0, 6, 0⟩ ∧
      homogeneousCompletion5Pair26_27V = rationalSparseMonomial ⟨0, 0, 0, 5, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair26_27_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair26_27D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair26_27L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair26_27D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair26_27L) ∧
      (∀ t ∈ homogeneousCompletion5Pair26_27D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair26_27L) ∧
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
