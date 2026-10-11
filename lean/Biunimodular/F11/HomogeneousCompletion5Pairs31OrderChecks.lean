/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5Pairs31Data
import Biunimodular.F11.HomogeneousCompletion5LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion5Pair6_7L : FixedSliceSparseExponent := ⟨0, 1, 2, 1, 1, 0⟩

theorem homogeneousCompletion5Pair6_7_monomials_check :
    homogeneousCompletion5Pair6_7U = rationalSparseMonomial ⟨0, 0, 2, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair6_7V = rationalSparseMonomial ⟨0, 1, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair6_7_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair6_7D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair6_7L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair6_7D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair6_7L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_7D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair6_7L) ∧
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


def homogeneousCompletion5Pair6_8L : FixedSliceSparseExponent := ⟨0, 1, 1, 1, 1, 0⟩

theorem homogeneousCompletion5Pair6_8_monomials_check :
    homogeneousCompletion5Pair6_8U = rationalSparseMonomial ⟨0, 0, 1, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair6_8V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair6_8_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair6_8D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair6_8L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair6_8D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair6_8L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_8D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair6_8L) ∧
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


def homogeneousCompletion5Pair6_9L : FixedSliceSparseExponent := ⟨0, 2, 0, 1, 1, 0⟩

theorem homogeneousCompletion5Pair6_9_monomials_check :
    homogeneousCompletion5Pair6_9U = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair6_9V = rationalSparseMonomial ⟨0, 0, 0, 1, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair6_9_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair6_9D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair6_9L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair6_9D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair6_9L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_9D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair6_9L) ∧
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


def homogeneousCompletion5Pair6_10L : FixedSliceSparseExponent := ⟨0, 1, 2, 1, 1, 0⟩

theorem homogeneousCompletion5Pair6_10_monomials_check :
    homogeneousCompletion5Pair6_10U = rationalSparseMonomial ⟨0, 0, 2, 0, 0, 0⟩ ∧
      homogeneousCompletion5Pair6_10V = rationalSparseMonomial ⟨0, 1, 0, 0, 1, 0⟩ := by
  native_decide

theorem homogeneousCompletion5Pair6_10_degree_bounds_check :
    ∀ k : Fin 27, ∀ t ∈ (homogeneousCompletion5Pair6_10D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion5Leading k)) homogeneousCompletion5Pair6_10L := by
  have h : (∀ t ∈ homogeneousCompletion5Pair6_10D1.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 0, 1, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D2.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 0, 1, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D3.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 0, 1, 0, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D4.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨1, 1, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D5.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨2, 0, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D6.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 1, 1, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D7.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 0, 1, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D8.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 0, 1, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D9.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 0, 1, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D10.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 2, 1, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D11.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 1, 1, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D12.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 0, 1, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D13.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 2, 0, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D14.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 2, 1, 0, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D15.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 3, 0, 0, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D16.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 2, 2, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D17.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 1, 2, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D18.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 3, 1, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D19.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 2, 1, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D20.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 3, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D21.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 3, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D22.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 4, 0, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D23.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 1, 4, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D24.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 1, 0, 4, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D25.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 1, 0, 0, 4, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D26.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 5, 0, 0⟩) homogeneousCompletion5Pair6_10L) ∧
      (∀ t ∈ homogeneousCompletion5Pair6_10D27.numerator, homogeneousExponentLT (fixedSliceSparseExponentMul t.exponent ⟨0, 0, 0, 0, 6, 0⟩) homogeneousCompletion5Pair6_10L) ∧
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
