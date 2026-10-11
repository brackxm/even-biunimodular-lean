/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4LaurentRankRelationsChecks
import Biunimodular.F11.H252Fiber4LaurentRankDeterminant
import Biunimodular.F11.TorusMacaulayPolynomialComparison

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
def h252Fiber4LaurentRankOriginalGenerators : List (List RurInverseTerm7) :=
  [rurInverseGenerator1, rurInverseGenerator2, rurInverseGenerator3,
    rurInverseGenerator4, rurInverseGenerator5]
theorem h252Fiber4LaurentRank_parents_allowed : ∀ j : Fin 1250,
    ∀ p ∈ h252Fiber4LaurentRankOriginalParents[j.val]?.getD [],
      p.2 ∈ h252Fiber4LaurentRankOriginalGenerators ∨ p.2 = h252Fiber4LaurentRankPhi := by native_decide
theorem h252Fiber4LaurentRank_original_check : ∀ j : Fin 1250,
    torusMacaulayColumnZeroCheck h252Fiber4LaurentRankColumns h252Fiber4LaurentRankMonomials h252Fiber4LaurentRankConstants
      h252Fiber4LaurentRankGlobal (h252Fiber4LaurentRankOriginalParents[j.val]?.getD []) j.val := by
  intro j
  have hr : (0 ≤ j.val ∧ j.val < 125) ∨ (125 ≤ j.val ∧ j.val < 250) ∨ (250 ≤ j.val ∧ j.val < 375) ∨ (375 ≤ j.val ∧ j.val < 500) ∨ (500 ≤ j.val ∧ j.val < 625) ∨ (625 ≤ j.val ∧ j.val < 750) ∨ (750 ≤ j.val ∧ j.val < 875) ∨ (875 ≤ j.val ∧ j.val < 1000) ∨ (1000 ≤ j.val ∧ j.val < 1125) ∨ (1125 ≤ j.val ∧ j.val < 1250) := by have hj := j.isLt; omega
  rcases hr with h | h | h | h | h | h | h | h | h | h
  · let k : Fin 125 := ⟨j.val-0, by omega⟩
    have he : 0+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check001 k
  · let k : Fin 125 := ⟨j.val-125, by omega⟩
    have he : 125+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check002 k
  · let k : Fin 125 := ⟨j.val-250, by omega⟩
    have he : 250+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check003 k
  · let k : Fin 125 := ⟨j.val-375, by omega⟩
    have he : 375+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check004 k
  · let k : Fin 125 := ⟨j.val-500, by omega⟩
    have he : 500+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check005 k
  · let k : Fin 125 := ⟨j.val-625, by omega⟩
    have he : 625+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check006 k
  · let k : Fin 125 := ⟨j.val-750, by omega⟩
    have he : 750+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check007 k
  · let k : Fin 125 := ⟨j.val-875, by omega⟩
    have he : 875+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check008 k
  · let k : Fin 125 := ⟨j.val-1000, by omega⟩
    have he : 1000+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check009 k
  · let k : Fin 125 := ⟨j.val-1125, by omega⟩
    have he : 1125+k.val = j.val := by dsimp [k]; omega
    simpa only [he] using h252Fiber4LaurentRank_original_check010 k

noncomputable section
theorem h252Fiber4LaurentRank_monomial_comparison
    {R : Type*} [CommRing R] [Algebra ℚ R] (z1 z2 z3 z4 w c1 c2 c3 c4 v a x : R)
    (hq : integerCoefficientEval a h252FiberCRTQ4 = 0)
    (hG : ∀ g ∈ h252Fiber4LaurentRankOriginalGenerators, rurInverseSparseEval g z1 z2 z3 z4 w a x = 0)
    (hcG : ∀ g ∈ h252Fiber4LaurentRankOriginalGenerators, rurInverseSparseEval g c1 c2 c3 c4 v a x = 0) :
    ∀ i : Fin 1250,
      rurInverseSparseEval h252Fiber4LaurentRankGlobal c1 c2 c3 c4 v a x *
        rurInverseSparseEval (h252Fiber4LaurentRankMonomials[i.val]?.getD []) z1 z2 z3 z4 w a x =
      rurInverseSparseEval h252Fiber4LaurentRankGlobal z1 z2 z3 z4 w a x *
        rurInverseSparseEval (h252Fiber4LaurentRankMonomials[i.val]?.getD []) c1 c2 c3 c4 v a x := by
  apply torusMacaulay_polynomial_compare 1250 h252Fiber4LaurentRankRows h252Fiber4LaurentRankColumns
    h252Fiber4LaurentRankMonomials h252Fiber4LaurentRankConstants h252Fiber4LaurentRankGlobal h252Fiber4LaurentRankOriginalParents
    z1 z2 z3 z4 w c1 c2 c3 c4 v a x h252Fiber4LaurentRank_transpose_check h252Fiber4LaurentRank_original_check
  · intro j p hp
    obtain hg | hphi := h252Fiber4LaurentRank_parents_allowed j p hp
    · exact hG p.2 hg
    · rw [hphi, h252Fiber4LaurentRankPhi, rurInverseSparseEval_ofZ5]
      exact hq
  · intro j p hp
    obtain hg | hphi := h252Fiber4LaurentRank_parents_allowed j p hp
    · exact hcG p.2 hg
    · rw [hphi, h252Fiber4LaurentRankPhi, rurInverseSparseEval_ofZ5]
      exact hq
  · exact h252Fiber4LaurentRank_det_isUnit_of_root a hq
end

end Biunimodular.F11
