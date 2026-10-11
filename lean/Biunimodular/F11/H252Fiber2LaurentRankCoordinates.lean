/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber2LaurentRankValues

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def h252Fiber2LaurentRankCoordinateIndices : Fin 4 → Fin 1250 := ![⟨897, by decide⟩, ⟨681, by decide⟩, ⟨633, by decide⟩, ⟨625, by decide⟩]

def h252Fiber2LaurentRankCoordinatePowers : Fin 4 → ℕ := ![4,5,3,9]

def h252Fiber2LaurentRankCoordinateMonomials : Fin 4 → List RurInverseTerm7 := ![[⟨1, ⟨5, 4, 4, 4, 0, 0, 0⟩⟩], [⟨1, ⟨4, 5, 4, 4, 0, 0, 0⟩⟩], [⟨1, ⟨4, 4, 5, 4, 0, 0, 0⟩⟩], [⟨1, ⟨4, 4, 4, 5, 0, 0, 0⟩⟩]]

def h252Fiber2LaurentRankCoordinatePoints : Fin 4 → List RurInverseTerm7 := ![[⟨1, ⟨0, 0, 0, 0, 0, 4, 0⟩⟩], [⟨1, ⟨0, 0, 0, 0, 0, 5, 0⟩⟩], [⟨1, ⟨0, 0, 0, 0, 0, 3, 0⟩⟩], [⟨1, ⟨0, 0, 0, 0, 0, 9, 0⟩⟩]]

theorem h252Fiber2LaurentRank_coordinate_check : ∀ j : Fin 4,
    h252Fiber2LaurentRankMonomials[(h252Fiber2LaurentRankCoordinateIndices j).val]?.getD [] = h252Fiber2LaurentRankCoordinateMonomials j ∧
    h252Fiber2LaurentRankPoints[(h252Fiber2LaurentRankCoordinateIndices j).val]?.getD [] = h252Fiber2LaurentRankCoordinatePoints j := by native_decide

noncomputable section
theorem h252Fiber2LaurentRank_phase_coordinates
    {R : Type*} [CommRing R] [Algebra ℚ R] (z1 z2 z3 z4 w a x : R)
    (hq : integerCoefficientEval a [1,1,1,1,1,1,1,1,1,1,1] = 0)
    (hG : ∀ g ∈ h252Fiber2LaurentRankOriginalGenerators,
      rurInverseSparseEval g z1 z2 z3 z4 w a x = 0)
    (hUnits : ∀ j : Fin 4, IsUnit (![z1,z2,z3,z4] j)) :
    ∀ j : Fin 4, ![z1,z2,z3,z4] j = a ^ h252Fiber2LaurentRankCoordinatePowers j := by
  have h1 : IsUnit z1 := hUnits 0
  have h2 : IsUnit z2 := hUnits 1
  have h3 : IsUnit z3 := hUnits 2
  have h4 : IsUnit z4 := hUnits 3
  have hm : IsUnit (rurInverseSparseEval h252Fiber2LaurentRankGlobal z1 z2 z3 z4 w a x) := by
    simpa [h252Fiber2LaurentRankGlobal, rurInverseSparseEval, rurInverseSparseTermEval] using
      (((h1.pow 4).mul (h2.pow 4)).mul (h3.pow 4)).mul (h4.pow 4)
  intro j
  have h := h252Fiber2LaurentRank_monomial_values z1 z2 z3 z4 w a x hq hG (h252Fiber2LaurentRankCoordinateIndices j)
  obtain ⟨hpoly,hpoint⟩ := h252Fiber2LaurentRank_coordinate_check j
  rw [hpoly,hpoint] at h
  apply hm.mul_left_cancel
  fin_cases j <;>
    simp [h252Fiber2LaurentRankCoordinatePowers, h252Fiber2LaurentRankCoordinateMonomials, h252Fiber2LaurentRankCoordinatePoints,
      h252Fiber2LaurentRankGlobal, rurInverseSparseEval, rurInverseSparseTermEval] at h ⊢ <;>
    linear_combination h
end

end Biunimodular.F11
