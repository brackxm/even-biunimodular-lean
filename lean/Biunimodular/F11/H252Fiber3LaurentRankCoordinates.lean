/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3LaurentRankComparison

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def h252Fiber3LaurentRankCoordinateIndices : Fin 4 → Fin 1250 := ![⟨897, by decide⟩, ⟨681, by decide⟩, ⟨633, by decide⟩, ⟨625, by decide⟩]

def h252Fiber3LaurentRankCoordinateMonomials : Fin 4 → List RurInverseTerm7 := ![[⟨1, ⟨5, 4, 4, 4, 0, 0, 0⟩⟩], [⟨1, ⟨4, 5, 4, 4, 0, 0, 0⟩⟩], [⟨1, ⟨4, 4, 5, 4, 0, 0, 0⟩⟩], [⟨1, ⟨4, 4, 4, 5, 0, 0, 0⟩⟩]]


theorem h252Fiber3LaurentRank_coordinate_check : ∀ j : Fin 4,
    h252Fiber3LaurentRankMonomials[(h252Fiber3LaurentRankCoordinateIndices j).val]?.getD [] = h252Fiber3LaurentRankCoordinateMonomials j := by native_decide
noncomputable section
theorem h252Fiber3LaurentRank_phase_unique
    {R : Type*} [CommRing R] [Algebra ℚ R] (z1 z2 z3 z4 w c1 c2 c3 c4 v a x : R)
    (hq : integerCoefficientEval a h252FiberCRTQ3 = 0)
    (hG : ∀ g ∈ h252Fiber3LaurentRankOriginalGenerators, rurInverseSparseEval g z1 z2 z3 z4 w a x = 0)
    (hcG : ∀ g ∈ h252Fiber3LaurentRankOriginalGenerators, rurInverseSparseEval g c1 c2 c3 c4 v a x = 0)
    (hu : ∀ j : Fin 4, IsUnit (![z1,z2,z3,z4] j))
    (hcu : ∀ j : Fin 4, IsUnit (![c1,c2,c3,c4] j)) :
    ∀ j : Fin 4, ![z1,z2,z3,z4] j = ![c1,c2,c3,c4] j := by
  have h1 : IsUnit z1 := hu 0
  have h2 : IsUnit z2 := hu 1
  have h3 : IsUnit z3 := hu 2
  have h4 : IsUnit z4 := hu 3
  have hc1 : IsUnit c1 := hcu 0
  have hc2 : IsUnit c2 := hcu 1
  have hc3 : IsUnit c3 := hcu 2
  have hc4 : IsUnit c4 := hcu 3
  have hm : IsUnit ((c1^4*c2^4*c3^4*c4^4)*(z1^4*z2^4*z3^4*z4^4)) :=
    ((((hc1.pow 4).mul (hc2.pow 4)).mul (hc3.pow 4)).mul (hc4.pow 4)).mul
      ((((h1.pow 4).mul (h2.pow 4)).mul (h3.pow 4)).mul (h4.pow 4))
  intro j
  have h := h252Fiber3LaurentRank_monomial_comparison z1 z2 z3 z4 w c1 c2 c3 c4 v a x hq hG hcG (h252Fiber3LaurentRankCoordinateIndices j)
  rw [h252Fiber3LaurentRank_coordinate_check j] at h
  apply hm.mul_left_cancel
  fin_cases j <;> simp [h252Fiber3LaurentRankCoordinateMonomials, h252Fiber3LaurentRankGlobal, rurInverseSparseEval, rurInverseSparseTermEval] at h ⊢ <;> linear_combination h
end

end Biunimodular.F11
