/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FiberCoordinateReconstruction
import Biunimodular.F11.CoordinateRangeInverse

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

theorem h252FiberCoordinateValues_phase (j : Fin 4) :
    h252FiberCoordinateValues (j.castAdd 5) = h252LocalizedPhaseVars j.castSucc := by
  fin_cases j <;> rfl

/-- Inverse phase coordinates need no separate fiber certificates once the
five phase coordinates belong to the finite coordinate image. -/
theorem h252LocalizedZ5Coordinate_surjective_of_phase_only
    (hz : ∀ i, h252LocalizedPhaseVars i ∈ h252LocalizedZ5Coordinate.range) :
    Function.Surjective h252LocalizedZ5Coordinate := by
  apply h252LocalizedZ5Coordinate_surjective_of_phase_ranges hz
  intro i
  exact coordinate_inverse_mem_range h252LocalizedZ5Coordinate h252Z5ComplexPolynomial
    h252Z5ComplexPolynomial_nonzero_degree.1 h252LocalizedZ5Coordinate_eliminant_zero
    _ _ (hz i) (h252LocalizedPhaseVars_units i)

/-- Four projected phase relations per factor suffice; z5 is the coordinate
itself, and the inverse variables follow from finite dimensionality. -/
theorem h252LocalizedZ5Coordinate_surjective_of_four_fiber_relations
    (d : Fin 7 → Fin 4 → ℤ) (n : Fin 7 → Fin 4 → List ℤ)
    (hd : ∀ i j, d i j ≠ 0)
    (h : ∀ i j, h252FiberProjection i *
      ((d i j : H252LocalizedTorusAlgebra) * h252LocalizedPhaseVars j.castSucc +
        integerCoefficientEval (h252LocalizedTorusVar 4) (n i j)) = 0) :
    Function.Surjective h252LocalizedZ5Coordinate := by
  apply h252LocalizedZ5Coordinate_surjective_of_phase_only
  have hy (j : Fin 4) : h252LocalizedPhaseVars j.castSucc ∈
      h252LocalizedZ5Coordinate.range :=
    h252Coordinate_mem_range_of_fiber_relations (fun i => d i j) (fun i => n i j)
      (fun i => hd i j) _ (fun i => h i j)
  intro i
  fin_cases i
  · exact hy 0
  · exact hy 1
  · exact hy 2
  · exact hy 3
  · refine ⟨X, ?_⟩
    change h252LocalizedZ5Coordinate X = h252LocalizedPhaseVars ⟨4, by decide⟩
    simp [h252LocalizedZ5Coordinate, h252LocalizedPhaseVars]

end
end Biunimodular.F11
