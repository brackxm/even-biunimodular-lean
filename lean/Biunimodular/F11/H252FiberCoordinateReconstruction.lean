/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FiberProjectionSemantics
import Biunimodular.F11.TorusFiberCoordinateValues

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

theorem h252LocalizedZ5Coordinate_integerCoefficients (cs : List ℤ) :
    h252LocalizedZ5Coordinate (integerCoefficientEval (X : ℂ[X]) cs) =
      integerCoefficientEval (h252LocalizedTorusVar 4) cs := by
  change (Polynomial.aeval (h252LocalizedTorusVar 4) :
    ℂ[X] →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom (integerCoefficientEval X cs) = _
  rw [integerCoefficientEval_map]
  have hX : (Polynomial.aeval (h252LocalizedTorusVar 4) :
      ℂ[X] →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom X =
      h252LocalizedTorusVar 4 := Polynomial.aeval_X _
  rw [hX]

/-- The checked seven projection identities reconstruct an actual coordinate
from its fiber linear relations, without assuming reducedness. -/
theorem h252Coordinate_mem_range_of_fiber_relations
    (d : Fin 7 → ℤ) (n : Fin 7 → List ℤ) (hd : ∀ i, d i ≠ 0)
    (y : H252LocalizedTorusAlgebra)
    (h : ∀ i, h252FiberProjection i *
      ((d i : H252LocalizedTorusAlgebra) * y +
        integerCoefficientEval (h252LocalizedTorusVar 4) (n i)) = 0) :
    y ∈ h252LocalizedZ5Coordinate.range := by
  let E (i : Fin 7) : ℂ[X] := integerCoefficientEval X (h252FiberProjectionCoeffs i)
  let N (i : Fin 7) : ℂ[X] := integerCoefficientEval X (n i)
  have hE (i : Fin 7) : h252LocalizedZ5Coordinate (E i) = h252FiberProjection i :=
    h252LocalizedZ5Coordinate_integerCoefficients _
  have hN (i : Fin 7) : h252LocalizedZ5Coordinate (N i) =
      integerCoefficientEval (h252LocalizedTorusVar 4) (n i) :=
    h252LocalizedZ5Coordinate_integerCoefficients _
  have hdc (i : Fin 7) : (d i : ℂ) ≠ 0 := by exact_mod_cast hd i
  apply coordinate_mem_range_of_projected_relations h252LocalizedZ5Coordinate E
    (fun i => C (-(d i : ℂ)⁻¹) * E i * N i) (h252FiberCRTScale : ℂ)
    (by exact_mod_cast ne_of_gt h252FiberCRTScale_pos) y
  · simpa only [hE, map_intCast] using h252FiberProjection_partition
  · intro i
    apply projected_linear_relation_value h252LocalizedZ5Coordinate (E i) (N i)
      (d i : ℂ) (hdc i) y
    rw [hE, hN, map_intCast]
    exact h i

theorem h252LocalizedZ5Coordinate_surjective_of_fiber_relations
    (d : Fin 7 → Fin 9 → ℤ) (n : Fin 7 → Fin 9 → List ℤ)
    (hd : ∀ i j, d i j ≠ 0)
    (h : ∀ i j, h252FiberProjection i *
      ((d i j : H252LocalizedTorusAlgebra) * h252FiberCoordinateValues j +
        integerCoefficientEval (h252LocalizedTorusVar 4) (n i j)) = 0) :
    Function.Surjective h252LocalizedZ5Coordinate := by
  have hy (j : Fin 9) : h252FiberCoordinateValues j ∈ h252LocalizedZ5Coordinate.range :=
    h252Coordinate_mem_range_of_fiber_relations (fun i => d i j) (fun i => n i j)
      (fun i => hd i j) _ (fun i => h i j)
  apply h252LocalizedZ5Coordinate_surjective_of_phase_ranges
  · intro i
    fin_cases i
    · simpa [h252FiberCoordinateValues] using hy 0
    · simpa [h252FiberCoordinateValues] using hy 1
    · simpa [h252FiberCoordinateValues] using hy 2
    · simpa [h252FiberCoordinateValues] using hy 3
    · refine ⟨X, ?_⟩
      change h252LocalizedZ5Coordinate X = h252LocalizedPhaseVars ⟨4, by decide⟩
      simp [h252LocalizedZ5Coordinate, h252LocalizedPhaseVars]
  · intro i
    fin_cases i
    · simpa [h252FiberCoordinateValues] using hy 4
    · simpa [h252FiberCoordinateValues] using hy 5
    · simpa [h252FiberCoordinateValues] using hy 6
    · simpa [h252FiberCoordinateValues] using hy 7
    · simpa [h252FiberCoordinateValues] using hy 8

end
end Biunimodular.F11
