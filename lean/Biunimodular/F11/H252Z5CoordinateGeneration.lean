/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252LocalizedZ5Coordinate
import Biunimodular.F11.H252ComplexPhaseReconstruction

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

def h252LocalizedPhaseVars : Fin 5 → H252LocalizedTorusAlgebra :=
  ![h252LocalizedTorusVar 0, h252LocalizedTorusVar 1, h252LocalizedTorusVar 2,
    h252LocalizedTorusVar 3, h252LocalizedTorusVar 4]

def h252LocalizedInverseVars (i : Fin 5) : H252LocalizedTorusAlgebra :=
  h252LocalizedTorusVar 5 * h252TorusCofactor h252LocalizedPhaseVars i

theorem h252LocalizedPhaseVars_units (i : Fin 5) :
    h252LocalizedPhaseVars i * h252LocalizedInverseVars i = 1 := by
  apply h252TorusCofactor_units
  have hs := rurInverseGenerator6_quotient_zero
  rw [rurInverseGenerator6_eval] at hs
  change h252LocalizedTorusVar 5 * h252TorusD (h252LocalizedTorusVar 0)
    (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
    (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 4) = 1
  exact sub_eq_zero.mp hs

/-- The inverse variables recover the saturation variable and the rotated
coordinate by polynomial expressions, so phase and inverse generation suffice. -/
theorem h252LocalizedZ5Coordinate_surjective_of_phase_ranges
    (hz : ∀ i, h252LocalizedPhaseVars i ∈ h252LocalizedZ5Coordinate.range)
    (ht : ∀ i, h252LocalizedInverseVars i ∈ h252LocalizedZ5Coordinate.range) :
    Function.Surjective h252LocalizedZ5Coordinate := by
  let z := h252LocalizedPhaseVars
  let t := h252LocalizedInverseVars
  let w := h252LocalizedTorusVar 5
  let x := h252LocalizedTorusVar 6
  let D := h252TorusDVector z
  let T := t 0 * t 1 * t 2 * t 3 * t 4
  have hu (i : Fin 5) : z i * t i = 1 := h252LocalizedPhaseVars_units i
  have hs : w * D = 1 := by
    have h := rurInverseGenerator6_quotient_zero
    rw [rurInverseGenerator6_eval] at h
    change h252LocalizedTorusVar 5 * h252TorusD (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 4) = 1
    exact sub_eq_zero.mp h
  have hd : D * T = 1 := by
    calc
      D * T = (z 0 * t 0) * (z 1 * t 1) * (z 2 * t 2) * (z 3 * t 3) * (z 4 * t 4) := by
        simp only [D, T, h252TorusDVector, h252TorusD]
        ring
      _ = 1 := by rw [hu 0, hu 1, hu 2, hu 3, hu 4]; ring
  have hw : w = T := by
    calc
      w = w * (D * T) := by rw [hd, mul_one]
      _ = T := by rw [← mul_assoc, hs, one_mul]
  have hwmem : w ∈ h252LocalizedZ5Coordinate.range := by
    rw [hw]
    exact h252LocalizedZ5Coordinate.range.mul_mem
      (h252LocalizedZ5Coordinate.range.mul_mem
        (h252LocalizedZ5Coordinate.range.mul_mem
          (h252LocalizedZ5Coordinate.range.mul_mem (ht 0) (ht 1)) (ht 2)) (ht 3)) (ht 4)
  have hc : (z 4) ^ 2 - 2 * x * z 4 - 1 = 0 := by
    change (h252LocalizedTorusVar 4) ^ 2 -
      2 * h252LocalizedTorusVar 6 * h252LocalizedTorusVar 4 - 1 = 0
    simpa only [rurInverseGenerator7_eval] using rurInverseGenerator7_quotient_zero
  have he : 2 * x = z 4 - t 4 := by
    linear_combination -(t 4) * hc + (z 4 - 2 * x) * hu 4
  have hi : (2 : H252LocalizedTorusAlgebra) * algebraMap ℂ H252LocalizedTorusAlgebra (1 / 2) = 1 := by
    have h := congrArg (algebraMap ℂ H252LocalizedTorusAlgebra)
      (show (2 : ℂ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  have hx : x = algebraMap ℂ H252LocalizedTorusAlgebra (1 / 2) * (z 4 - t 4) := by
    calc
      x = 1 * x := by ring
      _ = (2 * algebraMap ℂ H252LocalizedTorusAlgebra (1 / 2)) * x := by rw [hi]
      _ = algebraMap ℂ H252LocalizedTorusAlgebra (1 / 2) * (2 * x) := by ring
      _ = _ := by rw [he]
  have hxmem : x ∈ h252LocalizedZ5Coordinate.range := by
    rw [hx]
    exact h252LocalizedZ5Coordinate.range.mul_mem
      (h252LocalizedZ5Coordinate.range.algebraMap_mem (1 / 2))
      (h252LocalizedZ5Coordinate.range.sub_mem (hz 4) (ht 4))
  apply coordinate_surjective_of_variables_in_range
  intro i
  change h252LocalizedTorusVar i ∈ h252LocalizedZ5Coordinate.range
  fin_cases i
  · simpa [h252LocalizedPhaseVars] using hz 0
  · simpa [h252LocalizedPhaseVars] using hz 1
  · simpa [h252LocalizedPhaseVars] using hz 2
  · simpa [h252LocalizedPhaseVars] using hz 3
  · simpa [h252LocalizedPhaseVars] using hz 4
  · exact hwmem
  · exact hxmem

end
end Biunimodular.F11
