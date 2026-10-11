/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252ComplexPhaseSemantics

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

def h252ComplexPairA (z t : ℂ) : ℂ := (z + t) / 2
def h252ComplexPairB (z t : ℂ) : ℂ := (z - t) / (2 * Complex.I)

theorem h252ComplexPair_z (z t : ℂ) :
    h252ComplexPairA z t + Complex.I * h252ComplexPairB z t = z := by
  simp only [h252ComplexPairA, h252ComplexPairB]
  field_simp
  ring

theorem h252ComplexPair_inverse (z t : ℂ) :
    h252ComplexPairA z t - Complex.I * h252ComplexPairB z t = t := by
  simp only [h252ComplexPairA, h252ComplexPairB]
  field_simp
  ring

theorem h252ComplexPair_circle (z t : ℂ) :
    h252ComplexPairA z t ^ 2 + h252ComplexPairB z t ^ 2 = z * t := by
  simp only [h252ComplexPairA, h252ComplexPairB, div_pow, mul_pow, Complex.I_sq]
  norm_num
  ring

theorem h252ComplexPair_coordinate (z t x : ℂ) (hu : z * t = 1)
    (hc : z ^ 2 - 1 = 2 * z * x) : Complex.I * h252ComplexPairB z t = x := by
  have hz : z ≠ 0 := by intro hz; simp [hz] at hu
  have hs : z - t = 2 * x := by
    apply mul_left_cancel₀ hz
    linear_combination hc - hu
  calc
    _ = (z - t) / 2 := by simp only [h252ComplexPairB]; field_simp
    _ = x := by rw [hs]; ring

end

end Biunimodular.F11
