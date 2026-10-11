/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252ComplexPhaseSemantics
import Biunimodular.F11.H252UniversalElimination

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

/-- Necessity for the full original complexified phase system, in arbitrary
complex algebras. This permits specialization to its quotient coordinate ring. -/
theorem h252ComplexPhaseForward {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (hc : ∀ i, a i ^ 2 + b i ^ 2 = 1)
    (h1 : h252ComplexPhaseE1 a b = 0) (h2 : h252ComplexPhaseE2 a b = 0)
    (h3 : h252ComplexPhaseE3 a b = 0) (h4 : h252ComplexPhaseE4 a b = 0)
    (h5 : h252ComplexPhaseE5 a b = 0) :
    integerCoefficientEval ((algebraMap ℂ R Complex.I) * b 4) h252RurHCoeffs = 0 := by
  let z := h252ComplexPhaseZ a b
  let t := h252ComplexPhaseInverse a b
  let w := t 0 * t 1 * t 2 * t 3 * t 4
  have hu : ∀ i, z i * t i = 1 := h252ComplexPhase_units a b hc
  have hs : w * h252TorusD (z 0) (z 1) (z 2) (z 3) (z 4) = 1 := by
    calc
      _ = (z 0 * t 0) * (z 1 * t 1) * (z 2 * t 2) *
          (z 3 * t 3) * (z 4 * t 4) := by simp only [w, h252TorusD]; ring
      _ = 1 := by rw [hu 0, hu 1, hu 2, hu 3, hu 4]; ring
  have hS : h252TorusS (z 0) (z 1) (z 2) (z 3) w (z 4) = 0 :=
    sub_eq_zero.mpr hs
  have hcoord : (z 4) ^ 2 - 1 =
      2 * (z 4) * ((algebraMap ℂ R Complex.I) * b 4) := by
    calc
      _ = (z 4) ^ 2 - z 4 * t 4 := by rw [hu 4]
      _ = _ := by simp only [z, t, h252ComplexPhaseZ, h252ComplexPhaseInverse]; ring
  exact h252UniversalElimination (z 0) (z 1) (z 2) (z 3) w (z 4)
    ((algebraMap ℂ R Complex.I) * b 4)
    (h252ComplexPhaseE1_torus a b hc h1) (h252ComplexPhaseE2_torus a b hc h2)
    (h252ComplexPhaseE3_torus a b hc h3) (h252ComplexPhaseE4_torus a b hc h4)
    (h252ComplexPhaseE5_torus a b hc h5) hS hcoord

end

end Biunimodular.F11
