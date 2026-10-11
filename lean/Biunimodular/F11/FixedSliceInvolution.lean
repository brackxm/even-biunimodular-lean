/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceCommonProduct

set_option autoImplicit false

namespace Biunimodular.F11

section Field

variable {K : Type*} [Field K]

/-- Fourier action on the fixed slice. -/
def fixedSliceJ (F : Even6 K →ₗ[K] Even6 K) (h : Even6 K) : Even6 K := F h

/-- The fixed-slice equations are preserved when Fourier squares to a scalar.
This is the natural projective formulation for an unnormalised DFT. -/
theorem fixedSliceEq_fourier_of_sq_smul
    {F : Even6 K →ₗ[K] Even6 K} {c : K}
    (hF2 : ∀ h, F (F h) = c • h)
    {h : Even6 K}
    (hh : FixedSliceEq F h) :
    FixedSliceEq F (F h) := by
  intro j
  simp only [FixedSliceEq, fourierCoordProduct] at hh ⊢
  rw [hF2]
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    F h j * (c * h j) = c * (h j * F h j) := by ring
    _ = c * (h 0 * F h 0) := by rw [hh j]
    _ = F h 0 * (c * h 0) := by ring

/-- The fixed-slice equations are preserved by an involutive Fourier map. -/
theorem fixedSliceEq_fourier
    {F : Even6 K →ₗ[K] Even6 K}
    (hF2 : ∀ h, F (F h) = h)
    {h : Even6 K}
    (hh : FixedSliceEq F h) :
    FixedSliceEq F (F h) :=
  fixedSliceEq_fourier_of_sq_smul (c := 1)
    (fun h => by simpa using hF2 h) hh

/-- Fourier is an involution on vectors if `F²=1`. -/
theorem fixedSliceJ_involutive
    {F : Even6 K →ₗ[K] Even6 K}
    (hF2 : ∀ h, F (F h) = h) :
    Function.Involutive (fixedSliceJ F) := by
  intro h
  exact hF2 h

/-- The common product is invariant under the Fourier involution. -/
theorem commonProduct_fourier
    {F : Even6 K →ₗ[K] Even6 K}
    (hF2 : ∀ h, F (F h) = h)
    (h : Even6 K) :
    fourierCoordProduct F (F h) 0 = fourierCoordProduct F h 0 := by
  simp [fourierCoordProduct, hF2, mul_comm]

end Field

end Biunimodular.F11
