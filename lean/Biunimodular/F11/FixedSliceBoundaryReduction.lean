/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceCommonProduct

set_option autoImplicit false

namespace Biunimodular.F11

/-!
This module packages the exact logical use of prime Fourier uncertainty.
The genuine finite-Fourier uncertainty theorem can be connected later through
one adapter; no fixed-slice root certificate depends on numerical boxes.
-/

section Field

variable {K : Type*} [Field K]

/-- Abstract form of the only uncertainty consequence needed by the F11 classification:
no nonzero vector can have coordinatewise-disjoint support from its Fourier
image. -/
def NoDisjointFourierSupport (F : Even6 K →ₗ[K] Even6 K) : Prop :=
  ∀ h : Even6 K, h ≠ 0 → ¬ (∀ j, h j = 0 ∨ F h j = 0)

/-- Multiplying the Fourier operator by a nonzero scalar preserves the exact
coordinatewise support-uncertainty statement. -/
theorem noDisjointFourierSupport_smul_iff
    {F : Even6 K →ₗ[K] Even6 K} {c : K} (hc : c ≠ 0) :
    NoDisjointFourierSupport (c • F) ↔ NoDisjointFourierSupport F := by
  constructor
  · intro hu h hnz hdis
    apply hu h hnz
    intro j
    rcases hdis j with hj | hFj
    · exact Or.inl hj
    · right
      simp [hFj]
  · intro hu h hnz hdis
    apply hu h hnz
    intro j
    rcases hdis j with hj | hFj
    · exact Or.inl hj
    · right
      simpa [hc] using hFj

/-- Prime Fourier uncertainty removes the entire projective boundary in one
step: the common product cannot vanish at a nonzero fixed-slice point. -/
theorem fixedSlice_common_ne_zero_of_uncertainty
    {F : Even6 K →ₗ[K] Even6 K}
    (hu : NoDisjointFourierSupport F)
    {h : Even6 K}
    (hnz : h ≠ 0)
    (hh : FixedSliceEq F h) :
    fourierCoordProduct F h 0 ≠ 0 := by
  intro hz
  exact hu h hnz (fixedSlice_zero_common_support_disjoint hh hz)

/-- Consequently all physical/projective fixed-slice coordinates and their
Fourier coordinates are nonzero. -/
theorem fixedSlice_nowhere_coordinate_zero
    {F : Even6 K →ₗ[K] Even6 K}
    (hu : NoDisjointFourierSupport F)
    {h : Even6 K}
    (hnz : h ≠ 0)
    (hh : FixedSliceEq F h) :
    (∀ j, h j ≠ 0) ∧ (∀ j, F h j ≠ 0) := by
  have hc := fixedSlice_common_ne_zero_of_uncertainty hu hnz hh
  exact ⟨fixedSlice_all_h_nonzero hh hc, fixedSlice_all_Fh_nonzero hh hc⟩

end Field

end Biunimodular.F11
