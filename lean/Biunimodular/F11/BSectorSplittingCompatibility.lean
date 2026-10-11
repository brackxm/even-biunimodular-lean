/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.InvariantBMonicTransform

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable def BMonicQOriginal : ℚ[X] :=
  invariantBMonicTransform.map (Int.castRingHom ℚ)

noncomputable def BOriginalQ : ℚ[X] :=
  invariantB.map (Int.castRingHom ℚ)

/-- The monic root transform splits in the original B polynomial's
splitting field. -/
theorem bMonic_splits_in_original_splittingField :
    (BMonicQOriginal.map (algebraMap ℚ BOriginalQ.SplittingField)).Splits := by
  let K := BOriginalQ.SplittingField
  let a : ℚ := 279841
  have hBne : BOriginalQ ≠ 0 := by
    simpa only [BOriginalQ] using invariantB_irreducible_over_Q_closed.ne_zero
  have hlead : (algebraMap ℚ K) BOriginalQ.leadingCoeff ≠ 0 := by
    intro h
    apply leadingCoeff_ne_zero.mpr hBne
    exact (algebraMap ℚ K).injective (by simpa only [map_zero] using h)
  have hmap : (BOriginalQ.scaleRoots a).map (algebraMap ℚ K) =
      (BOriginalQ.map (algebraMap ℚ K)).scaleRoots (algebraMap ℚ K a) :=
    Polynomial.map_scaleRoots BOriginalQ a (algebraMap ℚ K) hlead
  have hs := (SplittingField.splits BOriginalQ).scaleRoots (algebraMap ℚ K a)
  have hpoly : BMonicQOriginal.map (algebraMap ℚ K) =
      (BOriginalQ.map (algebraMap ℚ K)).scaleRoots (algebraMap ℚ K a) *
        C ((algebraMap ℚ K) a⁻¹) := by
    unfold BMonicQOriginal
    rw [invariantBMonicTransform_over_Q]
    change ((BOriginalQ.scaleRoots a) * C a⁻¹).map (algebraMap ℚ K) = _
    rw [Polynomial.map_mul, hmap, Polynomial.map_C]
  rw [hpoly]
  exact hs.mul (Splits.C _)

end Biunimodular.F11
