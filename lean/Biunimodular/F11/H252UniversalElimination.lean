/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252UniversalTorusIdentity
import Biunimodular.F11.H252RurCircleLiftCoefficients

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

/-- The eliminant vanishes in every complex algebra satisfying the actual
localized torus equations. In particular this applies to the coordinate
quotient itself and proves ideal membership, not just pointwise vanishing. -/
theorem h252UniversalElimination {R : Type*} [CommRing R] [Algebra ℂ R]
    (z1 z2 z3 z4 w z5 x : R)
    (h1 : h252TorusF1 z1 z2 z3 z4 z5 = 0)
    (h2 : h252TorusF2 z1 z2 z3 z4 z5 = 0)
    (h3 : h252TorusF3 z1 z2 z3 z4 z5 = 0)
    (h4 : h252TorusF4 z1 z2 z3 z4 z5 = 0)
    (h5 : h252TorusF5 z1 z2 z3 z4 z5 = 0)
    (hS : h252TorusS z1 z2 z3 z4 w z5 = 0)
    (hcoord : z5 ^ 2 - 1 = 2 * z5 * x) :
    integerCoefficientEval x h252RurHCoeffs = 0 := by
  have hs : w * h252TorusD z1 z2 z3 z4 z5 = 1 := by
    exact sub_eq_zero.mp hS
  have hid := h252UniversalTorusIdentity z1 z2 z3 z4 w z5
  simp only [h252UniversalTorusIdentityLeft, h252UniversalTorusIdentityRight,
    h1, h2, h3, h4, h5, mul_zero, add_zero] at hid
  have he : integerCoefficientEval z5 h252TorusEliminantCoeffs11 = 0 := by
    calc
      _ = 1 * integerCoefficientEval z5 h252TorusEliminantCoeffs11 := by simp
      _ = (w * h252TorusD z1 z2 z3 z4 z5) *
          integerCoefficientEval z5 h252TorusEliminantCoeffs11 := by rw [hs]
      _ = w * (h252TorusD z1 z2 z3 z4 z5 *
          integerCoefficientEval z5 h252TorusEliminantCoeffs11) := by ring
      _ = 0 := by rw [hid, mul_zero]
  have hc : integerCoefficientEval z5 h252CircleLiftCoeffs11 = 0 := by
    have h := h252UniversalCircleFactor z5
    rw [he, zero_mul] at h
    exact h.symm
  have hb := integerCoefficientEval_eq_of_equal z5 _ _ h252RurCircleLift_coefficients
  rw [integerCoefficientEval_scale, integerCoefficientEval_scale, hc, mul_zero] at hb
  have hlu : IsUnit (h252RurOriginalLeading : R) := by
    have hl : (h252RurOriginalLeading : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt h252RurOriginalLeading_pos
    simpa using (isUnit_iff_ne_zero.mpr hl).map (algebraMap ℂ R)
  have hhom : integerCoefficientEval z5 (integerCoefficientHomogenize h252RurHCoeffs) = 0 :=
    hlu.mul_left_cancel (by simpa only [mul_zero] using hb.symm)
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil h252RurHCoeffs_nonempty
  have hlen : cs.length = 252 := by
    simpa [hcs] using h252RurHCoeffs_tail_length
  have hclear := integerCoefficientHomogenize_eval c cs z5 x hcoord
  rw [← hcs, hlen, hhom] at hclear
  have hzu : IsUnit z5 := by
    apply IsUnit.of_mul_eq_one_right (w * z1 * z2 * z3 * z4)
    calc
      _ = w * h252TorusD z1 z2 z3 z4 z5 := by simp only [h252TorusD]; ring
      _ = 1 := hs
  have h2u : IsUnit (2 : R) := by
    have h := (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map (algebraMap ℂ R)
    convert h using 1
    have ht : (2 : ℂ) = 1 + 1 := by norm_num
    rw [ht, map_add, map_one]
    ring
  exact ((h2u.mul hzu).pow 252).mul_left_cancel
    (by simpa only [mul_zero] using hclear.symm)

end

end Biunimodular.F11
