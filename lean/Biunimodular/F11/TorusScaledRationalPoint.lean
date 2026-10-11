/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientDifferential
import Mathlib.Algebra.Algebra.Basic

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

def torusScaledRationalValue {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : R) (scale : ℤ) (coefficients : List ℤ) : R :=
  algebraMap ℚ R ((scale : ℚ)⁻¹) * integerCoefficientEval a coefficients

theorem torusIntegerScale_isUnit {R : Type*} [CommRing R] [Algebra ℚ R]
    (scale : ℤ) (h : scale ≠ 0) : IsUnit (scale : R) := by
  have hu : IsUnit (scale : ℚ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast h)
  simpa only [map_intCast] using hu.map (algebraMap ℚ R)

theorem torusScaledRationalValue_scaled {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : R) (scale : ℤ) (h : scale ≠ 0) (coefficients : List ℤ) :
    (scale : R) * torusScaledRationalValue a scale coefficients =
      integerCoefficientEval a coefficients := by
  have hq : (scale : ℚ) ≠ 0 := by exact_mod_cast h
  have hm := congrArg (algebraMap ℚ R) (mul_inv_cancel₀ hq)
  simp only [map_mul, map_intCast, map_one] at hm
  simp only [torusScaledRationalValue, ← mul_assoc, hm, one_mul]

theorem torusScaledRationalValue_isUnit {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : R) (scale : ℤ) (hs : scale ≠ 0) (c v : List ℤ)
    (hcv : integerCoefficientEval a c * integerCoefficientEval a v = (scale : R)^2) :
    IsUnit (torusScaledRationalValue a scale c) := by
  apply IsUnit.of_mul_eq_one (torusScaledRationalValue a scale v)
  apply ((torusIntegerScale_isUnit (R := R) scale hs).pow 2).mul_left_cancel
  have hc := torusScaledRationalValue_scaled a scale hs c
  have hv := torusScaledRationalValue_scaled a scale hs v
  calc
    _ = ((scale : R) * torusScaledRationalValue a scale c) *
        ((scale : R) * torusScaledRationalValue a scale v) := by ring
    _ = (scale : R)^2 := by rw [hc, hv, hcv]
    _ = _ := by ring

end
end Biunimodular.F11
