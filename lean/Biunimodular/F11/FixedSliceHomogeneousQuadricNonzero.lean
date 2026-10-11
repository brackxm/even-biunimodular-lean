/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceHomogeneousRegularCriterion

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

theorem even11Lift_delta_zero :
    even11Lift (Pi.single (0 : Fin 6) (1 : ℂ)) = Pi.single (0 : ZMod 11) (1 : ℂ) := by
  have hz : ∀ t : ZMod 11, even11Coordinate t = 0 ↔ t = 0 := by native_decide
  funext t
  change (Pi.single (0 : Fin 6) (1 : ℂ) : Fin 6 → ℂ) (even11Coordinate t) =
    (Pi.single (0 : ZMod 11) (1 : ℂ) : ZMod 11 → ℂ) t
  simp only [Pi.single_apply, hz]

theorem even11FourierNormalized_delta_zero_zero :
    even11FourierNormalized (Pi.single (0 : Fin 6) (1 : ℂ)) 0 =
      (Real.sqrt 11 : ℂ)⁻¹ := by
  simp [even11FourierNormalized, even11Fourier_apply, ZMod.dft_apply_zero,
    even11Lift_delta_zero]

/-- Each original homogeneous quadric is nonzero, as witnessed at the
zeroth coordinate vector. -/
theorem even11FixedSliceHomogeneousQuadric_nonzero (j : Fin 5) :
    fixedSliceHomogeneousQuadric even11FourierNormalized j.succ ≠ 0 := by
  intro hz
  have h := congrArg (aeval (Pi.single (0 : Fin 6) (1 : ℂ))) hz
  rw [fixedSliceHomogeneousQuadric_eval] at h
  simp only [map_zero, fourierCoordProduct, Pi.single_apply,
    Fin.succ_ne_zero, ↓reduceIte, zero_mul, even11FourierNormalized_delta_zero_zero,
    one_mul, zero_sub, neg_eq_zero] at h
  have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 11))
  exact (inv_ne_zero hs) h

/-- The first prefix colon condition is unconditional: the polynomial ring
is a domain and the first original quadric is nonzero. -/
theorem even11FixedSliceHomogeneousGenerators_first_colon
    (x : MvPolynomial (Fin 6) ℂ)
    (h : even11FixedSliceHomogeneousGenerators[0] * x ∈
      Ideal.ofList (even11FixedSliceHomogeneousGenerators.take 0)) :
    x ∈ Ideal.ofList (even11FixedSliceHomogeneousGenerators.take 0) := by
  have hq : even11FixedSliceHomogeneousGenerators[0] ≠ 0 := by
    simpa [even11FixedSliceHomogeneousGenerators, fixedSliceHomogeneousGenerators] using
      even11FixedSliceHomogeneousQuadric_nonzero (0 : Fin 5)
  simpa using (mul_eq_zero.mp (by simpa using h)).resolve_left hq

end
end Biunimodular.F11
