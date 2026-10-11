/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectivePhysical11
import Biunimodular.F11.Even11FourierPhaseAction11

set_option autoImplicit false

namespace Biunimodular.F11

open scoped LinearAlgebra.Projectivization

noncomputable section

theorem phaseSignalEquiv11_fullSignal (s : PhaseSolution11) :
    signalOnZMod11 (phaseSolutionSignalEquiv11 s) =
      phaseOnZMod11 s.1 := rfl

/-- On projective signal lines, the Fourier transform of a physical even
solution is exactly the line of the normalized Fourier phase solution. -/
theorem fullProjectiveFourier11_phaseSolution (s : PhaseSolution11) :
    fullProjectiveOfSignal11
      (phaseSolutionSignalEquiv11 (phaseSolution11Fourier s)) =
    fullProjectiveFourier11
      (fullProjectiveOfSignal11 (phaseSolutionSignalEquiv11 s)) := by
  let h : Even6 ℂ := phaseEvenVector11 s
  let gamma : ℂ := even11FourierNormalized h 0
  let g : Even6 ℂ := even11NormalizeFourier h
  have hgammaNorm : Complex.normSq gamma = 1 := by
    simpa [gamma, h, even11Lift_apply, even11Coordinate_zero] using
      phaseEvenVector11_fourier_normSq_one s 0
  have hgamma : gamma ≠ 0 := by
    intro hz
    simp [hz] at hgammaNorm
  have hg0 : g 0 = 1 := even11NormalizeFourier_zero h hgamma
  have htrans : phaseOnZMod11 (phaseSolution11Fourier s).1 = even11Lift g := by
    funext x
    have hx := phaseSignal11_phaseCoordsOfEven11 g (by simp [hg0])
      ⟨x.val, x.val_lt⟩
    simpa [phaseOnZMod11, phaseSolution11Fourier, g, hg0,
      ZMod.natCast_zmod_val] using hx
  let alpha : ℂ := gamma⁻¹ * (Real.sqrt 11 : ℂ)⁻¹
  have hscaled : phaseOnZMod11 (phaseSolution11Fourier s).1 =
      alpha • ZMod.dft (phaseOnZMod11 s.1) := by
    rw [htrans]
    funext x
    have hF := congrFun (even11Lift_fourierNormalized h) x
    simp [g, alpha, even11NormalizeFourier,
      even11FullFourierNormalized,
      even11Lift_apply, Pi.smul_apply, smul_eq_mul] at hF ⊢
    rw [hF]
    simp only [h, phaseEvenVector11_lift]
    ring
  simp only [fullProjectiveOfSignal11, fullProjectiveFourier11_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨alpha, by simpa only [phaseSignalEquiv11_fullSignal] using hscaled.symm⟩

end
end Biunimodular.F11
