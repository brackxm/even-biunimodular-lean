/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectiveAction11
import Biunimodular.F11.FullSymmetryProjectivePhysical11

set_option autoImplicit false

namespace Biunimodular.F11

open scoped LinearAlgebra.Projectivization

noncomputable section

private noncomputable instance (z : FullProjectiveSignal11) :
    Fintype (MulAction.orbit fullLinearSubgroup11 z) :=
  (Finite.finite_mulAction_orbit z).fintype

theorem fullProjectiveOfSignal11_injective :
    Function.Injective fullProjectiveOfSignal11 := by
  intro z w h
  rw [fullProjectiveOfSignal11] at h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrFun hc (0 : ZMod 11)
  have hc1 : c = 1 := by
    simpa [Pi.smul_apply, signalOnZMod11_zero] using h0
  rw [hc1] at hc
  have hsignal : z.signal = w.signal := by
    funext j
    have hj := congrFun hc (j.val : ZMod 11)
    simpa [Pi.smul_apply, signalOnZMod11,
      ZMod.val_natCast_of_lt j.isLt] using hj.symm
  cases z
  cases w
  cases hsignal
  rfl

private noncomputable instance (z : FullProjectiveSignal11) :
    Fintype (MulAction.orbit FullSymmetryLabel11 z) :=
  (Finite.finite_mulAction_orbit z).fintype

theorem fullReflection11_fixed_signal (z : ZeroAutocorrSignal11) :
    fullReflection11 • fullProjectiveOfSignal11 z =
      fullProjectiveOfSignal11 z := by
  change fullProjectiveSymmetryPerm11 fullReflection11
    (fullProjectiveOfSignal11 z) = fullProjectiveOfSignal11 z
  rw [fullReflection11, fullProjectiveSymmetryPerm11_linear,
    projectiveLinearFourierPerm11_R]
  exact fullProjectiveOfSignal11_reflection z

theorem fullWeylSubgroup11_signal_stabilizer_trivial
    (z : ZeroAutocorrSignal11)
    (hNonG : ¬ IsQuadraticGaussianSignal11 z)
    (g : FullSymmetryLabel11)
    (hg : g ∈ fullWeylSubgroup11)
    (hgz : g • fullProjectiveOfSignal11 z =
      fullProjectiveOfSignal11 z) : g = 1 := by
  obtain ⟨p, rfl⟩ := hg
  change fullProjectiveSymmetryPerm11 (SemidirectProduct.inl p)
    (fullProjectiveOfSignal11 z) = fullProjectiveOfSignal11 z at hgz
  rw [fullProjectiveSymmetryPerm11_weyl] at hgz
  have hp : p = 1 :=
    fullProjectiveOfSignal11_weyl_stabilizer_trivial z hNonG p hgz
  rw [hp, map_one]

/-- The abstract 1210-orbit theorem now applies to the actual projective
Fourier/Weyl action; the hypothesis is the ten-point linear orbit. -/
theorem fullProjectiveOfSignal11_orbit_card_1210
    (z : ZeroAutocorrSignal11)
    (hNonG : ¬ IsQuadraticGaussianSignal11 z)
    (hKorbit : Fintype.card
      (MulAction.orbit fullLinearSubgroup11
        (fullProjectiveOfSignal11 z)) = 10) :
    Fintype.card
      (MulAction.orbit FullSymmetryLabel11
        (fullProjectiveOfSignal11 z)) = 1210 := by
  exact fullSymmetryLabel11_orbit_card_1210
    (fullProjectiveOfSignal11 z)
    (fullReflection11_fixed_signal z)
    (fullWeylSubgroup11_signal_stabilizer_trivial z hNonG)
    hKorbit

end
end Biunimodular.F11
