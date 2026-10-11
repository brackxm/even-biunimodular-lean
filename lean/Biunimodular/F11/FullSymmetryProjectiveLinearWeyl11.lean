/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectiveLinearAction11

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

theorem linearFourierLabel11_normal_form (k : LinearFourierLabel11) :
    k = linearD11 ^ k.dilate.val *
      (if k.conjugate then linearC11 else 1) *
      (if k.fourier then linearF11 else 1) := by
  native_decide +revert

private def LinearWeylIntertwines11 (k : LinearFourierLabel11) : Prop :=
  ∀ p : WeylLabels11, ∀ z : FullProjectiveSignal11,
    k • (p • z) =
      (linearFourierWeylAction11 k p) • (k • z)

private theorem linearWeylIntertwines_one11 :
    LinearWeylIntertwines11 1 := by
  intro p z
  simp

private theorem linearWeylIntertwines_mul11
    {k l : LinearFourierLabel11}
    (hk : LinearWeylIntertwines11 k)
    (hl : LinearWeylIntertwines11 l) :
    LinearWeylIntertwines11 (k * l) := by
  intro p z
  rw [mul_smul, hl, hk, mul_smul, map_mul]
  rfl

private theorem linearWeylIntertwines_pow11
    {k : LinearFourierLabel11}
    (hk : LinearWeylIntertwines11 k) (n : ℕ) :
    LinearWeylIntertwines11 (k ^ n) := by
  induction n with
  | zero => simpa using linearWeylIntertwines_one11
  | succ n ih =>
      rw [pow_succ]
      exact linearWeylIntertwines_mul11 ih hk

private theorem linearWeylIntertwines_D11 :
    LinearWeylIntertwines11 linearD11 := by
  intro p z
  change projectiveLinearFourierPerm11 linearD11 (p • z) =
    (linearFourierWeylAction11 linearD11 p) •
      projectiveLinearFourierPerm11 linearD11 z
  rw [projectiveLinearFourierPerm11_D]
  exact projectiveD2Perm11_weyl_intertwine p z

private theorem linearWeylIntertwines_C11 :
    LinearWeylIntertwines11 linearC11 := by
  intro p z
  change projectiveLinearFourierPerm11 linearC11 (p • z) =
    (linearFourierWeylAction11 linearC11 p) •
      projectiveLinearFourierPerm11 linearC11 z
  rw [projectiveLinearFourierPerm11_C]
  exact projectiveCPerm11_weyl_intertwine p z

private theorem linearWeylIntertwines_F11 :
    LinearWeylIntertwines11 linearF11 := by
  intro p z
  change projectiveLinearFourierPerm11 linearF11 (p • z) =
    (linearFourierWeylAction11 linearF11 p) •
      projectiveLinearFourierPerm11 linearF11 z
  rw [projectiveLinearFourierPerm11_F]
  exact projectiveFPerm11_weyl_intertwine p z

/-- Every element of the forty-element linear group acts compatibly with
the Weyl automorphism used in the semidirect product. -/
theorem projectiveLinearFourier_weyl_intertwine
    (k : LinearFourierLabel11) (p : WeylLabels11)
    (z : FullProjectiveSignal11) :
    k • (p • z) =
      (linearFourierWeylAction11 k p) • (k • z) := by
  have hD := linearWeylIntertwines_pow11 linearWeylIntertwines_D11
    k.dilate.val
  have hC : LinearWeylIntertwines11
      (if k.conjugate then linearC11 else 1) := by
    split
    · exact linearWeylIntertwines_C11
    · exact linearWeylIntertwines_one11
  have hF : LinearWeylIntertwines11
      (if k.fourier then linearF11 else 1) := by
    split
    · exact linearWeylIntertwines_F11
    · exact linearWeylIntertwines_one11
  rw [linearFourierLabel11_normal_form k]
  exact linearWeylIntertwines_mul11
    (linearWeylIntertwines_mul11 hD hC) hF p z

end
end Biunimodular.F11
