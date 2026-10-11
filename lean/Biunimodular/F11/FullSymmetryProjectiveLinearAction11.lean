/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryLinearRepresentation11

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

/-- The concrete forty-element Fourier/dilation/conjugation action on
all projective length-eleven signals. -/
def projectiveLinearFourierPerm11 :
    LinearFourierLabel11 →* Equiv.Perm FullProjectiveSignal11 :=
  linearFourierRepresentation11
    projectiveD2Perm11 projectiveCPerm11 projectiveFPerm11
    projectiveD2Perm11_pow_ten
    projectiveCPerm11_sq
    (by rw [projectiveFPerm11_sq, projectiveD2Perm11_pow_five])
    projectiveCPerm11_comm_dilate
    projectiveFPerm11_dilate
    (by rw [projectiveFPerm11_conj, projectiveD2Perm11_pow_five])

instance : MulAction LinearFourierLabel11 FullProjectiveSignal11 where
  smul k z := projectiveLinearFourierPerm11 k z
  one_smul z := by
    change projectiveLinearFourierPerm11 1 z = z
    rw [map_one]
    rfl
  mul_smul k l z := by
    change projectiveLinearFourierPerm11 (k * l) z =
      projectiveLinearFourierPerm11 k
        (projectiveLinearFourierPerm11 l z)
    rw [map_mul]
    rfl

theorem projectiveLinearFourierPerm11_D :
    projectiveLinearFourierPerm11 linearD11 =
      projectiveD2Perm11 := by
  change dPower11 projectiveD2Perm11 projectiveD2Perm11_pow_ten 1 *
      1 * 1 = projectiveD2Perm11
  simpa only [mul_one, pow_one, Nat.cast_one] using
    (dPower11_natCast projectiveD2Perm11 projectiveD2Perm11_pow_ten 1)

theorem projectiveLinearFourierPerm11_C :
    projectiveLinearFourierPerm11 linearC11 =
      projectiveCPerm11 := by
  change dPower11 projectiveD2Perm11 projectiveD2Perm11_pow_ten 0 *
      projectiveCPerm11 * 1 = projectiveCPerm11
  simp [dPower11_zero]

theorem projectiveLinearFourierPerm11_F :
    projectiveLinearFourierPerm11 linearF11 =
      projectiveFPerm11 := by
  change dPower11 projectiveD2Perm11 projectiveD2Perm11_pow_ten 0 *
      1 * projectiveFPerm11 = projectiveFPerm11
  simp [dPower11_zero]

theorem projectiveLinearFourierPerm11_R :
    projectiveLinearFourierPerm11 linearR11 =
      projectiveRPerm11 := by
  change dPower11 projectiveD2Perm11 projectiveD2Perm11_pow_ten 5 *
      1 * 1 = projectiveRPerm11
  simpa only [mul_one, Nat.cast_ofNat] using
    (dPower11_natCast projectiveD2Perm11 projectiveD2Perm11_pow_ten 5).trans
      projectiveD2Perm11_pow_five

end
end Biunimodular.F11
