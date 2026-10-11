/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryZModPower11
import Biunimodular.F11.FullSymmetryProjectiveWeylGenerators11

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace Biunimodular.F11

private theorem commute_powerZModTen11 {G : Type*} [Group G]
    (D C : G) (hD : D ^ 10 = 1) (hCD : C * D = D * C)
    (a : ZMod 10) : C * dPower11 D hD a = dPower11 D hD a * C := by
  rw [← ZMod.natCast_zmod_val a, dPower11_natCast]
  induction a.val with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        C * (D ^ n * D) = (C * D ^ n) * D := by group
        _ = (D ^ n * C) * D := by rw [ih]
        _ = D ^ n * D * C := by rw [mul_assoc, hCD, ← mul_assoc]

private theorem invert_powerZModTen11 {G : Type*} [Group G]
    (D F : G) (hD : D ^ 10 = 1) (hFD : F * D = D⁻¹ * F)
    (a : ZMod 10) :
    F * dPower11 D hD a = dPower11 D hD (-a) * F := by
  rw [← ZMod.natCast_zmod_val a, dPower11_natCast,
    dPower11_neg, dPower11_natCast, ← inv_pow]
  induction a.val with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        F * (D ^ n * D) = (F * D ^ n) * D := by group
        _ = (D⁻¹ ^ n * F) * D := by rw [ih]
        _ = D⁻¹ ^ n * D⁻¹ * F := by
          calc
            (D⁻¹ ^ n * F) * D = D⁻¹ ^ n * (F * D) := by rw [mul_assoc]
            _ = D⁻¹ ^ n * (D⁻¹ * F) := by rw [hFD]
            _ = D⁻¹ ^ n * D⁻¹ * F := by rw [mul_assoc]

/-- The defining Fourier/dilation/conjugation relations induce a
representation of the forty-element normal-form group. -/
def linearFourierRepresentation11 {G : Type*} [Group G]
    (D C F : G)
    (hD : D ^ 10 = 1) (hC : C ^ 2 = 1)
    (hF : F ^ 2 = D ^ 5)
    (hCD : C * D = D * C)
    (hFD : F * D = D⁻¹ * F)
    (hFC : F * C = D ^ 5 * C * F) :
    LinearFourierLabel11 →* G := by
  let P := dPower11 D hD
  let w : LinearFourierLabel11 → G := fun k =>
    P k.dilate * (if k.conjugate then C else 1) *
      (if k.fourier then F else 1)
  have hPadd (a b : ZMod 10) : P (a + b) = P a * P b :=
    dPower11_add D hD a b
  have hPzero : P 0 = 1 := dPower11_zero D hD
  have hPfive : P 5 = D ^ 5 := dPower11_natCast D hD 5
  have hPcomm (a : ZMod 10) : C * P a = P a * C :=
    commute_powerZModTen11 D C hD hCD a
  have hPinvert (a : ZMod 10) : F * P a = P (-a) * F :=
    invert_powerZModTen11 D F hD hFD a
  have hCtwo : C * C = 1 := by simpa [pow_two] using hC
  have hFtwo : F * F = P 5 := by simpa [pow_two, hPfive] using hF
  have hFCp : F * C = P 5 * C * F := by simpa [hPfive] using hFC
  have hPcomm' (a : ZMod 10) (X : G) :
      C * (P a * X) = P a * (C * X) := by
    rw [← mul_assoc, hPcomm, mul_assoc]
  have hPinvert' (a : ZMod 10) (X : G) :
      F * (P a * X) = P (-a) * (F * X) := by
    rw [← mul_assoc, hPinvert, mul_assoc]
  have hFCp' (X : G) : F * (C * X) = P 5 * (C * (F * X)) := by
    rw [← mul_assoc, hFCp]
    group
  have hCtwo' (X : G) : C * (C * X) = X := by
    rw [← mul_assoc, hCtwo, one_mul]
  have hFtwo' (X : G) : F * (F * X) = P 5 * X := by
    rw [← mul_assoc, hFtwo]
  refine { toFun := w, map_one' := ?_, map_mul' := ?_ }
  · change w ⟨0, false, false⟩ = 1
    simp [w, hPzero]
  · intro x y
    rcases x with ⟨a, c, f⟩
    rcases y with ⟨b, e, g⟩
    change w (linearFourierMul11 ⟨a, c, f⟩ ⟨b, e, g⟩) =
      w ⟨a, c, f⟩ * w ⟨b, e, g⟩
    cases c <;> cases f <;> cases e <;> cases g
    all_goals
      simp [w, linearFourierMul11, fiveBit11, hPadd, hPfive]
      try simp only [mul_assoc, hPcomm', hPinvert', hFCp',
        hCtwo', hCtwo, hFtwo, mul_one]
      try simp only [← mul_assoc, hPcomm, hPinvert, hFCp]
      try simp only [mul_assoc, hPfive]
      try group
      try simp only [mul_assoc, hCtwo, one_mul]

end Biunimodular.F11
