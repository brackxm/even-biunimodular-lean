/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ProofTactics

set_option autoImplicit false

namespace Biunimodular.F11

/-- Powers of an order-ten element indexed without choosing integer lifts. -/
def powerZModTen11 {G : Type*} [Group G] (d : G) (hd : d ^ 10 = 1) :
    ZMod 10 →+ Additive G :=
  ZMod.lift 10 ⟨MonoidHom.toAdditive (zpowersHom G d), by
    change d ^ (10 : ℤ) = 1
    simpa using hd⟩

def dPower11 {G : Type*} [Group G] (d : G) (hd : d ^ 10 = 1)
    (a : ZMod 10) : G :=
  Additive.toMul (powerZModTen11 d hd a)

theorem dPower11_add {G : Type*} [Group G] (d : G) (hd : d ^ 10 = 1)
    (a b : ZMod 10) :
    dPower11 d hd (a + b) = dPower11 d hd a * dPower11 d hd b := by
  change Additive.toMul (powerZModTen11 d hd (a + b)) = _
  rw [map_add]
  rfl

theorem dPower11_zero {G : Type*} [Group G] (d : G) (hd : d ^ 10 = 1) :
    dPower11 d hd 0 = 1 := by
  change Additive.toMul (powerZModTen11 d hd 0) = 1
  simp

theorem dPower11_natCast {G : Type*} [Group G] (d : G) (hd : d ^ 10 = 1)
    (n : ℕ) : dPower11 d hd (n : ZMod 10) = d ^ n := by
  let f : { f : ℤ →+ Additive G // f 10 = 0 } :=
    ⟨MonoidHom.toAdditive (zpowersHom G d), by
      change d ^ (10 : ℤ) = 1
      simpa using hd⟩
  have hs : powerZModTen11 d hd (n : ZMod 10) = f.1 (n : ℤ) := by
    change (ZMod.lift 10 f) ((n : ℤ) : ZMod 10) = f.1 (n : ℤ)
    exact ZMod.lift_coe 10 f (n : ℤ)
  change Additive.toMul (powerZModTen11 d hd (n : ZMod 10)) = d ^ n
  rw [hs]
  change d ^ (n : ℤ) = d ^ n
  simp

theorem dPower11_neg {G : Type*} [Group G] (d : G) (hd : d ^ 10 = 1)
    (a : ZMod 10) : dPower11 d hd (-a) = (dPower11 d hd a)⁻¹ := by
  change Additive.toMul (powerZModTen11 d hd (-a)) = _
  rw [map_neg]
  rfl

end Biunimodular.F11
