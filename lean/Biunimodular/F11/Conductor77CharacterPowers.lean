/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Conductor77PrimitiveCharacter

set_option autoImplicit false
namespace Biunimodular.F11

theorem conductor77Character_square_order : orderOf (conductor77PrimitiveCharacter ^ 2) = 3 := by
  rw [orderOf_pow' conductor77PrimitiveCharacter (by decide : (2 : ℕ) ≠ 0),
    conductor77PrimitiveCharacter_order]
  decide

theorem conductor77Character_cube_order : orderOf (conductor77PrimitiveCharacter ^ 3) = 2 := by
  rw [orderOf_pow' conductor77PrimitiveCharacter (by decide : (3 : ℕ) ≠ 0),
    conductor77PrimitiveCharacter_order]
  decide

theorem conductor77Character_square_factorsThrough_seven :
    (conductor77PrimitiveCharacter ^ 2).FactorsThrough 7 := by
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap
    (χ := conductor77PrimitiveCharacter ^ 2) (by decide : 7 ∣ 77)).mpr
  intro u hu
  have h : ∀ u : (ZMod 77)ˣ, ZMod.unitsMap (by decide : 7 ∣ 77) u = 1 →
      conductor77PrimitiveCharacter (u : ZMod 77) ^ 2 = 1 := by native_decide
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  change (conductor77PrimitiveCharacter ^ 2) (u : ZMod 77) = 1
  rw [MulChar.pow_apply_coe]
  exact h u (MonoidHom.mem_ker.mp hu)

/-- The primitive character inducing psi squared has conductor exactly seven,
in accordance with the cubic conductor-seven subfield. -/
theorem conductor77Character_square_conductor : (conductor77PrimitiveCharacter ^ 2).conductor = 7 := by
  have hd : (conductor77PrimitiveCharacter ^ 2).conductor ∣ 7 :=
    DirichletCharacter.conductor_dvd_of_mem_conductorSet _
      conductor77Character_square_factorsThrough_seven
  have hp : Nat.Prime 7 := by decide
  rcases (Nat.dvd_prime hp).mp hd with h1 | h7
  · have hf := (conductor77PrimitiveCharacter ^ 2).factorsThrough_conductor
    rw [h1] at hf
    have he := (DirichletCharacter.factorsThrough_one_iff _).mp hf
    have hv := DFunLike.congr_fun he (3 : ZMod 77)
    have hu : IsUnit (3 : ZMod 77) := (ZMod.isUnit_iff_coprime 3 77).mpr (by decide)
    have hn : (conductor77PrimitiveCharacter ^ 2) (3 : ZMod 77) ≠ 1 := by
      rw [MulChar.pow_apply' conductor77PrimitiveCharacter (by decide : (2 : ℕ) ≠ 0)]
      native_decide
    exact (hn (by simpa only [MulChar.one_apply hu] using hv)).elim
  · exact h7

private theorem conductor77Character_cube_not_factorsThrough_seven :
    ¬ (conductor77PrimitiveCharacter ^ 3).FactorsThrough 7 := by
  intro h
  let u : (ZMod 77)ˣ := ⟨8, 29, by native_decide, by native_decide⟩
  have hu : u ∈ (ZMod.unitsMap (by decide : 7 ∣ 77)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    native_decide
  have hc := ((DirichletCharacter.factorsThrough_iff_ker_unitsMap
    (χ := conductor77PrimitiveCharacter ^ 3) (by decide : 7 ∣ 77)).mp h) hu
  have hv := congrArg (fun v : Conductor77CharacterValuesˣ => v.val)
    (MonoidHom.mem_ker.mp hc)
  change (conductor77PrimitiveCharacter ^ 3) (8 : ZMod 77) = 1 at hv
  rw [MulChar.pow_apply' conductor77PrimitiveCharacter (by decide : (3 : ℕ) ≠ 0)] at hv
  have hn : conductor77PrimitiveCharacter (8 : ZMod 77) ^ 3 ≠ 1 := by native_decide
  exact hn hv

private theorem conductor77Character_cube_not_factorsThrough_eleven :
    ¬ (conductor77PrimitiveCharacter ^ 3).FactorsThrough 11 := by
  intro h
  let u : (ZMod 77)ˣ := ⟨12, 45, by native_decide, by native_decide⟩
  have hu : u ∈ (ZMod.unitsMap (by decide : 11 ∣ 77)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    native_decide
  have hc := ((DirichletCharacter.factorsThrough_iff_ker_unitsMap
    (χ := conductor77PrimitiveCharacter ^ 3) (by decide : 11 ∣ 77)).mp h) hu
  have hv := congrArg (fun v : Conductor77CharacterValuesˣ => v.val)
    (MonoidHom.mem_ker.mp hc)
  change (conductor77PrimitiveCharacter ^ 3) (12 : ZMod 77) = 1 at hv
  rw [MulChar.pow_apply' conductor77PrimitiveCharacter (by decide : (3 : ℕ) ≠ 0)] at hv
  have hn : conductor77PrimitiveCharacter (12 : ZMod 77) ^ 3 ≠ 1 := by native_decide
  exact hn hv

/-- The quadratic character inducing the degree-two subfield is primitive
of conductor 77, rather than of conductor seven or eleven. -/
theorem conductor77Character_cube_conductor : (conductor77PrimitiveCharacter ^ 3).conductor = 77 := by
  let d := (conductor77PrimitiveCharacter ^ 3).conductor
  have h := (conductor77PrimitiveCharacter ^ 3).factorsThrough_conductor
  have hc : ∀ d : Fin 78, d.val ∣ 77 →
      d.val = 1 ∨ d.val = 7 ∨ d.val = 11 ∨ d.val = 77 := by native_decide
  have hd : d < 78 := Nat.lt_succ_of_le
    (Nat.le_of_dvd (by decide : 0 < 77) h.dvd)
  rcases hc ⟨d, hd⟩ h.dvd with h1 | h7 | h11 | h77
  · change d = 1 at h1
    rw [show (conductor77PrimitiveCharacter ^ 3).conductor = 1 from h1] at h
    have he := (DirichletCharacter.factorsThrough_one_iff _).mp h
    have hv := DFunLike.congr_fun he (3 : ZMod 77)
    have hu : IsUnit (3 : ZMod 77) := (ZMod.isUnit_iff_coprime 3 77).mpr (by decide)
    rw [MulChar.one_apply hu,
      MulChar.pow_apply' conductor77PrimitiveCharacter (by decide : (3 : ℕ) ≠ 0)] at hv
    have hn : conductor77PrimitiveCharacter (3 : ZMod 77) ^ 3 ≠ 1 := by native_decide
    exact (hn hv).elim
  · exact (conductor77Character_cube_not_factorsThrough_seven (h7 ▸ h)).elim
  · exact (conductor77Character_cube_not_factorsThrough_eleven (h11 ▸ h)).elim
  · exact h77

end Biunimodular.F11
