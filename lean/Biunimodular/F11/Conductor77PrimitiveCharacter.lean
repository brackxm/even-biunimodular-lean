/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.GroupTheory.OrderOfElement
import Lean.Elab.Tactic.Decide

set_option autoImplicit false
namespace Biunimodular.F11

/-- Exponents of the primitive order-six character modulo seven, with
generator 3. The value at the nonunit 0 is unused. -/
def conductor77Chi7Exponent (n : ℕ) : ZMod 6 :=
  match n % 7 with
  | 1 => 0
  | 2 => 2
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 3
  | _ => 0

/-- The Legendre sign modulo eleven, encoded as exponent 0 or 3 in C6. -/
def conductor77LegendreExponent (n : ℕ) : ZMod 6 :=
  if n % 11 ∈ ([1, 3, 4, 5, 9] : List ℕ) then 0 else 3

abbrev Conductor77CharacterValues := WithZero (Multiplicative (ZMod 6))

def conductor77CharacterValue (a : ZMod 77) : Conductor77CharacterValues :=
  if Nat.Coprime a.val 77 then
    ↑(Multiplicative.ofAdd
      (conductor77Chi7Exponent a.val + conductor77LegendreExponent a.val))
  else 0

/-- The product chi7*lambda11, with its sixth-root values represented exactly
by C6 with an adjoined zero. This is an actual Dirichlet character. -/
def conductor77PrimitiveCharacter : DirichletCharacter Conductor77CharacterValues 77 where
  toFun := conductor77CharacterValue
  map_one' := by native_decide
  map_mul' := by native_decide
  map_nonunit' := by
    intro a ha
    by_cases h : Nat.Coprime a.val 77
    · have hu : IsUnit (a.val : ZMod 77) := (ZMod.isUnit_iff_coprime _ _).mpr h
      exact (ha (by simpa only [ZMod.natCast_zmod_val] using hu)).elim
    · simp only [conductor77CharacterValue, h, ite_false]

theorem conductor77PrimitiveCharacter_even :
    conductor77PrimitiveCharacter (-1) = 1 := by native_decide

theorem conductor77PrimitiveCharacter_at_three :
    conductor77PrimitiveCharacter 3 =
      (↑(Multiplicative.ofAdd (1 : ZMod 6)) : Conductor77CharacterValues) := by
  native_decide

theorem conductor77PrimitiveCharacter_kernel :
    ∀ a : ZMod 77, conductor77PrimitiveCharacter a = 1 ↔
      a.val ∈ ([1, 6, 36, 62, 64, 76, 71, 41, 15, 13] : List ℕ) := by
  native_decide

theorem conductor77PrimitiveCharacter_kernel_powers :
    ∀ a : ZMod 77, conductor77PrimitiveCharacter a = 1 ↔
      ∃ j : Fin 10, a = 6 ^ j.val := by native_decide

private def conductor77UnitThree : (ZMod 77)ˣ :=
  ⟨3, 26, by native_decide, by native_decide⟩

def conductor77CharacterUnitHom : (ZMod 77)ˣ →* Multiplicative (ZMod 6) :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp conductor77PrimitiveCharacter.toUnitHom

theorem conductor77CharacterUnitHom_surjective :
    Function.Surjective conductor77CharacterUnitHom := by
  have h : ∀ k : Fin 6, conductor77CharacterUnitHom (conductor77UnitThree ^ k.val) =
      Multiplicative.ofAdd (k.val : ZMod 6) := by native_decide
  intro z
  let k : ZMod 6 := Multiplicative.toAdd z
  refine ⟨conductor77UnitThree ^ k.val, ?_⟩
  change conductor77CharacterUnitHom (conductor77UnitThree ^ k.val) = Multiplicative.ofAdd k
  simpa only [ZMod.natCast_zmod_val] using
    h ⟨k.val, k.val_lt⟩

theorem conductor77PrimitiveCharacter_order :
    orderOf conductor77PrimitiveCharacter = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  constructor
  · apply MulChar.ext
    intro a
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have h : ∀ a : ZMod 77, Nat.Coprime a.val 77 →
        conductor77PrimitiveCharacter a ^ 6 = 1 := by native_decide
    have hu : IsUnit (((a : ZMod 77).val : ℕ) : ZMod 77) := by
      simpa only [ZMod.natCast_zmod_val] using a.isUnit
    exact h a ((ZMod.isUnit_iff_coprime _ _).mp hu)
  · intro m hmlt hmpos heq
    have hv := DFunLike.congr_fun heq (conductor77UnitThree : ZMod 77)
    have hu : IsUnit (conductor77UnitThree : ZMod 77) := conductor77UnitThree.isUnit
    rw [MulChar.pow_apply' conductor77PrimitiveCharacter (Nat.ne_of_gt hmpos),
      MulChar.one_apply hu] at hv
    have h : ∀ m : Fin 6, 0 < m.val →
        conductor77PrimitiveCharacter (3 : ZMod 77) ^ m.val ≠ 1 := by native_decide
    exact h ⟨m, hmlt⟩ hmpos hv

private def conductor77UnitEight : (ZMod 77)ˣ :=
  ⟨8, 29, by native_decide, by native_decide⟩

private def conductor77UnitTwelve : (ZMod 77)ˣ :=
  ⟨12, 45, by native_decide, by native_decide⟩

private theorem conductor77_not_factorsThrough_seven :
    ¬ conductor77PrimitiveCharacter.FactorsThrough 7 := by
  intro h
  have hk : conductor77UnitEight ∈
      (ZMod.unitsMap (by decide : 7 ∣ 77)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    native_decide
  have hc := ((DirichletCharacter.factorsThrough_iff_ker_unitsMap
    (χ := conductor77PrimitiveCharacter) (by decide : 7 ∣ 77)).mp h) hk
  have hv := congrArg (fun u : Conductor77CharacterValuesˣ => u.val)
    (MonoidHom.mem_ker.mp hc)
  change conductor77CharacterValue (8 : ZMod 77) = 1 at hv
  have hn : conductor77CharacterValue (8 : ZMod 77) ≠ 1 := by native_decide
  exact hn hv

private theorem conductor77_not_factorsThrough_eleven :
    ¬ conductor77PrimitiveCharacter.FactorsThrough 11 := by
  intro h
  have hk : conductor77UnitTwelve ∈
      (ZMod.unitsMap (by decide : 11 ∣ 77)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    native_decide
  have hc := ((DirichletCharacter.factorsThrough_iff_ker_unitsMap
    (χ := conductor77PrimitiveCharacter) (by decide : 11 ∣ 77)).mp h) hk
  have hv := congrArg (fun u : Conductor77CharacterValuesˣ => u.val)
    (MonoidHom.mem_ker.mp hc)
  change conductor77CharacterValue (12 : ZMod 77) = 1 at hv
  have hn : conductor77CharacterValue (12 : ZMod 77) ≠ 1 := by native_decide
  exact hn hv

/-- No proper divisor of 77 is a level for this character. -/
theorem conductor77PrimitiveCharacter_factorsThrough_iff (d : ℕ) :
    conductor77PrimitiveCharacter.FactorsThrough d ↔ d = 77 := by
  constructor
  · intro h
    have hchoices : ∀ d : Fin 78, d.val ∣ 77 →
        d.val = 1 ∨ d.val = 7 ∨ d.val = 11 ∨ d.val = 77 := by native_decide
    have hd : d < 78 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide : 0 < 77) h.dvd)
    rcases hchoices ⟨d, hd⟩ h.dvd with h1 | h7 | h11 | h77
    · change d = 1 at h1
      subst d
      have he := (DirichletCharacter.factorsThrough_one_iff _).mp h
      have hv := DFunLike.congr_fun he (3 : ZMod 77)
      have hu : IsUnit (3 : ZMod 77) := (ZMod.isUnit_iff_coprime 3 77).mpr (by decide)
      have hn : conductor77PrimitiveCharacter (3 : ZMod 77) ≠ 1 := by native_decide
      exact (hn (by simpa only [MulChar.one_apply hu] using hv)).elim
    · exact (conductor77_not_factorsThrough_seven (h7 ▸ h)).elim
    · exact (conductor77_not_factorsThrough_eleven (h11 ▸ h)).elim
    · exact h77
  · rintro rfl
    exact DirichletCharacter.FactorsThrough.same_level _

/-- The displayed even character is primitive with conductor exactly 77. -/
theorem conductor77PrimitiveCharacter_conductor :
    conductor77PrimitiveCharacter.conductor = 77 :=
  (conductor77PrimitiveCharacter_factorsThrough_iff _).mp
    conductor77PrimitiveCharacter.factorsThrough_conductor

theorem conductor77PrimitiveCharacter_isPrimitive :
    conductor77PrimitiveCharacter.IsPrimitive := conductor77PrimitiveCharacter_conductor

end Biunimodular.F11
