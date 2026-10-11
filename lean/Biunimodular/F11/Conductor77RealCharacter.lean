/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Conductor77PrimitiveCharacter
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false
namespace Biunimodular.F11

/-- The sign subgroup in the actual conductor-77 unit group. -/
def conductor77Signs : Subgroup (ZMod 77)ˣ where
  carrier := {u | u = 1 ∨ u = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl <;> simp

abbrev Conductor77RealUnits := (ZMod 77)ˣ ⧸ conductor77Signs

theorem conductor77Signs_le_character_kernel :
    conductor77Signs ≤ conductor77CharacterUnitHom.ker := by
  intro u hu
  rcases hu with rfl | rfl
  · exact MonoidHom.mem_ker.mpr (map_one _)
  · exact MonoidHom.mem_ker.mpr (by native_decide)

/-- The even character descends to the actual quotient by signs. -/
def conductor77RealCharacter : Conductor77RealUnits →* Multiplicative (ZMod 6) :=
  QuotientGroup.lift conductor77Signs conductor77CharacterUnitHom
    conductor77Signs_le_character_kernel

theorem conductor77RealCharacter_surjective : Function.Surjective conductor77RealCharacter :=
  QuotientGroup.lift_surjective_of_surjective conductor77Signs
    conductor77CharacterUnitHom conductor77CharacterUnitHom_surjective
    conductor77Signs_le_character_kernel

def conductor77UnitSix : (ZMod 77)ˣ := ⟨6, 13, by native_decide, by native_decide⟩

theorem conductor77UnitSix_fifth : conductor77UnitSix ^ 5 = -1 := by
  apply Units.ext
  native_decide

def conductor77RealSix : Conductor77RealUnits := QuotientGroup.mk' conductor77Signs conductor77UnitSix

theorem conductor77RealSix_fifth : conductor77RealSix ^ 5 = 1 := by
  rw [conductor77RealSix, ← map_pow, conductor77UnitSix_fifth]
  exact (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)

theorem conductor77RealSix_order : orderOf conductor77RealSix = 5 := by
  apply (orderOf_eq_iff (by decide : 0 < 5)).mpr
  refine ⟨conductor77RealSix_fifth, ?_⟩
  intro m hmlt hmpos hm
  have hmem : conductor77UnitSix ^ m ∈ conductor77Signs := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' conductor77Signs (conductor77UnitSix ^ m) = 1
    rw [map_pow]
    exact hm
  have hn : ∀ k : Fin 5, 0 < k.val →
      conductor77UnitSix ^ k.val ≠ 1 ∧ conductor77UnitSix ^ k.val ≠ -1 := by
    native_decide
  exact hmem.elim (hn ⟨m, hmlt⟩ hmpos).1 (hn ⟨m, hmlt⟩ hmpos).2

theorem conductor77RealCharacter_at_six : conductor77RealCharacter conductor77RealSix = 1 := by
  change conductor77CharacterUnitHom conductor77UnitSix = 1
  native_decide

/-- The kernel after quotienting by signs consists precisely of the five
classes represented by powers of 6. -/
theorem conductor77RealCharacter_kernel_powers (u : Conductor77RealUnits) :
    conductor77RealCharacter u = 1 ↔ ∃ j : Fin 5, u = conductor77RealSix ^ j.val := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective conductor77Signs u
  have hk : ∀ v : (ZMod 77)ˣ, conductor77CharacterUnitHom v = 1 ↔
      ∃ j : Fin 10, v = conductor77UnitSix ^ j.val := by native_decide
  constructor
  · intro hv
    obtain ⟨j, rfl⟩ := (hk v).mp hv
    refine ⟨⟨j.val % 5, Nat.mod_lt _ (by decide)⟩, ?_⟩
    change conductor77RealSix ^ j.val = conductor77RealSix ^ (j.val % 5)
    rw [← conductor77RealSix_order]
    exact (pow_mod_orderOf _ _).symm
  · rintro ⟨j, hj⟩
    rw [hj, map_pow]
    rw [conductor77RealCharacter_at_six, one_pow]

theorem conductor77RealCharacter_kernel :
    conductor77RealCharacter.ker = Subgroup.zpowers conductor77RealSix := by
  ext u
  constructor
  · intro hu
    obtain ⟨j, rfl⟩ := (conductor77RealCharacter_kernel_powers u).mp
      (MonoidHom.mem_ker.mp hu)
    exact Subgroup.npow_mem_zpowers _ _
  · intro hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    apply MonoidHom.mem_ker.mpr
    rw [map_zpow, conductor77RealCharacter_at_six, one_zpow]

theorem conductor77RealCharacter_kernel_card : Nat.card conductor77RealCharacter.ker = 5 := by
  rw [conductor77RealCharacter_kernel, Nat.card_zpowers, conductor77RealSix_order]

/-- The kernel in the real unit quotient is isomorphic to C5. Together
with surjectivity to C6 this proves the character's exact sequence. -/
noncomputable def conductor77RealCharacter_kernel_equiv_C5 :
    Multiplicative (ZMod 5) ≃* conductor77RealCharacter.ker := by
  letI : IsCyclic conductor77RealCharacter.ker := by
    rw [conductor77RealCharacter_kernel]
    infer_instance
  rw [← conductor77RealCharacter_kernel_card]
  exact zmodCyclicMulEquiv (inferInstance : IsCyclic conductor77RealCharacter.ker)

end Biunimodular.F11
