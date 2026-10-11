/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Conductor77RealCharacter

set_option autoImplicit false
namespace Biunimodular.F11

def conductor11Signs : Subgroup (ZMod 11)ˣ where
  carrier := {u | u = 1 ∨ u = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl <;> simp

abbrev Conductor11RealUnits := (ZMod 11)ˣ ⧸ conductor11Signs

def conductor77Reduction11 : (ZMod 77)ˣ →* (ZMod 11)ˣ :=
  ZMod.unitsMap (by decide : 11 ∣ 77)

def conductor77SignedReduction11 : (ZMod 77)ˣ →* Conductor11RealUnits :=
  (QuotientGroup.mk' conductor11Signs).comp conductor77Reduction11

theorem conductor77Signs_le_reduction_kernel :
    conductor77Signs ≤ conductor77SignedReduction11.ker := by
  intro u hu
  rcases hu with rfl | rfl
  · exact MonoidHom.mem_ker.mpr (map_one _)
  · apply MonoidHom.mem_ker.mpr
    change QuotientGroup.mk' conductor11Signs (conductor77Reduction11 (-1)) = 1
    have hn : conductor77Reduction11 (-1) = -1 := by
      apply Units.ext
      native_decide
    rw [hn]
    exact (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)

def conductor77RealReduction11 : Conductor77RealUnits →* Conductor11RealUnits :=
  QuotientGroup.lift conductor77Signs conductor77SignedReduction11
    conductor77Signs_le_reduction_kernel

def conductor11UnitSix : (ZMod 11)ˣ := ⟨6, 2, by native_decide, by native_decide⟩

theorem conductor77Reduction11_six : conductor77Reduction11 conductor77UnitSix = conductor11UnitSix := by
  apply Units.ext
  native_decide

theorem conductor77RealReduction11_six :
    conductor77RealReduction11 conductor77RealSix =
      QuotientGroup.mk' conductor11Signs conductor11UnitSix := by
  change QuotientGroup.mk' conductor11Signs (conductor77Reduction11 conductor77UnitSix) = _
  rw [conductor77Reduction11_six]

/-- Actual reduction modulo eleven restricted to the character kernel. -/
def conductor77KernelReduction11 : conductor77RealCharacter.ker →* Conductor11RealUnits :=
  conductor77RealReduction11.comp conductor77RealCharacter.ker.subtype

theorem conductor77KernelReduction11_injective : Function.Injective conductor77KernelReduction11 := by
  intro u v he
  obtain ⟨j, hj⟩ := (conductor77RealCharacter_kernel_powers u.val).mp
    (MonoidHom.mem_ker.mp u.property)
  obtain ⟨k, hk⟩ := (conductor77RealCharacter_kernel_powers v.val).mp
    (MonoidHom.mem_ker.mp v.property)
  change conductor77RealReduction11 u.val = conductor77RealReduction11 v.val at he
  rw [hj, hk, map_pow, map_pow, conductor77RealReduction11_six, ← map_pow, ← map_pow] at he
  obtain ⟨s, hs, he⟩ := (QuotientGroup.mk'_eq_mk' conductor11Signs).mp he
  have hn : ∀ j k : Fin 5,
      (conductor11UnitSix ^ j.val = conductor11UnitSix ^ k.val ∨
        conductor11UnitSix ^ j.val * (-1) = conductor11UnitSix ^ k.val) → j = k := by
    native_decide
  have hjk : j = k := by
    rcases hs with rfl | rfl
    · exact hn j k (Or.inl (by simpa only [mul_one] using he))
    · exact hn j k (Or.inr he)
  apply Subtype.ext
  rw [hj, hk, hjk]

theorem conductor77KernelReduction11_surjective : Function.Surjective conductor77KernelReduction11 := by
  intro u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective conductor11Signs u
  have hv : ∀ v : (ZMod 11)ˣ, ∃ j : Fin 5,
      v = conductor11UnitSix ^ j.val ∨ v = conductor11UnitSix ^ j.val * (-1) := by
    native_decide
  obtain ⟨j, hj⟩ := hv v
  have hc : conductor77RealSix ^ j.val ∈ conductor77RealCharacter.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_pow, conductor77RealCharacter_at_six, one_pow]
  refine ⟨⟨conductor77RealSix ^ j.val, hc⟩, ?_⟩
  change conductor77RealReduction11 (conductor77RealSix ^ j.val) =
    QuotientGroup.mk' conductor11Signs v
  rw [map_pow, conductor77RealReduction11_six, ← map_pow]
  rcases hj with rfl | rfl
  · rfl
  · exact (QuotientGroup.mk'_eq_mk' conductor11Signs).mpr ⟨-1, Or.inr rfl, rfl⟩

/-- Reduction modulo eleven canonically identifies the relative C5 kernel
with the unit group modulo signs of the length-eleven dilation action. -/
noncomputable def conductor77KernelReduction11_equiv :
    conductor77RealCharacter.ker ≃* Conductor11RealUnits :=
  MulEquiv.ofBijective conductor77KernelReduction11
    ⟨conductor77KernelReduction11_injective, conductor77KernelReduction11_surjective⟩

noncomputable def conductor11RealUnits_equiv_C5 :
    Multiplicative (ZMod 5) ≃* Conductor11RealUnits :=
  conductor77RealCharacter_kernel_equiv_C5.trans conductor77KernelReduction11_equiv

end Biunimodular.F11
