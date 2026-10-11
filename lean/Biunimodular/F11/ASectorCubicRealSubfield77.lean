/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodSubfieldDegrees77

set_option autoImplicit false
namespace Biunimodular.F11
open scoped IntermediateField
noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

/-- The real conductor-seven cyclotomic coordinate in the conductor-77 field. -/
def conductor7RealGenerator77 : Conductor77Cyclotomic := zeta77 ^ 11 + zeta77 ^ 66

def conductor7RealSubfield77 : IntermediateField ℚ Conductor77Cyclotomic :=
  ℚ⟮conductor7RealGenerator77⟯

theorem zeta77_pow11_isPrimitiveRoot7 : IsPrimitiveRoot (zeta77 ^ 11) 7 := by
  exact IsPrimitiveRoot.pow (by decide : 0 < 77)
    (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic) (by decide : 77 = 11 * 7)

private theorem periodCubicGenerator77_pair :
    periodCubicGenerator77 = -(zeta77 ^ 22 + zeta77 ^ 55) := by
  simpa [periodCubicGenerator77] using periodOrbit77_pair 0

theorem periodCubicGenerator77_eq_two_sub_sq :
    periodCubicGenerator77 = 2 - conductor7RealGenerator77 ^ 2 := by
  have hζ : zeta77 ^ 77 = 1 :=
    (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic).pow_eq_one
  have h132 : zeta77 ^ 132 = zeta77 ^ 55 := by
    simpa using pow_eq_pow_mod 132 hζ
  rw [periodCubicGenerator77_pair, conductor7RealGenerator77]
  ring_nf
  rw [h132, hζ]
  ring

theorem periodCubicGenerator77_mul_realGenerator :
    periodCubicGenerator77 * conductor7RealGenerator77 = 1 - periodCubicGenerator77 := by
  have hζ : zeta77 ^ 77 = 1 :=
    (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic).pow_eq_one
  have h88 : zeta77 ^ 88 = zeta77 ^ 11 := by
    simpa using pow_eq_pow_mod 88 hζ
  have h121 : zeta77 ^ 121 = zeta77 ^ 44 := by
    simpa using pow_eq_pow_mod 121 hζ
  have hsum := zeta77_pow11_isPrimitiveRoot7.geom_sum_eq_zero (by decide : 1 < 7)
  norm_num [Finset.sum_range_succ, ← pow_mul] at hsum
  rw [periodCubicGenerator77_pair, conductor7RealGenerator77]
  ring_nf
  rw [h88, h121]
  linear_combination -hsum

theorem periodCubicGenerator77_ne_zero : periodCubicGenerator77 ≠ 0 := by
  intro h
  have hr := periodCubicGenerator77_relation
  rw [h] at hr
  norm_num at hr

theorem conductor77CubicSubfield_eq_real7 :
    conductor77CubicSubfield = conductor7RealSubfield77 := by
  apply le_antisymm
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    rw [periodCubicGenerator77_eq_two_sub_sq]
    have ht : conductor7RealGenerator77 ∈ conductor7RealSubfield77 :=
      IntermediateField.mem_adjoin_simple_self ℚ conductor7RealGenerator77
    apply conductor7RealSubfield77.sub_mem (conductor7RealSubfield77.natCast_mem 2)
    simpa only [pow_two] using conductor7RealSubfield77.mul_mem ht ht
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    have hb : periodCubicGenerator77 ∈ conductor77CubicSubfield :=
      IntermediateField.mem_adjoin_simple_self ℚ periodCubicGenerator77
    have he : conductor7RealGenerator77 =
        (1 - periodCubicGenerator77) / periodCubicGenerator77 := by
      apply (eq_div_iff periodCubicGenerator77_ne_zero).mpr
      simpa only [mul_comm] using periodCubicGenerator77_mul_realGenerator
    rw [he]
    exact conductor77CubicSubfield.div_mem
      (conductor77CubicSubfield.sub_mem conductor77CubicSubfield.one_mem hb) hb

theorem conductor7RealSubfield77_finrank : Module.finrank ℚ conductor7RealSubfield77 = 3 := by
  rw [← conductor77CubicSubfield_eq_real7]
  exact conductor77CubicSubfield_finrank

end
end Biunimodular.F11
