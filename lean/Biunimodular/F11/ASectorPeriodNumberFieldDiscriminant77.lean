/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodOrderSaturation77
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

instance conductor77PeriodField_numberField : NumberField conductor77PeriodField where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- The integral-basis bridge to the actual number-field discriminant.
The two prime saturation certificates are explicit outstanding hypotheses. -/
theorem conductor77PeriodField_discr_of_saturation
    (h7 : PeriodOrderSaturated77 7) (h11 : PeriodOrderSaturated77 11) :
    NumberField.discr conductor77PeriodField = (7^5 * 11^3 : ℤ) := by
  classical
  let b := NumberField.integralBasis conductor77PeriodField
  have h : ∀ i j, IsIntegral ℤ (conductor77PeriodBasis.toMatrix b i j) := by
    intro i j
    have hj : IsIntegral ℤ (b j) := by
      rw [NumberField.integralBasis_apply]
      exact NumberField.RingOfIntegers.isIntegral_coe _
    have hm := (periodIntegerSpan77_integral_iff_of_saturation h7 h11 (b j)).mp hj
    obtain ⟨z, hz⟩ := (periodIntegerSpan77_mem_iff_coordinates (b j)).mp hm i
    rw [Module.Basis.toMatrix_apply, ← hz]
    exact isIntegral_intCast z
  have h' : ∀ i j, IsIntegral ℤ (b.toMatrix conductor77PeriodBasis i j) := by
    intro i j
    have hj : IsIntegral ℤ (conductor77PeriodBasis j) := by
      rw [conductor77PeriodBasis_apply]
      exact periodFieldOrbit77_isIntegral_int j
    have hr : conductor77PeriodBasis j ∈
        (algebraMap (NumberField.RingOfIntegers conductor77PeriodField)
          conductor77PeriodField).range := ⟨⟨conductor77PeriodBasis j, hj⟩, rfl⟩
    have hm := (NumberField.mem_span_integralBasis conductor77PeriodField).mpr hr
    obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ (conductor77PeriodBasis j)).mp hm i
    rw [Module.Basis.toMatrix_apply, ← hz]
    exact isIntegral_algebraMap
  have hd := Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral
    conductor77PeriodField h h'
  apply Int.cast_injective (α := ℚ)
  rw [NumberField.coe_discr, ← hd, conductor77PeriodBasis_discr]
  norm_num

end
end Biunimodular.F11
