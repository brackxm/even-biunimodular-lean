/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodNumberFieldDiscriminant77
import Biunimodular.F11.ASectorPeriodResidueSeven77
import Biunimodular.F11.ASectorPeriodResidueEleven77

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

theorem periodOrderSaturated77_of_finite_trace_test (p : ℕ) (hp : 0 < p)
    (ht : ∀ a b c d e f : Fin p,
      PeriodResidueTraceTest77 (p : ℤ) (periodResidueVector77 a b c d e f)) :
    PeriodOrderSaturated77 (p : ℤ) := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  apply periodOrderSaturated77_of_residue_test (p : ℤ) hpZ
  intro v hv hx i
  let w : Fin 6 → Fin p := fun j => ⟨(v j).toNat, by
    have h : ((v j).toNat : ℤ) < p := by
      simpa only [Int.toNat_of_nonneg (hv j).1] using (hv j).2
    exact_mod_cast h⟩
  have hw : periodResidueVector77 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) = v := by
    funext j
    fin_cases j <;> simp [periodResidueVector77, w, Int.toNat_of_nonneg (hv _).1]
  have ht' := ht (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
  rw [hw] at ht'
  by_contra hi
  obtain ⟨k, hk⟩ := ht' ⟨i, hi⟩
    (fun j => periodFraction77_trace_divisibility (p : ℤ) (ne_of_gt hpZ) v hx j)
  exact hk (periodFraction77_power_trace_divisibility (p : ℤ)
    (ne_of_gt hpZ) v hx (k.val + 1))

theorem periodOrderSaturated77_seven : PeriodOrderSaturated77 7 :=
  periodOrderSaturated77_of_finite_trace_test 7 (by decide) periodResidueSeven77_trace_test

theorem periodOrderSaturated77_eleven : PeriodOrderSaturated77 11 :=
  periodOrderSaturated77_of_finite_trace_test 11 (by decide) periodResidueEleven77_trace_test

/-- The integer period order is the full set of algebraic integers. -/
theorem periodIntegerSpan77_integral_iff (x : conductor77PeriodField) :
    IsIntegral ℤ x ↔ x ∈ periodIntegerSpan77 :=
  periodIntegerSpan77_integral_iff_of_saturation
    periodOrderSaturated77_seven periodOrderSaturated77_eleven x

/-- The actual sextic number field has the conductor discriminant. -/
theorem conductor77PeriodField_discr :
    NumberField.discr conductor77PeriodField = (7^5 * 11^3 : ℤ) :=
  conductor77PeriodField_discr_of_saturation
    periodOrderSaturated77_seven periodOrderSaturated77_eleven

end
end Biunimodular.F11
