/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodOrderMultiplication77
import Biunimodular.F11.ASectorPeriodSubfields77
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

set_option autoImplicit false

namespace Biunimodular.F11
open scoped IntermediateField
noncomputable section

/-- The rational span of the actual six Gaussian periods. -/
def periodOrbitSpan77 : Submodule ℚ Conductor77Cyclotomic :=
  Submodule.span ℚ (Set.range periodOrbit77)

theorem periodOrbit77_mem_span (i : Fin 6) : periodOrbit77 i ∈ periodOrbitSpan77 :=
  Submodule.subset_span ⟨i, rfl⟩

theorem periodOrbitSpan77_one : (1 : Conductor77Cyclotomic) ∈ periodOrbitSpan77 := by
  rw [← periodOrbit77_sum]
  repeat' apply Submodule.add_mem
  all_goals exact periodOrbit77_mem_span _

theorem periodOrbitSpan77_mul {x y : Conductor77Cyclotomic}
    (hx : x ∈ periodOrbitSpan77) (hy : y ∈ periodOrbitSpan77) :
    x * y ∈ periodOrbitSpan77 := by
  refine Submodule.span_induction₂ (p := fun x y _ _ => x * y ∈ periodOrbitSpan77)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    rw [periodOrbit77_mul]
    apply Submodule.sum_mem
    intro k _
    have h := periodOrbitSpan77.smul_mem
      (periodOrderProductCoefficients77 i j k : ℚ) (periodOrbit77_mem_span k)
    simpa only [Algebra.smul_def, map_intCast] using h
  · intro y _
    simpa only [zero_mul] using periodOrbitSpan77.zero_mem
  · intro x _
    simpa only [mul_zero] using periodOrbitSpan77.zero_mem
  · intro x y z _ _ _ hx hy
    simpa only [add_mul] using periodOrbitSpan77.add_mem hx hy
  · intro x y z _ _ _ hx hy
    simpa only [mul_add] using periodOrbitSpan77.add_mem hx hy
  · intro r x y _ _ h
    simpa only [smul_mul_assoc] using periodOrbitSpan77.smul_mem r h
  · intro r x y _ _ h
    simpa only [mul_smul_comm] using periodOrbitSpan77.smul_mem r h

def periodOrbitSpanSubalgebra77 : Subalgebra ℚ Conductor77Cyclotomic where
  carrier := periodOrbitSpan77
  mul_mem' := periodOrbitSpan77_mul
  one_mem' := periodOrbitSpan77_one
  add_mem' := periodOrbitSpan77.add_mem
  zero_mem' := periodOrbitSpan77.zero_mem
  algebraMap_mem' r := by
    change algebraMap ℚ Conductor77Cyclotomic r ∈ periodOrbitSpan77
    simpa only [Algebra.smul_def, mul_one] using
      periodOrbitSpan77.smul_mem r periodOrbitSpan77_one

/-- Multiplicative closure and the period generator identify the entire sextic field. -/
theorem periodOrbitSpan77_eq_field :
    periodOrbitSpan77 = conductor77PeriodField.toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact periodOrbit77_mem_periodField i
  · have hle : conductor77PeriodField.toSubalgebra ≤ periodOrbitSpanSubalgebra77 := by
      change (IntermediateField.adjoin ℚ {periodEta77}).toSubalgebra ≤ _
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsIntegral.of_finite ℚ periodEta77).isAlgebraic]
      apply Algebra.adjoin_le
      intro x hx
      have he : periodOrbit77 0 = periodEta77 := by
        simp [periodOrbit77, conductor77PeriodOrbitValue,
          conductor77PeriodOrbitPolynomials, periodEta77, conductor77PeriodPolynomial]
      change x ∈ periodOrbitSpan77
      rw [Set.mem_singleton_iff.mp hx, ← he]
      exact periodOrbit77_mem_span 0
    exact hle

def periodFieldOrbit77 (i : Fin 6) : conductor77PeriodField :=
  ⟨periodOrbit77 i, periodOrbit77_mem_periodField i⟩

theorem periodFieldOrbit77_span :
    Submodule.span ℚ (Set.range periodFieldOrbit77) = ⊤ := by
  apply Submodule.map_injective_of_injective conductor77PeriodField.toSubmodule.injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top]
  have himage : conductor77PeriodField.toSubmodule.subtype '' Set.range periodFieldOrbit77 =
      Set.range periodOrbit77 := by
    rw [← Set.range_comp]
    rfl
  rw [himage]
  exact periodOrbitSpan77_eq_field

/-- A basis consisting of the actual periods, with the coset indexing. -/
def conductor77PeriodBasis : Module.Basis (Fin 6) ℚ conductor77PeriodField :=
  basisOfTopLeSpanOfCardEqFinrank periodFieldOrbit77
    (by rw [periodFieldOrbit77_span])
    (by simpa using conductor77PeriodField_finrank.symm)

@[simp] theorem conductor77PeriodBasis_apply (i : Fin 6) :
    conductor77PeriodBasis i = periodFieldOrbit77 i := by
  simp [conductor77PeriodBasis]

end
end Biunimodular.F11
