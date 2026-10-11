/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodBasisDiscriminant77
import Biunimodular.F11.ASectorPeriodIntegrality77

set_option autoImplicit false

namespace Biunimodular.F11
noncomputable section

def periodIntegerSpan77 : Submodule ℤ conductor77PeriodField :=
  Submodule.span ℤ (Set.range periodFieldOrbit77)

theorem periodFieldOrbit77_mem_integerSpan (i : Fin 6) :
    periodFieldOrbit77 i ∈ periodIntegerSpan77 := Submodule.subset_span ⟨i, rfl⟩

theorem periodFieldOrbit77_mul_int (i j : Fin 6) :
    periodFieldOrbit77 i * periodFieldOrbit77 j =
      ∑ k : Fin 6, periodOrderProductCoefficients77 i j k • periodFieldOrbit77 k := by
  simpa [Algebra.smul_def] using periodFieldOrbit77_mul i j

theorem periodIntegerSpan77_one : (1 : conductor77PeriodField) ∈ periodIntegerSpan77 := by
  have hsum : periodFieldOrbit77 0 + periodFieldOrbit77 1 + periodFieldOrbit77 2 +
      periodFieldOrbit77 3 + periodFieldOrbit77 4 + periodFieldOrbit77 5 = 1 := by
    apply Subtype.ext
    exact periodOrbit77_sum
  rw [← hsum]
  repeat' apply Submodule.add_mem
  all_goals exact periodFieldOrbit77_mem_integerSpan _

theorem periodIntegerSpan77_mul {x y : conductor77PeriodField}
    (hx : x ∈ periodIntegerSpan77) (hy : y ∈ periodIntegerSpan77) :
    x * y ∈ periodIntegerSpan77 := by
  refine Submodule.span_induction₂ (p := fun x y _ _ => x * y ∈ periodIntegerSpan77)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    rw [periodFieldOrbit77_mul_int]
    apply Submodule.sum_mem
    intro k _
    exact periodIntegerSpan77.smul_mem _ (periodFieldOrbit77_mem_integerSpan k)
  · intro y _
    simpa only [zero_mul] using periodIntegerSpan77.zero_mem
  · intro x _
    simpa only [mul_zero] using periodIntegerSpan77.zero_mem
  · intro x y z _ _ _ hx hy
    simpa only [add_mul] using periodIntegerSpan77.add_mem hx hy
  · intro x y z _ _ _ hx hy
    simpa only [mul_add] using periodIntegerSpan77.add_mem hx hy
  · intro r x y _ _ h
    simpa only [smul_mul_assoc] using periodIntegerSpan77.smul_mem r h
  · intro r x y _ _ h
    simpa only [mul_smul_comm] using periodIntegerSpan77.smul_mem r h

/-- The integer span is an actual subalgebra, rather than just multiplication data. -/
def conductor77PeriodIntegerOrder : Subalgebra ℤ conductor77PeriodField :=
  periodIntegerSpan77.toSubalgebra periodIntegerSpan77_one
    (fun _ _ hx hy => periodIntegerSpan77_mul hx hy)

theorem periodFieldOrbit77_linearIndependent_int :
    LinearIndependent ℤ periodFieldOrbit77 := by
  have h := conductor77PeriodBasis.linearIndependent.restrict_scalars' ℤ
  have he : ⇑conductor77PeriodBasis = periodFieldOrbit77 :=
    funext conductor77PeriodBasis_apply
  rw [he] at h
  exact h

/-- The actual integer period order has a basis of six periods. -/
def conductor77PeriodIntegerOrderBasis :
    Module.Basis (Fin 6) ℤ conductor77PeriodIntegerOrder :=
  Module.Basis.span periodFieldOrbit77_linearIndependent_int

theorem periodFieldOrbit77_isIntegral_int (i : Fin 6) :
    IsIntegral ℤ (periodFieldOrbit77 i) := by
  apply (isIntegral_algebraMap_iff (R := ℤ) (A := conductor77PeriodField)
    (B := Conductor77Cyclotomic)).mp
  exact periodOrbit77_isIntegral_int i

/-- Every member of the order is an algebraic integer. -/
theorem periodIntegerSpan77_isIntegral {x : conductor77PeriodField}
    (hx : x ∈ periodIntegerSpan77) : IsIntegral ℤ x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact periodFieldOrbit77_isIntegral_int i
  | zero => exact isIntegral_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul r x _ hx =>
    rw [Algebra.smul_def]
    exact (isIntegral_algebraMap).mul hx

end
end Biunimodular.F11
