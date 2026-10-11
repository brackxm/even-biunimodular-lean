/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodTraceIntegrality77
import Mathlib.LinearAlgebra.Basis.Submodule

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- Membership in the actual period order is exactly integrality of the six
rational basis coordinates. This does not assume maximality of the order. -/
theorem periodIntegerSpan77_mem_iff_coordinates (x : conductor77PeriodField) :
    x ∈ periodIntegerSpan77 ↔
      ∀ i : Fin 6, ∃ z : ℤ, (z : ℚ) = conductor77PeriodBasis.repr x i := by
  have he : ⇑conductor77PeriodBasis = periodFieldOrbit77 :=
    funext conductor77PeriodBasis_apply
  simpa [he, periodIntegerSpan77, Set.mem_range]
    using conductor77PeriodBasis.mem_span_iff_repr_mem ℤ x

/-- A denominator class is zero in the order precisely when every numerator
coordinate is divisible by that denominator. -/
theorem periodFraction77_mem_iff_dvd (p : ℤ) (hp : p ≠ 0) (v : Fin 6 → ℤ) :
    periodFraction77 p v ∈ periodIntegerSpan77 ↔ ∀ i : Fin 6, p ∣ v i := by
  rw [periodIntegerSpan77_mem_iff_coordinates]
  simp only [periodFraction77_repr]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  constructor
  · intro h i
    obtain ⟨z, hz⟩ := h i
    refine ⟨z, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    exact ((eq_div_iff hpQ).mp hz).symm.trans (mul_comm _ _)
  · intro h i
    obtain ⟨z, hz⟩ := h i
    refine ⟨z, ?_⟩
    rw [hz, Int.cast_mul]
    field_simp

/-- Any nonzero numerator class that fails a power-trace divisibility cannot
represent an algebraic integer in a larger order. -/
theorem periodFraction77_not_integral_of_trace_obstruction (p : ℤ) (hp : p ≠ 0)
    (v : Fin 6 → ℤ) (k : ℕ)
    (hk : ¬ p ^ k ∣ Matrix.trace (periodIntegerMultiplicationMatrix77 v ^ k)) :
    ¬ IsIntegral ℤ (periodFraction77 p v) := by
  intro hx
  exact hk (periodFraction77_power_trace_divisibility p hp v hx k)

end
end Biunimodular.F11
