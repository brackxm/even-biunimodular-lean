/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodTraceDenominator77

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

theorem periodIntegerCombination77_mem (v : Fin 6 → ℤ) :
    periodIntegerCombination77 v ∈ periodIntegerSpan77 := by
  rw [periodIntegerSpan77_mem_iff_coordinates]
  intro i
  refine ⟨v i, ?_⟩
  rw [periodIntegerCombination77, conductor77PeriodBasis.repr_sum_self]

/-- Subtracting an element of the period order reduces a denominator class
to the canonical integer residues used by the finite certificate. -/
theorem periodFraction77_emod_decomposition (p : ℤ) (hp : p ≠ 0)
    (v : Fin 6 → ℤ) :
    periodFraction77 p v = periodFraction77 p (fun i => v i % p) +
      periodIntegerCombination77 (fun i => v i / p) := by
  apply conductor77PeriodBasis.repr.injective
  ext i
  simp only [map_add, Finsupp.add_apply, periodFraction77_repr,
    periodIntegerCombination77, conductor77PeriodBasis.repr_sum_self]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have h : ((v i % p : ℤ) : ℚ) + (p : ℚ) * ((v i / p : ℤ) : ℚ) = (v i : ℚ) := by
    exact_mod_cast Int.emod_add_mul_ediv (v i) p
  apply (div_eq_iff hpQ).mpr
  rw [add_mul, div_mul_cancel₀ _ hpQ]
  simpa [mul_comm] using h.symm

theorem periodFraction77_emod_isIntegral_iff (p : ℤ) (hp : p ≠ 0)
    (v : Fin 6 → ℤ) :
    IsIntegral ℤ (periodFraction77 p (fun i => v i % p)) ↔
      IsIntegral ℤ (periodFraction77 p v) := by
  have hi := periodIntegerSpan77_isIntegral
    (periodIntegerCombination77_mem (fun i => v i / p))
  rw [periodFraction77_emod_decomposition p hp v]
  constructor
  · exact fun hx => hx.add hi
  · intro hx
    simpa using hx.sub hi

/-- Every element whose multiple by `p` is in the order has an actual period
fraction representation, so the finite numerator test applies to all such elements. -/
theorem periodFraction77_exists_of_smul_mem (p : ℤ) (hp : p ≠ 0)
    (x : conductor77PeriodField) (hx : (p : ℚ) • x ∈ periodIntegerSpan77) :
    ∃ v : Fin 6 → ℤ, x = periodFraction77 p v := by
  classical
  rw [periodIntegerSpan77_mem_iff_coordinates] at hx
  choose v hv using hx
  refine ⟨v, conductor77PeriodBasis.repr.injective ?_⟩
  ext i
  rw [periodFraction77_repr]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  apply (eq_div_iff hpQ).mpr
  have hi := hv i
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hi
  exact (mul_comm _ _).trans hi.symm

end
end Biunimodular.F11
