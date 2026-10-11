/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodFractionReduction77

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- Saturation is restricted to algebraic integers, as required for maximality. -/
def PeriodOrderSaturated77 (p : ℤ) : Prop :=
  ∀ x : conductor77PeriodField, IsIntegral ℤ x →
    p • x ∈ periodIntegerSpan77 → x ∈ periodIntegerSpan77

/-- A finite test on canonical residue vectors suffices for saturation of
the actual period order. The test itself remains a separate certificate. -/
theorem periodOrderSaturated77_of_residue_test (p : ℤ) (hp : 0 < p)
    (htest : ∀ v : Fin 6 → ℤ, (∀ i, 0 ≤ v i ∧ v i < p) →
      IsIntegral ℤ (periodFraction77 p v) → ∀ i, v i = 0) :
    PeriodOrderSaturated77 p := by
  intro x hx hmultiple
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hm : (p : ℚ) • x ∈ periodIntegerSpan77 := by
    simpa only [Int.cast_smul_eq_zsmul] using hmultiple
  obtain ⟨v, rfl⟩ := periodFraction77_exists_of_smul_mem p hp0 x hm
  have hmod := (periodFraction77_emod_isIntegral_iff p hp0 v).mpr hx
  have hzero := htest (fun i => v i % p)
    (fun i => ⟨Int.emod_nonneg _ hp0, Int.emod_lt_of_pos _ hp⟩) hmod
  apply (periodFraction77_mem_iff_dvd p hp0 v).mpr
  intro i
  exact Int.dvd_of_emod_eq_zero (hzero i)

theorem periodOrderSaturated77_pow (p : ℤ) (h : PeriodOrderSaturated77 p) (n : ℕ) :
    PeriodOrderSaturated77 (p ^ n) := by
  induction n with
  | zero =>
    intro x hx hm
    simpa using hm
  | succ n ih =>
    intro x hx hm
    apply ih x hx
    apply h (p ^ n • x) (hx.smul (p ^ n))
    simpa only [smul_smul, pow_succ', mul_comm] using hm

/-- The checked trace denominator bound reduces maximality to the two prime
saturation certificates at seven and eleven. -/
theorem periodIntegerSpan77_integral_iff_of_saturation
    (h7 : PeriodOrderSaturated77 7) (h11 : PeriodOrderSaturated77 11)
    (x : conductor77PeriodField) :
    IsIntegral ℤ x ↔ x ∈ periodIntegerSpan77 := by
  constructor
  · intro hx
    apply periodOrderSaturated77_pow 11 h11 3 x hx
    apply periodOrderSaturated77_pow 7 h7 5 (11^3 • x) (hx.smul (11^3 : ℤ))
    have hm := periodIntegerSpan77_discriminant_smul_mem hx
    have hc : (7^5 * 11^3 : ℚ) = ((7^5 * 11^3 : ℤ) : ℚ) := by norm_num
    rw [hc, Int.cast_smul_eq_zsmul] at hm
    simpa only [smul_smul] using hm
  · exact periodIntegerSpan77_isIntegral

end
end Biunimodular.F11
