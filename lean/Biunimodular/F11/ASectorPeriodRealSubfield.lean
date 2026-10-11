/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodARealization
import Biunimodular.F11.ASectorFieldGeneration

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

theorem star_pow_complement77 (μ : ℂ) (hμ : μ ^ 77 = 1)
    (a : ℕ) (ha : a ≤ 77) : star (μ ^ a) = μ ^ (77 - a) := by
  have hnorm : ‖μ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hμ (by norm_num)
  have hstar : star μ = μ⁻¹ := by
    rw [RCLike.star_def]
    exact (Complex.inv_eq_conj hnorm).symm
  rw [star_pow, hstar, inv_pow]
  apply inv_eq_of_mul_eq_one_left
  have hexp : (77 - a) + a = 77 := by omega
  rw [← pow_add, hexp]
  exact hμ

private theorem conductor77_period_value_real (μ : ℂ) (hμ : μ ^ 77 = 1) :
    star (μ ^ 1 + μ ^ 6 + μ ^ 13 + μ ^ 15 + μ ^ 36 +
      μ ^ 41 + μ ^ 62 + μ ^ 64 + μ ^ 71 + μ ^ 76) =
      μ ^ 1 + μ ^ 6 + μ ^ 13 + μ ^ 15 + μ ^ 36 +
      μ ^ 41 + μ ^ 62 + μ ^ 64 + μ ^ 71 + μ ^ 76 := by
  have h1 := star_pow_complement77 μ hμ 1 (by norm_num)
  have h6 := star_pow_complement77 μ hμ 6 (by norm_num)
  have h13 := star_pow_complement77 μ hμ 13 (by norm_num)
  have h15 := star_pow_complement77 μ hμ 15 (by norm_num)
  have h36 := star_pow_complement77 μ hμ 36 (by norm_num)
  have h41 := star_pow_complement77 μ hμ 41 (by norm_num)
  have h62 := star_pow_complement77 μ hμ 62 (by norm_num)
  have h64 := star_pow_complement77 μ hμ 64 (by norm_num)
  have h71 := star_pow_complement77 μ hμ 71 (by norm_num)
  have h76 := star_pow_complement77 μ hμ 76 (by norm_num)
  simp only [star_add, h1, h6, h13, h15, h36,
    h41, h62, h64, h71, h76]
  ring

/-- The ten-element period is fixed by complex conjugation under every
embedding, hence lies in the maximal real conductor-77 subfield. -/
theorem periodEta77_mem_maximalReal :
    periodEta77 ∈ NumberField.maximalRealSubfield Conductor77Cyclotomic := by
  rw [NumberField.mem_maximalRealSubfield_iff]
  intro φ
  let μ : ℂ := φ zeta77
  have hζ : zeta77 ^ 77 = 1 := by
    exact (IsCyclotomicExtension.zeta_spec 77 ℚ
      Conductor77Cyclotomic).pow_eq_one
  have hμ : μ ^ 77 = 1 := by
    simpa only [μ, map_pow, map_one] using congrArg φ hζ
  have hvalue : φ periodEta77 =
      μ ^ 1 + μ ^ 6 + μ ^ 13 + μ ^ 15 + μ ^ 36 +
        μ ^ 41 + μ ^ 62 + μ ^ 64 + μ ^ 71 + μ ^ 76 := by
    simp [periodEta77, conductor77PeriodPolynomial, μ]
  rw [hvalue]
  exact conductor77_period_value_real μ hμ

/-- The invariant coordinate obtained from the real period is real as well. -/
theorem periodInvariantU77_mem_maximalReal :
    periodInvariantU77 ∈
      NumberField.maximalRealSubfield Conductor77Cyclotomic := by
  let R := NumberField.maximalRealSubfield Conductor77Cyclotomic
  have hη := periodEta77_mem_maximalReal
  have hm (c : ℤ) (k : ℕ) :
      (c : Conductor77Cyclotomic) * periodEta77 ^ k ∈ R :=
    R.mul_mem (R.intCast_mem c) (R.pow_mem hη k)
  have hN :
      (1236 * periodEta77 ^ 5 + 1432 * periodEta77 ^ 4 -
        21392 * periodEta77 ^ 3 - 20240 * periodEta77 ^ 2 +
        87372 * periodEta77 + 50820 : Conductor77Cyclotomic) / 13 ∈ R := by
    apply R.div_mem
    · apply R.add_mem
      · apply R.add_mem
        · apply R.sub_mem
          · apply R.sub_mem
            · exact R.add_mem (hm 1236 5) (hm 1432 4)
            · exact hm 21392 3
          · exact hm 20240 2
        · simpa only [pow_one, Int.cast_ofNat] using hm 87372 1
      · exact R.intCast_mem 50820
    · exact R.intCast_mem 13
  simpa only [periodInvariantU77, periodN77, eval₂_add,
    eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_ofNat] using hN

end Biunimodular.F11
