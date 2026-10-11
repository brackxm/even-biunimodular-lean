/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorAnalyticApproximation77
import Biunimodular.F11.ASectorPeriodSubfieldValues77

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial
noncomputable section

private def quadraticPeriodExponents77 : List ℕ :=
  [1, 6, 13, 15, 36, 41, 62, 64, 71, 76,
   9, 16, 19, 23, 37, 40, 54, 58, 61, 68,
   4, 10, 17, 24, 25, 52, 53, 60, 67, 73]

private def quadraticPeriodApprox77 : ℚ :=
  2 * (quadraticPeriodExponents77.map conductor77CosApproxQ).sum - 1

private theorem quadraticPeriodApprox77_lower : 8 < quadraticPeriodApprox77 := by
  native_decide

private theorem quadraticPeriodEmbedding77_sum :
    conductor77AnalyticEmbedding periodQuadraticGenerator77 =
      2 * (quadraticPeriodExponents77.map (fun k => analyticZeta77 ^ k)).sum - 1 := by
  norm_num [periodQuadraticGenerator77, periodOrbit77, conductor77PeriodOrbitValue,
    conductor77PeriodOrbitPolynomials, quadraticPeriodExponents77,
    conductor77AnalyticEmbedding_zeta, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, map_ofNat]
  ring

private theorem list_sum_error (s : List ℕ) (f g : ℕ → ℝ) (ε : ℝ)
    (h : ∀ k ∈ s, |f k - g k| ≤ ε) :
    |(s.map f).sum - (s.map g).sum| ≤ (s.length : ℝ) * ε := by
  induction s with
  | nil => simp
  | cons k s ih =>
    have ht := ih (fun j hj => h j (List.mem_cons_of_mem k hj))
    have hk := h k (by simp)
    have ha := abs_add_le (f k - g k) ((s.map f).sum - (s.map g).sum)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    rw [add_sub_add_comm]
    linarith

theorem periodQuadraticGenerator77_analytic_real_pos :
    0 < (conductor77AnalyticEmbedding periodQuadraticGenerator77).re := by
  let f (k : ℕ) : ℝ := Real.cos (2 * Real.pi * k / 77)
  let g (k : ℕ) : ℝ := (conductor77CosApproxQ k : ℝ)
  have hb : ∀ k ∈ quadraticPeriodExponents77, k < 77 := by
    decide
  have herr := list_sum_error quadraticPeriodExponents77 f g (2 / 10^18)
    (fun k hk => conductor77CosApproxQ_error k (hb k hk))
  have hre : (conductor77AnalyticEmbedding periodQuadraticGenerator77).re =
      2 * (quadraticPeriodExponents77.map f).sum - 1 := by
    rw [quadraticPeriodEmbedding77_sum]
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, Complex.one_re]
    have hsum : ((quadraticPeriodExponents77.map (fun k => analyticZeta77 ^ k)).sum).re =
        (quadraticPeriodExponents77.map f).sum := by
      have hm := map_list_sum Complex.reAddGroupHom
        (quadraticPeriodExponents77.map (fun k => analyticZeta77 ^ k))
      simp only [Complex.coe_reAddGroupHom, List.map_map, Function.comp_def] at hm
      rw [hm]
      apply congrArg List.sum
      apply List.map_congr_left
      intro k hk
      rw [analyticZeta77_pow_real, Nat.mod_eq_of_lt (hb k hk)]
    rw [hsum]
  have happ : (quadraticPeriodApprox77 : ℝ) =
      2 * (quadraticPeriodExponents77.map g).sum - 1 := by
    simp [quadraticPeriodApprox77, g, Rat.cast_list_sum, List.map_map, Function.comp_def]
  have hl : (8 : ℝ) < (quadraticPeriodApprox77 : ℝ) := by
    exact_mod_cast quadraticPeriodApprox77_lower
  have hlen : quadraticPeriodExponents77.length = 30 := rfl
  rw [hlen] at herr
  rw [abs_le] at herr
  rw [hre]
  rw [happ] at hl
  norm_num at herr
  linarith

/-- At the specified embedding the quadratic period difference is
the positive square root, including its sign. -/
theorem periodQuadraticGenerator77_analytic_sqrt :
    conductor77AnalyticEmbedding periodQuadraticGenerator77 = (Real.sqrt 77 : ℂ) := by
  have hsq : conductor77AnalyticEmbedding periodQuadraticGenerator77 ^ 2 = (77 : ℂ) := by
    simpa only [map_pow, map_ofNat] using
      congrArg conductor77AnalyticEmbedding periodQuadraticGenerator77_square
  have hsqrt : (Real.sqrt 77 : ℂ) ^ 2 = (77 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 77)
  have hcases := (sq_eq_sq_iff_eq_or_eq_neg).mp (hsq.trans hsqrt.symm)
  rcases hcases with h | h
  · exact h
  · have hp := periodQuadraticGenerator77_analytic_real_pos
    rw [h, Complex.neg_re, Complex.ofReal_re] at hp
    linarith [Real.sqrt_nonneg (77 : ℝ)]

theorem periodOrbit77_analytic_even_half :
    conductor77AnalyticEmbedding (periodOrbit77 0 + periodOrbit77 2 + periodOrbit77 4) =
      ((1 + Real.sqrt 77) / 2 : ℂ) := by
  have h := congrArg conductor77AnalyticEmbedding periodOrbit77_even_half
  simp only [map_mul, map_add, map_one, map_ofNat,
    periodQuadraticGenerator77_analytic_sqrt] at h
  simp only [map_add]
  linear_combination h / 2

theorem periodOrbit77_analytic_odd_half :
    conductor77AnalyticEmbedding (periodOrbit77 1 + periodOrbit77 3 + periodOrbit77 5) =
      ((1 - Real.sqrt 77) / 2 : ℂ) := by
  have h := congrArg conductor77AnalyticEmbedding periodOrbit77_odd_half
  simp only [map_mul, map_sub, map_add, map_one, map_ofNat,
    periodQuadraticGenerator77_analytic_sqrt] at h
  simp only [map_add]
  linear_combination h / 2

end
end Biunimodular.F11
