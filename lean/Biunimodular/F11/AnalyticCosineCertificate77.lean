/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false

namespace Biunimodular.F11

open scoped BigOperators

/-- A rational cosine approximation obtained from thirty even terms of the
exponential series. -/
def cosineTaylor30Q77 (t : ℚ) : ℚ :=
  ∑ n ∈ Finset.range 30,
    (-1 : ℚ) ^ n * t ^ (2 * n) / (2 * n).factorial

private theorem imaginaryExpTaylor_real (t : ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range (2 * N),
      ((t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re =
      ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * t ^ (2 * n) / (2 * n).factorial := by
  have heven (n : ℕ) : ((t : ℂ) * Complex.I) ^ (2 * n) =
      (((-1 : ℝ) ^ n * t ^ (2 * n) : ℝ) : ℂ) := by
    rw [mul_pow, pow_mul Complex.I 2 n, Complex.I_sq]
    push_cast
    ring
  have hodd (n : ℕ) :
      (((t : ℂ) * Complex.I) ^ (2 * n + 1)).re = 0 := by
    have heq : ((t : ℂ) * Complex.I) ^ (2 * n + 1) =
        (((-1 : ℝ) ^ n * t ^ (2 * n) * t : ℝ) : ℂ) * Complex.I := by
      rw [pow_succ, heven, ← mul_assoc]
      exact congrArg (fun z : ℂ => z * Complex.I)
        (Complex.ofReal_mul ((-1 : ℝ) ^ n * t ^ (2 * n)) t).symm
    rw [heq, Complex.mul_I_re, Complex.ofReal_im]
    simp
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Complex.add_re, Complex.add_re, ih, Finset.sum_range_succ]
    simp only [← Complex.ofReal_natCast, Complex.div_ofReal_re,
      hodd, zero_div, add_zero, heven, Complex.ofReal_re]

/-- A uniform certified Taylor error on the angle range needed for
conductor-77 coordinates. -/
theorem cosineTaylor30Q77_error (t : ℚ) (ht : |(t : ℝ)| ≤ 8) :
    |Real.cos (t : ℝ) - (cosineTaylor30Q77 t : ℝ)| ≤
      (1 / 10 ^ 18 : ℝ) := by
  let z : ℂ := (t : ℝ) * Complex.I
  have hnorm : ‖z‖ = |(t : ℝ)| := by
    simp [z]
  have hsmall : ‖z‖ / (61 : ℝ) ≤ 1 / 2 := by
    rw [hnorm]
    linarith
  have hb := Complex.exp_bound' (n := 60) hsmall
  have hre := Complex.abs_re_le_norm
    (Complex.exp z - ∑ m ∈ Finset.range 60, z ^ m / (m.factorial : ℂ))
  have hsum :
      (∑ m ∈ Finset.range 60, z ^ m / (m.factorial : ℂ)).re =
        (cosineTaylor30Q77 t : ℝ) := by
    have h := imaginaryExpTaylor_real (t : ℝ) 30
    simpa only [z, cosineTaylor30Q77, Rat.cast_sum, Rat.cast_div,
      Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
      Rat.cast_natCast] using h
  have hcos : (Complex.exp z).re = Real.cos (t : ℝ) := by
    exact Complex.exp_ofReal_mul_I_re _
  rw [Complex.sub_re, hsum, hcos] at hre
  have hpower : ‖z‖ ^ 60 ≤ (8 : ℝ) ^ 60 := by
    rw [hnorm]
    gcongr
  have hbound : ‖z‖ ^ 60 / (60).factorial * 2 ≤ (1 / 10 ^ 18 : ℝ) := by
    calc
      ‖z‖ ^ 60 / (60).factorial * 2 ≤ (8 : ℝ) ^ 60 / (60).factorial * 2 := by
        gcongr
      _ ≤ (1 / 10 ^ 18 : ℝ) := by norm_num
  exact hre.trans (hb.trans hbound)

/-- The lower twenty-decimal rational bound for pi. -/
def piApproxQ77 : ℚ := 314159265358979323846 / 10 ^ 20

def conductor77AngleQ (k : ℕ) : ℚ := 2 * piApproxQ77 * k / 77

def conductor77CosApproxQ (k : ℕ) : ℚ :=
  cosineTaylor30Q77 (conductor77AngleQ k)

theorem conductor77AngleQ_cast (k : ℕ) :
    (conductor77AngleQ k : ℝ) = 2 * (piApproxQ77 : ℝ) * k / 77 := by
  simp [conductor77AngleQ]

theorem conductor77CosApproxQ_error (k : ℕ) (hk : k < 77) :
    |Real.cos (2 * Real.pi * k / 77) - (conductor77CosApproxQ k : ℝ)| ≤
      (2 / 10 ^ 18 : ℝ) := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hk76 : (k : ℝ) ≤ 76 := by exact_mod_cast (show k ≤ 76 by omega)
  have hpi : |Real.pi - (piApproxQ77 : ℝ)| ≤ (1 / 10 ^ 20 : ℝ) := by
    rw [abs_le]
    norm_num [piApproxQ77]
    constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]
  have hangle : |(conductor77AngleQ k : ℝ)| ≤ 8 := by
    rw [conductor77AngleQ_cast, abs_le]
    have hp0 : 0 ≤ (piApproxQ77 : ℝ) := by norm_num [piApproxQ77]
    have hp4 : (piApproxQ77 : ℝ) ≤ 4 := by norm_num [piApproxQ77]
    constructor
    · have hnonneg : 0 ≤ 2 * (piApproxQ77 : ℝ) * (k : ℝ) / 77 := by positivity
      linarith
    · nlinarith
  have hangleError :
      |2 * Real.pi * k / 77 - (conductor77AngleQ k : ℝ)| ≤
        (1 / 10 ^ 18 : ℝ) := by
    rw [conductor77AngleQ_cast]
    calc
      |2 * Real.pi * k / 77 - 2 * (piApproxQ77 : ℝ) * k / 77| =
          2 * |Real.pi - (piApproxQ77 : ℝ)| * k / 77 := by
        rw [show 2 * Real.pi * k / 77 - 2 * (piApproxQ77 : ℝ) * k / 77 =
          2 * (Real.pi - (piApproxQ77 : ℝ)) * k / 77 by ring]
        rw [abs_div, abs_mul, abs_mul]
        simp only [abs_of_nonneg hk0]
        norm_num
      _ ≤ 2 * (1 / 10 ^ 20 : ℝ) * 76 / 77 := by gcongr
      _ ≤ (1 / 10 ^ 18 : ℝ) := by norm_num
  have hcos := (Real.abs_cos_sub_cos_le
    (2 * Real.pi * k / 77) (conductor77AngleQ k : ℝ)).trans hangleError
  have hTaylor := cosineTaylor30Q77_error (conductor77AngleQ k) hangle
  calc
    |Real.cos (2 * Real.pi * k / 77) - (conductor77CosApproxQ k : ℝ)| ≤
        |Real.cos (2 * Real.pi * k / 77) - Real.cos (conductor77AngleQ k : ℝ)| +
          |Real.cos (conductor77AngleQ k : ℝ) - (conductor77CosApproxQ k : ℝ)| :=
      abs_sub_le _ _ _
    _ ≤ (2 / 10 ^ 18 : ℝ) := by
      change |Real.cos (2 * Real.pi * k / 77) - Real.cos (conductor77AngleQ k : ℝ)| +
        |Real.cos (conductor77AngleQ k : ℝ) -
          (cosineTaylor30Q77 (conductor77AngleQ k) : ℝ)| ≤ _
      linarith

end Biunimodular.F11
