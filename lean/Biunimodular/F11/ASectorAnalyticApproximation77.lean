/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.AnalyticCosineCertificate77
import Biunimodular.F11.ASectorAnalyticCoordinateDistinct77

set_option autoImplicit false

namespace Biunimodular.F11

open scoped BigOperators

/-- Rational approximation to the explicit conductor-77 coordinate. -/
def analyticASectorCoordinateApproxQ77 (e : ℕ) : ℚ :=
  -627 + ∑ n ∈ Finset.range 29,
    (aSectorCyclotomicCoeffs[n]! : ℚ) *
      (conductor77CosApproxQ ((26 * e * ((3 * (n + 1)) % 77)) % 77) +
       conductor77CosApproxQ ((26 * e * (77 - ((3 * (n + 1)) % 77))) % 77))

theorem analyticZeta77_pow_real (k : ℕ) :
    (analyticZeta77 ^ k).re = Real.cos (2 * Real.pi * ((k % 77 : ℕ) : ℝ) / 77) := by
  rw [pow_eq_pow_mod _ analyticZeta77_primitive.pow_eq_one]
  unfold analyticZeta77
  rw [← Complex.exp_nat_mul]
  have heq : ((k % 77 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 77) =
      ((2 * Real.pi * ((k % 77 : ℕ) : ℝ) / 77 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq]
  exact Complex.exp_ofReal_mul_I_re _

theorem analyticASectorCoordinate_cosine77 (e : ℕ) :
    analyticASectorCoordinate e =
      -627 + ∑ n ∈ Finset.range 29,
        (aSectorCyclotomicCoeffs[n]! : ℝ) *
          (Real.cos (2 * Real.pi * (((26 * e * ((3 * (n + 1)) % 77)) % 77 : ℕ) : ℝ) / 77) +
           Real.cos (2 * Real.pi * (((26 * e * (77 - ((3 * (n + 1)) % 77))) % 77 : ℕ) : ℝ) / 77)) := by
  have hp (k : ℕ) : ((analyticZeta77 ^ (26 * e)) ^ k).re =
      Real.cos (2 * Real.pi * (((26 * e * k) % 77 : ℕ) : ℝ) / 77) := by
    rw [← pow_mul]
    exact analyticZeta77_pow_real _
  simp only [analyticASectorCoordinate, aSectorX77Pair, Complex.add_re,
    Complex.neg_re, Complex.re_ofNat, Complex.re_sum, Complex.mul_re,
    Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, hp]

/-- The rational approximation has a certified error much smaller than the
separation between the physical A-sector roots. -/
theorem analyticASectorCoordinateApproxQ77_error (e : ℕ) :
    |analyticASectorCoordinate e - (analyticASectorCoordinateApproxQ77 e : ℝ)| ≤
      (1 / 10 ^ 10 : ℝ) := by
  let c (n : ℕ) : ℝ := (aSectorCyclotomicCoeffs[n]! : ℝ)
  let k1 (n : ℕ) := (26 * e * ((3 * (n + 1)) % 77)) % 77
  let k2 (n : ℕ) := (26 * e * (77 - ((3 * (n + 1)) % 77))) % 77
  let f (n : ℕ) : ℝ := c n *
    (Real.cos (2 * Real.pi * k1 n / 77) + Real.cos (2 * Real.pi * k2 n / 77))
  let g (n : ℕ) : ℝ := c n *
    ((conductor77CosApproxQ (k1 n) : ℝ) + (conductor77CosApproxQ (k2 n) : ℝ))
  have htrue : analyticASectorCoordinate e = -627 + ∑ n ∈ Finset.range 29, f n :=
    analyticASectorCoordinate_cosine77 e
  have happ : (analyticASectorCoordinateApproxQ77 e : ℝ) =
      -627 + ∑ n ∈ Finset.range 29, g n := by
    simp [analyticASectorCoordinateApproxQ77, g, c, k1, k2]
  have herr (n : ℕ) : |f n - g n| ≤ |c n| * (4 / 10 ^ 18 : ℝ) := by
    have h1 := conductor77CosApproxQ_error (k1 n)
      (Nat.mod_lt _ (by norm_num : 0 < 77))
    have h2 := conductor77CosApproxQ_error (k2 n)
      (Nat.mod_lt _ (by norm_num : 0 < 77))
    have hsum :
        |(Real.cos (2 * Real.pi * k1 n / 77) - (conductor77CosApproxQ (k1 n) : ℝ)) +
          (Real.cos (2 * Real.pi * k2 n / 77) - (conductor77CosApproxQ (k2 n) : ℝ))| ≤
          (4 / 10 ^ 18 : ℝ) := by
      have ht := abs_add_le
        (Real.cos (2 * Real.pi * k1 n / 77) - (conductor77CosApproxQ (k1 n) : ℝ))
        (Real.cos (2 * Real.pi * k2 n / 77) - (conductor77CosApproxQ (k2 n) : ℝ))
      linarith
    calc
      |f n - g n| = |c n| *
          |(Real.cos (2 * Real.pi * k1 n / 77) - (conductor77CosApproxQ (k1 n) : ℝ)) +
            (Real.cos (2 * Real.pi * k2 n / 77) - (conductor77CosApproxQ (k2 n) : ℝ))| := by
        rw [← abs_mul]
        congr 1
        dsimp [f, g]
        ring
      _ ≤ |c n| * (4 / 10 ^ 18 : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  have hcsZ : (∑ n ∈ Finset.range 29, |aSectorCyclotomicCoeffs[n]!|) ≤
      (100000 : ℤ) := by native_decide
  have hcs : (∑ n ∈ Finset.range 29, |c n|) ≤ (100000 : ℝ) := by
    dsimp [c]
    exact_mod_cast hcsZ
  rw [htrue, happ]
  have hdiff : (-627 + ∑ n ∈ Finset.range 29, f n) -
      (-627 + ∑ n ∈ Finset.range 29, g n) =
      ∑ n ∈ Finset.range 29, (f n - g n) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  calc
    |∑ n ∈ Finset.range 29, (f n - g n)| ≤
        ∑ n ∈ Finset.range 29, |f n - g n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range 29, |c n| * (4 / 10 ^ 18 : ℝ) :=
      Finset.sum_le_sum fun n _ => herr n
    _ = (∑ n ∈ Finset.range 29, |c n|) * (4 / 10 ^ 18 : ℝ) := by
      rw [Finset.sum_mul]
    _ ≤ 100000 * (4 / 10 ^ 18 : ℝ) := by gcongr
    _ ≤ (1 / 10 ^ 10 : ℝ) := by norm_num

end Biunimodular.F11
