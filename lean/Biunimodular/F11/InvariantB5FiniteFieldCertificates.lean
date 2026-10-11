/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic.IntervalCases
import Biunimodular.F11.InvariantPolynomialData
import Biunimodular.F11.FiniteFieldIrreducibilityCriterion
import Biunimodular.F11.InvariantB5FiniteFieldData
import Biunimodular.F11.InvariantB5FrobeniusStep2
import Biunimodular.F11.InvariantB5FrobeniusStep3
import Biunimodular.F11.InvariantB5FrobeniusStep4
import Biunimodular.F11.InvariantB5FrobeniusStep5
import Biunimodular.F11.InvariantB5FrobeniusStep6
import Biunimodular.F11.InvariantB5FrobeniusStep7
import Biunimodular.F11.InvariantB5FrobeniusStep8

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

/-!
The expensive characteristic-5 quotient identities are compiled in independent
modules so Lake can schedule them concurrently.  This file only assembles the
Frobenius chain, three small Bezout certificates, and the Rabin criterion.

The cumulative chain is kept in `frobeniusIter` form.  This prevents Lean from
normalizing the large natural exponents `5^7` and `5^8` at every intermediate
step.  The final conversion to the standard `X^(p^n)` form is performed only in
a generic wrapper where `p` and `n` remain symbolic during elaboration.
-/

/-- First Frobenius remainder congruence for the B polynomial. -/
theorem b5_frobenius_iter_dvd1 : invariantB5 ∣ frobeniusIter 5 1 - b5r1 := by
  simp [frobeniusIter, b5r1]

/-- Cumulative Frobenius congruence through step 2. -/
theorem b5_frobenius_iter_dvd2 : invariantB5 ∣ frobeniusIter 5 2 - b5r2 := by
  exact frobeniusIter_dvd_next (p := 5) (e := 1) b5_frobenius_iter_dvd1
    ⟨b5q2, b5_frobenius_step2_identity⟩

/-- Cumulative Frobenius congruence through step 3. -/
theorem b5_frobenius_iter_dvd3 : invariantB5 ∣ frobeniusIter 5 3 - b5r3 := by
  exact frobeniusIter_dvd_next (p := 5) (e := 2) b5_frobenius_iter_dvd2
    ⟨b5q3, b5_frobenius_step3_identity⟩

/-- Cumulative Frobenius congruence through step 4. -/
theorem b5_frobenius_iter_dvd4 : invariantB5 ∣ frobeniusIter 5 4 - b5r4 := by
  exact frobeniusIter_dvd_next (p := 5) (e := 3) b5_frobenius_iter_dvd3
    ⟨b5q4, b5_frobenius_step4_identity⟩

/-- Cumulative Frobenius congruence through step 5. -/
theorem b5_frobenius_iter_dvd5 : invariantB5 ∣ frobeniusIter 5 5 - b5r5 := by
  exact frobeniusIter_dvd_next (p := 5) (e := 4) b5_frobenius_iter_dvd4
    ⟨b5q5, b5_frobenius_step5_identity⟩

/-- Cumulative Frobenius congruence through step 6. -/
theorem b5_frobenius_iter_dvd6 : invariantB5 ∣ frobeniusIter 5 6 - b5r6 := by
  exact frobeniusIter_dvd_next (p := 5) (e := 5) b5_frobenius_iter_dvd5
    ⟨b5q6, b5_frobenius_step6_identity⟩

/-- Cumulative Frobenius congruence through step 7. -/
theorem b5_frobenius_iter_dvd7 : invariantB5 ∣ frobeniusIter 5 7 - b5r7 := by
  exact frobeniusIter_dvd_next (p := 5) (e := 6) b5_frobenius_iter_dvd6
    ⟨b5q7, b5_frobenius_step7_identity⟩

/-- Cumulative Frobenius congruence through step 8. -/
theorem b5_frobenius_iter_dvd8 : invariantB5 ∣ frobeniusIter 5 8 - b5r8 := by
  exact frobeniusIter_dvd_next (p := 5) (e := 7) b5_frobenius_iter_dvd7
    ⟨b5q8, b5_frobenius_step8_identity⟩

/-- Feed a recursive Frobenius certificate to the standard irreducibility
criterion while the exponent parameters are still symbolic. -/
private theorem irreducible_of_frobenius_iter_certificate
    {p n : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
    (hfmonic : f.Monic)
    (hdeg : f.natDegree = n)
    (hn : 0 < n)
    (hfull : f ∣ frobeniusIter p n - X)
    (hproper : ∀ d : ℕ, d ∣ n → 0 < d → d < n →
      IsCoprime f (X ^ p ^ d - X)) :
    Irreducible f := by
  apply irreducible_of_frobenius_certificate
      (p := p) (n := n) (f := f)
  · exact hfmonic
  · exact hdeg
  · exact hn
  · rw [← frobeniusIter_eq_X_pow p n]
    exact hfull
  · exact hproper

/-- B is irreducible modulo 5. -/
theorem invariantB5_irreducible : Irreducible invariantB5 := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let bLow : (ZMod 5)[X] := 1 + 2*X^2 + 4*X^3 + X^5 + 4*X^6 + X^7
  have hBform : invariantB5 = X^8 + bLow := by
    simp only [invariantB5, bLow]
    ring
  have hBlow : bLow.degree < 8 := by
    simp only [bLow]
    compute_degree; norm_num
  have hm : invariantB5.Monic := by
    rw [hBform]
    exact monic_X_pow_add hBlow
  have hdeg : invariantB5.natDegree = 8 := by
    rw [hBform, natDegree_add_eq_left_of_degree_lt]
    · simp
    · simpa using hBlow
  have hfullIter : invariantB5 ∣ frobeniusIter 5 8 - X := by
    simpa only [b5r8] using b5_frobenius_iter_dvd8
  have hc1small : IsCoprime invariantB5 (b5r1 - X) := by
    refine ⟨X ^ 4 - 2 * X ^ 3 - X ^ 2 + 1,
      -X ^ 7 + X ^ 6 - X ^ 5 - 2 * X ^ 4 - X ^ 3 + 2 * X ^ 2 + X, ?_⟩
    simp only [invariantB5, b5r1]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h1num : invariantB5 ∣ X ^ 5 ^ 1 - b5r1 := by
    rw [← frobeniusIter_eq_X_pow 5 1]
    exact b5_frobenius_iter_dvd1
  have hc1 : IsCoprime invariantB5 (X ^ 5 ^ 1 - X) := by
    apply isCoprime_of_dvd_sub hc1small
    convert h1num using 1
    all_goals ring
  have hc2small : IsCoprime invariantB5 (b5r2 - X) := by
    refine ⟨2 * X ^ 5 + X ^ 4 - X ^ 3 - 2 * X ^ 2 - 2 * X + 1,
      -2 * X ^ 6 - X ^ 5 - 2 * X ^ 4 - X ^ 3 + X ^ 2 + 2 * X - 1, ?_⟩
    simp only [invariantB5, b5r2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2num : invariantB5 ∣ X ^ 5 ^ 2 - b5r2 := by
    rw [← frobeniusIter_eq_X_pow 5 2]
    exact b5_frobenius_iter_dvd2
  have hc2 : IsCoprime invariantB5 (X ^ 5 ^ 2 - X) := by
    apply isCoprime_of_dvd_sub hc2small
    convert h2num using 1
    all_goals ring
  have hc4small : IsCoprime invariantB5 (b5r4 - X) := by
    refine ⟨X ^ 4 - 2 * X ^ 3 - X - 1,
      -2 * X ^ 7 - X ^ 6 - X ^ 3 - 2 * X + 2, ?_⟩
    simp only [invariantB5, b5r4]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4num : invariantB5 ∣ X ^ 5 ^ 4 - b5r4 := by
    rw [← frobeniusIter_eq_X_pow 5 4]
    exact b5_frobenius_iter_dvd4
  have hc4 : IsCoprime invariantB5 (X ^ 5 ^ 4 - X) := by
    apply isCoprime_of_dvd_sub hc4small
    convert h4num using 1
    all_goals ring
  apply irreducible_of_frobenius_iter_certificate
      (p := 5) (n := 8) (f := invariantB5)
  · exact hm
  · exact hdeg
  · norm_num
  · exact hfullIter
  · intro d hd hdpos hdlt
    interval_cases d
    · exact hc1
    · exact hc2
    · norm_num at hd
    · exact hc4
    · norm_num at hd
    · norm_num at hd
    · norm_num at hd

end Biunimodular.F11
