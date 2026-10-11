/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormDet
import Biunimodular.F11.InvariantPolynomialData
import Biunimodular.F11.FiniteFieldIrreducibilityCriterion

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Exact conductor-77 certificates for the A-sector

This file contains only finite algebraic data used by the F11 arithmetic
conductor-77 arithmetic. It deliberately avoids any choice of abstract number-field API:
the exact polynomial identities can be replayed independently and then wired
into the repository's cyclotomic-field layer.
-/

/-- Minimal polynomial of the six conductor-77 Gaussian periods. -/
def periodC77 : ℤ[X] :=
  X^6 - X^5 - 20*X^4 + 20*X^3 + 106*X^2 - 106*X - 83

/-- Polynomial giving the invariant `u = N(η)/13` on the six embeddings. -/
def periodN77 : ℤ[X] :=
  1236*X^5 + 1432*X^4 - 21392*X^3 - 20240*X^2 + 87372*X + 50820

/-- Mod-2 reduction of the period sextic. -/
def periodC77mod2 : (ZMod 2)[X] := X^6 + X^5 + 1

theorem periodC77_mod2 :
    periodC77.map (Int.castRingHom (ZMod 2)) = periodC77mod2 := by
  norm_num [periodC77, periodC77mod2]
  all_goals reduce_mod_char

/-- The finite-field irreducibility certificate for the period sextic. -/
theorem periodC77mod2_irreducible : Irreducible periodC77mod2 := by
  let cLow : (ZMod 2)[X] := X^5 + 1
  have hCform : periodC77mod2 = X^6 + cLow := by
    simp only [periodC77mod2, cLow]
    ring
  have hClow : cLow.degree < 6 := by
    simp only [cLow]
    compute_degree; norm_num
  have hm : periodC77mod2.Monic := by
    rw [hCform]
    exact monic_X_pow_add hClow
  have hdeg : periodC77mod2.natDegree = 6 := by
    rw [hCform, natDegree_add_eq_left_of_degree_lt]
    · simp
    · simpa using hClow
  let r1 : (ZMod 2)[X] := X ^ 2
  let r2 : (ZMod 2)[X] := X ^ 4
  let r3 : (ZMod 2)[X] := X ^ 5 + X ^ 2 + X + 1
  let r4 : (ZMod 2)[X] := X ^ 5 + X ^ 3 + X
  let r5 : (ZMod 2)[X] := X ^ 4 + X ^ 3 + X
  let r6 : (ZMod 2)[X] := X
  let q3 : (ZMod 2)[X] := X ^ 2 + X + 1
  let q4 : (ZMod 2)[X] := X ^ 4 + X ^ 3 + X ^ 2 + X + 1
  let q5 : (ZMod 2)[X] := X ^ 4 + X ^ 3 + X ^ 2 + X
  let q6 : (ZMod 2)[X] := X ^ 2 + X
  have h1 : periodC77mod2 ∣ X ^ 2 ^ 1 - r1 := by simp [r1]
  have hs2 : periodC77mod2 ∣ r1 ^ 2 - r2 := by
    have hz : r1 ^ 2 - r2 = 0 := by
      simp [r1, r2]
      ring
    rw [hz]
    exact dvd_zero _
  have h2 : periodC77mod2 ∣ X ^ 2 ^ 2 - r2 := frobenius_dvd_next h1 hs2
  have hs3 : periodC77mod2 ∣ r2 ^ 2 - r3 := by
    refine ⟨q3, ?_⟩
    simp only [r2, r3, q3, periodC77mod2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h3 : periodC77mod2 ∣ X ^ 2 ^ 3 - r3 := frobenius_dvd_next h2 hs3
  have hs4 : periodC77mod2 ∣ r3 ^ 2 - r4 := by
    refine ⟨q4, ?_⟩
    simp only [r3, r4, q4, periodC77mod2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : periodC77mod2 ∣ X ^ 2 ^ 4 - r4 := frobenius_dvd_next h3 hs4
  have hs5 : periodC77mod2 ∣ r4 ^ 2 - r5 := by
    refine ⟨q5, ?_⟩
    simp only [r4, r5, q5, periodC77mod2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h5 : periodC77mod2 ∣ X ^ 2 ^ 5 - r5 := frobenius_dvd_next h4 hs5
  have hs6 : periodC77mod2 ∣ r5 ^ 2 - r6 := by
    refine ⟨q6, ?_⟩
    simp only [r5, r6, q6, periodC77mod2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h6 : periodC77mod2 ∣ X ^ 2 ^ 6 - r6 := frobenius_dvd_next h5 hs6
  have hfull : periodC77mod2 ∣ X ^ 2 ^ 6 - X := by simpa [r6] using h6
  have hc1small : IsCoprime periodC77mod2 (r1 - X) := by
    refine ⟨1, X ^ 4, ?_⟩
    simp only [periodC77mod2, r1]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have hc1 : IsCoprime periodC77mod2 (X ^ 2 ^ 1 - X) := by
    apply isCoprime_of_dvd_sub hc1small
    convert h1 using 1
    all_goals ring
  have hc2small : IsCoprime periodC77mod2 (r2 - X) := by
    refine ⟨X ^ 3 + X + 1, X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1, ?_⟩
    simp only [periodC77mod2, r2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have hc2 : IsCoprime periodC77mod2 (X ^ 2 ^ 2 - X) := by
    apply isCoprime_of_dvd_sub hc2small
    convert h2 using 1
    all_goals ring
  have hc3small : IsCoprime periodC77mod2 (r3 - X) := by
    refine ⟨X ^ 2 + X, X ^ 3 + X + 1, ?_⟩
    simp only [periodC77mod2, r3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have hc3 : IsCoprime periodC77mod2 (X ^ 2 ^ 3 - X) := by
    apply isCoprime_of_dvd_sub hc3small
    convert h3 using 1
    all_goals ring
  apply irreducible_of_frobenius_certificate
      (p := 2) (n := 6) (f := periodC77mod2)
  · exact hm
  · exact hdeg
  · norm_num
  · exact hfull
  · intro d hd hdpos hdlt
    interval_cases d
    · exact hc1
    · exact hc2
    · exact hc3
    · norm_num at hd
    · norm_num at hd

/-- Coefficient list, low-to-high, of the exact resultant in `u`, divided by
`13^6`. It is exactly `invariantA`. The full bivariate resultant identity is
replayed independently by `verify_arithmetic_theorem.py`. -/
def periodAResultantQuotientCoeffs : List ℤ :=
  [692224, -84262912, 1012283392, -1009036608,
   10298240, -6320, 1]

theorem periodAResultantQuotientCoeffs_exact :
    periodAResultantQuotientCoeffs =
      [692224, -84262912, 1012283392, -1009036608,
       10298240, -6320, 1] := by
  rfl

/-- The subgroup `H₀` used for the six Gaussian periods. -/
def conductor77H0 : Finset (ZMod 77) :=
  {1, 6, 13, 15, 36, 41, 62, 64, 71, 76}

/-- `6^5 = -1 (mod 77)`. -/
theorem six_pow_five_mod77 : (6 : ZMod 77)^5 = -1 := by
  native_decide

/-- `6` has order ten modulo 77, witnessed by its ten distinct powers. -/
def conductor77Powers6 : List (ZMod 77) :=
  (List.range 10).map (fun n => (6 : ZMod 77)^n)

theorem conductor77Powers6_nodup : conductor77Powers6.Nodup := by
  native_decide

theorem conductor77Powers6_eq_H0 :
    conductor77Powers6.toFinset = conductor77H0 := by
  native_decide

/-- Polynomial discriminant of `C`; its square-free field-discriminant part
is `7^5 * 11^3`, with index factor `13^4`. -/
def periodC77Discriminant : ℤ := 638912911637

theorem periodC77_discriminant_value :
    periodC77.discr = periodC77Discriminant := by
  let low : ℤ[X] :=
    -X^5 - 20*X^4 + 20*X^3 + 106*X^2 - 106*X - 83
  have hform : periodC77 = X^6 + low := by
    simp only [periodC77, low]
    ring
  have hlow : low.degree < 6 := by
    simp only [low]
    compute_degree; norm_num
  have hdeg : periodC77.natDegree = 6 := by
    rw [hform, natDegree_add_eq_left_of_degree_lt]
    · simp
    · simpa using hlow
  have hdegExplicit :
      (X^6 - X^5 - 20*X^4 + 20*X^3 + 106*X^2 - 106*X - 83 : ℤ[X]).natDegree = 6 := by
    simpa only [periodC77] using hdeg
  let e : Fin (periodC77.natDegree - 1 + periodC77.natDegree) ≃ Fin 11 :=
    finCongr (by rw [hdeg])
  rw [Polynomial.discr, ← Matrix.det_reindex_self e]
  have hmat : periodC77.sylvesterDeriv.reindex e e =
      !![-83, 0, 0, 0, 0, -106, 0, 0, 0, 0, 0;
         -106, -83, 0, 0, 0, 212, -106, 0, 0, 0, 0;
         106, -106, -83, 0, 0, 60, 212, -106, 0, 0, 0;
         20, 106, -106, -83, 0, -80, 60, 212, -106, 0, 0;
         -20, 20, 106, -106, -83, -5, -80, 60, 212, -106, 0;
         -1, -20, 20, 106, -106, 6, -5, -80, 60, 212, -106;
         1, -1, -20, 20, 106, 0, 6, -5, -80, 60, 212;
         0, 1, -1, -20, 20, 0, 0, 6, -5, -80, 60;
         0, 0, 1, -1, -20, 0, 0, 0, 6, -5, -80;
         0, 0, 0, 1, -1, 0, 0, 0, 0, 6, -5;
         0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 6] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [e, Polynomial.sylvesterDeriv, Polynomial.sylvester, hdeg,
        Polynomial.coeff_derivative, Fin.addCases, Matrix.reindex_apply,
        finCongr_symm, Matrix.submatrix_apply, finCongr_apply,
        Fin.cast_mk, Matrix.of_apply] <;>
      norm_num [periodC77, hdegExplicit, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  rw [hmat]
  simp only [norm_det]
  norm_num [hdeg, periodC77Discriminant]

theorem periodC77_discriminant_decomposition :
    periodC77Discriminant = 13^4 * 7^5 * 11^3 := by
  native_decide

/-- The field-discriminant value asserted for the cyclic sextic period field. -/
def conductor77SexticFieldDisc : ℤ := 7^5 * 11^3

/-- Finite arithmetic content of the conductor pattern
`77,7,77,7,77`. -/
def conductor77NontrivialCharacterConductors : List ℕ := [77, 7, 77, 7, 77]

theorem conductor77_conductor_discriminant_product :
    (conductor77NontrivialCharacterConductors.foldl (· * ·) 1 : ℕ) =
      7^5 * 11^3 := by
  native_decide

end

end Biunimodular.F11
