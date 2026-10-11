/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Biunimodular.F11.InvariantPolynomialData
import Biunimodular.F11.FiniteFieldIrreducibilityCriterion

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

/-!
The degree-six finite-field certificate is isolated from the B-sector so Lake
can compile the two arithmetic sectors independently.  The pinned polynomial
representation is non-executable for subtraction/semiring operations, so the
explicit A-sector quotient and Bézout identities are kernel-checked by
`ring_nf` rather than `native_decide`.
-/

/-- A is irreducible modulo 3. -/
theorem invariantA3_irreducible : Irreducible invariantA3 := by
  let aLow : (ZMod 3)[X] := 1 + 2*X + X^2 + 2*X^4 + X^5
  have hAform : invariantA3 = X^6 + aLow := by
    simp only [invariantA3, aLow]
    ring
  have hAlow : aLow.degree < 6 := by
    simp only [aLow]
    compute_degree; norm_num
  have hm : invariantA3.Monic := by
    rw [hAform]
    exact monic_X_pow_add hAlow
  have hdeg : invariantA3.natDegree = 6 := by
    rw [hAform, natDegree_add_eq_left_of_degree_lt]
    · simp
    · simpa using hAlow
  let r1 : (ZMod 3)[X] := X ^ 3
  let r2 : (ZMod 3)[X] := X ^ 5 - X ^ 4 - X ^ 3 + X
  let r3 : (ZMod 3)[X] := -X ^ 5 - X ^ 3 + X ^ 2
  let r4 : (ZMod 3)[X] := -X ^ 5 + X ^ 4 + X ^ 3 + X + 1
  let r5 : (ZMod 3)[X] := X ^ 5 - X ^ 2 + 1
  let r6 : (ZMod 3)[X] := X
  let q2 : (ZMod 3)[X] := X ^ 3 - X ^ 2 - X
  let q3 : (ZMod 3)[X] :=
    X ^ 9 - X ^ 8 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 + X ^ 3 - X ^ 2
  let q4 : (ZMod 3)[X] :=
    -X ^ 9 + X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 2 + X - 1
  let q5 : (ZMod 3)[X] :=
    -X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2
  let q6 : (ZMod 3)[X] :=
    X ^ 9 - X ^ 8 - X ^ 7 + X ^ 5 + X ^ 4 - X ^ 3 - X ^ 2 + 1
  have h1 : invariantA3 ∣ X ^ 3 ^ 1 - r1 := by simp [r1]
  have hs2 : invariantA3 ∣ r1 ^ 3 - r2 := by
    refine ⟨q2, ?_⟩
    simp only [r1, r2, q2, invariantA3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : invariantA3 ∣ X ^ 3 ^ 2 - r2 := frobenius_dvd_next h1 hs2
  have hs3 : invariantA3 ∣ r2 ^ 3 - r3 := by
    refine ⟨q3, ?_⟩
    simp only [r2, r3, q3, invariantA3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h3 : invariantA3 ∣ X ^ 3 ^ 3 - r3 := frobenius_dvd_next h2 hs3
  have hs4 : invariantA3 ∣ r3 ^ 3 - r4 := by
    refine ⟨q4, ?_⟩
    simp only [r3, r4, q4, invariantA3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : invariantA3 ∣ X ^ 3 ^ 4 - r4 := frobenius_dvd_next h3 hs4
  have hs5 : invariantA3 ∣ r4 ^ 3 - r5 := by
    refine ⟨q5, ?_⟩
    simp only [r4, r5, q5, invariantA3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h5 : invariantA3 ∣ X ^ 3 ^ 5 - r5 := frobenius_dvd_next h4 hs5
  have hs6 : invariantA3 ∣ r5 ^ 3 - r6 := by
    refine ⟨q6, ?_⟩
    simp only [r5, r6, q6, invariantA3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h6 : invariantA3 ∣ X ^ 3 ^ 6 - r6 := frobenius_dvd_next h5 hs6
  have hfull : invariantA3 ∣ X ^ 3 ^ 6 - X := by simpa [r6] using h6
  have hc1small : IsCoprime invariantA3 (r1 - X) := by
    refine ⟨X ^ 2 + 1,
      -X ^ 5 - X ^ 4 - X ^ 3 + X ^ 2 - X - 1, ?_⟩
    simp only [invariantA3, r1]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have hc1 : IsCoprime invariantA3 (X ^ 3 ^ 1 - X) := by
    apply isCoprime_of_dvd_sub hc1small
    convert h1 using 1
    all_goals ring
  have hc2small : IsCoprime invariantA3 (r2 - X) := by
    refine ⟨X ^ 4 + X + 1,
      -X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 - X + 1, ?_⟩
    simp only [invariantA3, r2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have hc2 : IsCoprime invariantA3 (X ^ 3 ^ 2 - X) := by
    apply isCoprime_of_dvd_sub hc2small
    convert h2 using 1
    all_goals ring
  have hc3small : IsCoprime invariantA3 (r3 - X) := by
    refine ⟨-X ^ 4 + X ^ 3 - X ^ 2 - X + 1,
      -X ^ 5 - X ^ 3 - X ^ 2 - X + 1, ?_⟩
    simp only [invariantA3, r3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have hc3 : IsCoprime invariantA3 (X ^ 3 ^ 3 - X) := by
    apply isCoprime_of_dvd_sub hc3small
    convert h3 using 1
    all_goals ring
  apply irreducible_of_frobenius_certificate
      (p := 3) (n := 6) (f := invariantA3)
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

end Biunimodular.F11
