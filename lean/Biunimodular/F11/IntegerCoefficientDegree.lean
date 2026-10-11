/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Mathlib.Algebra.Polynomial.Degree.Operations

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial

theorem integerCoefficientPolynomial_append_degree {R : Type*} [CommRing R] [IsDomain R]
    (a : List ℤ) (c : ℤ) (hc : (c : R) ≠ 0) :
    integerCoefficientEval (X : R[X]) (a ++ [c]) ≠ 0 ∧
      (integerCoefficientEval (X : R[X]) (a ++ [c])).natDegree = a.length := by
  induction a with
  | nil =>
    simp only [List.nil_append, integerCoefficientEval_singleton, List.length_nil]
    have he : (c : R[X]) = C (c : R) := by simp
    rw [he]
    exact ⟨C_ne_zero.mpr hc, natDegree_C _⟩
  | cons b bs ih =>
    let q : R[X] := X * integerCoefficientEval X (bs ++ [c])
    have hqn : q ≠ 0 := mul_ne_zero X_ne_zero ih.1
    have hqd : q.natDegree = bs.length + 1 := by
      simp only [q, natDegree_X_mul ih.1, ih.2]
    have hlt : (C (b : R)).degree < q.degree := by
      apply degree_C_le.trans_lt
      rw [degree_eq_natDegree hqn, hqd]
      exact_mod_cast Nat.zero_lt_succ bs.length
    have he : integerCoefficientEval (X : R[X]) ((b :: bs) ++ [c]) = C (b : R) + q := by
      simp only [List.cons_append, integerCoefficientEval]
      rw [map_intCast]
    rw [he]
    refine ⟨?_, ?_⟩
    · have hdeg := degree_add_eq_right_of_degree_lt hlt
      intro hz
      rw [hz, degree_zero] at hdeg
      exact hqn (degree_eq_bot.mp hdeg.symm)
    · rw [natDegree_add_eq_right_of_degree_lt hlt, hqd, List.length_cons]

end Biunimodular.F11
