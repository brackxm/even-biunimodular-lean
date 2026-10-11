/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientDifferential
import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Monic

set_option autoImplicit false

namespace Biunimodular.F11

def integerCoefficientEqualMod (p : ℕ) (a b : List ℤ) : Bool :=
  (integerCoefficientAdd a (integerCoefficientScale (-1) b)).all
    (fun c ↦ c % (p : ℤ) == 0)

theorem integerCoefficientEval_zero_of_all_mod {R : Type*} [CommRing R]
    (p : ℕ) [CharP R p] (x : R) (a : List ℤ)
    (h : a.all (fun c ↦ c % (p : ℤ) == 0) = true) :
    integerCoefficientEval x a = 0 := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    have hs : a % (p : ℤ) = 0 ∧ as.all (fun c ↦ c % (p : ℤ) == 0) = true := by
      simpa using h
    have hz : (a : R) = 0 := by
      rw [CharP.intCast_eq_intCast_mod R p, hs.1, Int.cast_zero]
    simp only [integerCoefficientEval, hz, ih hs.2, mul_zero, add_zero]

theorem integerCoefficientEval_eq_of_equal_mod {R : Type*} [CommRing R]
    (p : ℕ) [CharP R p] (x : R) (a b : List ℤ)
    (h : integerCoefficientEqualMod p a b = true) :
    integerCoefficientEval x a = integerCoefficientEval x b := by
  have hz := integerCoefficientEval_zero_of_all_mod p x
    (integerCoefficientAdd a (integerCoefficientScale (-1) b)) h
  rw [integerCoefficientEval_add, integerCoefficientEval_scale] at hz
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hz)

open Polynomial

theorem integerCoefficientPolynomial_monic_degree {R : Type*} [CommRing R] [Nontrivial R]
    (a : List ℤ) :
    (integerCoefficientEval (X : R[X]) (a ++ [1])).Monic ∧
      (integerCoefficientEval (X : R[X]) (a ++ [1])).natDegree = a.length := by
  induction a with
  | nil => simp [integerCoefficientEval]
  | cons c cs ih =>
    let q : R[X] := X * integerCoefficientEval X (cs ++ [1])
    have hqm : q.Monic := monic_X.mul ih.1
    have hqd : q.natDegree = cs.length + 1 := by
      simp only [q, natDegree_X_mul ih.1.ne_zero, ih.2]
    have hlt : (C (c : R)).degree < q.degree := by
      apply degree_C_le.trans_lt
      rw [degree_eq_natDegree hqm.ne_zero, hqd]
      exact_mod_cast Nat.zero_lt_succ cs.length
    have he : integerCoefficientEval (X : R[X]) ((c :: cs) ++ [1]) = C (c : R) + q := by
      simp only [List.cons_append, integerCoefficientEval]
      rw [map_intCast]
    rw [he]
    exact ⟨hqm.add_of_right hlt, by
      rw [natDegree_add_eq_right_of_degree_lt hlt, hqd, List.length_cons]⟩

end Biunimodular.F11
