/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomial
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.CoeffList

set_option autoImplicit false

namespace Biunimodular.F11

theorem integerCoefficientEval_nil {R : Type*} [CommRing R] (x : R) :
    integerCoefficientEval x [] = 0 := rfl

theorem integerCoefficientEval_singleton {R : Type*} [CommRing R] (x : R) (a : ℤ) :
    integerCoefficientEval x [a] = a := by simp [integerCoefficientEval]

theorem integerCoefficientEval_variable {R : Type*} [CommRing R] (x : R) :
    integerCoefficientEval x [0, 1] = x := by simp [integerCoefficientEval]

theorem integerCoefficientEval_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) (a : List ℤ) :
    f (integerCoefficientEval x a) = integerCoefficientEval (f x) a := by
  induction a with
  | nil => simp [integerCoefficientEval]
  | cons a as ih => simp [integerCoefficientEval, ih]

/-- Mathlib's coefficient-list semantics agree with the executable integer
Horner evaluator over every commutative coefficient ring. -/
theorem integerCoefficientPolynomial_eq_ofCoeffList {R : Type*} [CommRing R]
    (a : List ℤ) :
    integerCoefficientEval (Polynomial.X : Polynomial R) a =
      Polynomial.ofCoeffList (a.map (Int.castRingHom R)) := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp [integerCoefficientEval, Polynomial.ofCoeffList, ih]

@[simp] theorem integerCoefficientPolynomial_coeff {R : Type*} [CommRing R]
    (a : List ℤ) (i : ℕ) :
    (integerCoefficientEval (Polynomial.X : Polynomial R) a).coeff i = (a.getD i 0 : R) := by
  rw [integerCoefficientPolynomial_eq_ofCoeffList, Polynomial.coeff_ofCoeffList]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a[i]? <;> simp

theorem integerCoefficientPolynomial_eval {R : Type*} [CommRing R]
    (x : R) (a : List ℤ) :
    (integerCoefficientEval (Polynomial.X : Polynomial R) a).eval x =
      integerCoefficientEval x a := by
  simpa using integerCoefficientEval_map (Polynomial.evalRingHom x) Polynomial.X a

end Biunimodular.F11
