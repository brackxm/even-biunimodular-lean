/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomial
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false

namespace Biunimodular.F11

def integerCoefficientEqual (a b : List ℤ) : Bool :=
  (integerCoefficientAdd a (integerCoefficientScale (-1) b)).all (· == 0)

theorem integerCoefficientEval_zero_of_all {R : Type*} [CommRing R]
    (x : R) (a : List ℤ) (h : a.all (· == 0) = true) :
    integerCoefficientEval x a = 0 := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    have hs : a = 0 ∧ as.all (· == 0) = true := by simpa using h
    simp [integerCoefficientEval, hs.1, ih hs.2]

theorem integerCoefficientEval_eq_of_equal {R : Type*} [CommRing R]
    (x : R) (a b : List ℤ) (h : integerCoefficientEqual a b = true) :
    integerCoefficientEval x a = integerCoefficientEval x b := by
  have hz := integerCoefficientEval_zero_of_all x
    (integerCoefficientAdd a (integerCoefficientScale (-1) b)) h
  rw [integerCoefficientEval_add, integerCoefficientEval_scale] at hz
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hz)

def integerCoefficientWeighted (n : ℕ) : List ℤ → List ℤ
  | [] => []
  | a :: as => (n : ℤ) * a :: integerCoefficientWeighted (n + 1) as

def integerCoefficientDerivative : List ℤ → List ℤ
  | [] => []
  | _ :: as => integerCoefficientWeighted 1 as

def integerCoefficientPow (a : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => integerCoefficientMul (integerCoefficientPow a n) a

theorem integerCoefficientEval_pow {R : Type*} [CommRing R]
    (x : R) (a : List ℤ) (n : ℕ) :
    integerCoefficientEval x (integerCoefficientPow a n) =
      integerCoefficientEval x a ^ n := by
  induction n with
  | zero => simp [integerCoefficientPow, integerCoefficientEval]
  | succ n ih => rw [integerCoefficientPow, integerCoefficientEval_mul, ih, pow_succ]

theorem integerCoefficientEval_weighted {R : Type*} [CommRing R]
    (x : R) (a : List ℤ) (n : ℕ) :
    integerCoefficientEval x (integerCoefficientWeighted n a) =
      (n : R) * integerCoefficientEval x a +
        x * integerCoefficientEval x (integerCoefficientDerivative a) := by
  induction a generalizing n with
  | nil => simp [integerCoefficientWeighted, integerCoefficientDerivative, integerCoefficientEval]
  | cons a as ih =>
    simp only [integerCoefficientWeighted, integerCoefficientDerivative,
      integerCoefficientEval, Int.cast_mul, Int.cast_natCast]
    rw [ih (n + 1), ih 1]
    push_cast
    ring

/-- The executable list derivative agrees with the formal polynomial
derivative over every commutative coefficient ring. -/
theorem integerCoefficientPolynomial_derivative {R : Type*} [CommRing R]
    (a : List ℤ) :
    Polynomial.derivative (integerCoefficientEval (Polynomial.X : Polynomial R) a) =
      integerCoefficientEval Polynomial.X (integerCoefficientDerivative a) := by
  induction a with
  | nil => simp [integerCoefficientEval, integerCoefficientDerivative]
  | cons a as ih =>
    rw [integerCoefficientEval, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_X, ih]
    rw [integerCoefficientDerivative, integerCoefficientEval_weighted]
    simp

end Biunimodular.F11
