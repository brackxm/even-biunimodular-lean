/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Biunimodular.F11

/-- Integer coefficient arithmetic, independent of noncomputable polynomial instances. -/
def integerCoefficientAdd : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: integerCoefficientAdd as bs

def integerCoefficientScale (c : ℤ) (a : List ℤ) : List ℤ := a.map (c * ·)

def integerCoefficientMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => integerCoefficientAdd (integerCoefficientScale a b)
      (0 :: integerCoefficientMul as b)

def integerCoefficientEval {R : Type*} [CommRing R] (x : R) : List ℤ → R
  | [] => 0
  | a :: as => (a : R) + x * integerCoefficientEval x as

theorem integerCoefficientEval_add {R : Type*} [CommRing R] (x : R) (a b : List ℤ) :
    integerCoefficientEval x (integerCoefficientAdd a b) =
      integerCoefficientEval x a + integerCoefficientEval x b := by
  induction a generalizing b with
  | nil => simp [integerCoefficientAdd, integerCoefficientEval]
  | cons a as ih =>
    cases b with
    | nil => simp [integerCoefficientAdd, integerCoefficientEval]
    | cons b bs =>
      simp only [integerCoefficientAdd, integerCoefficientEval, Int.cast_add, ih]
      ring

theorem integerCoefficientEval_scale {R : Type*} [CommRing R]
    (x : R) (c : ℤ) (a : List ℤ) :
    integerCoefficientEval x (integerCoefficientScale c a) =
      (c : R) * integerCoefficientEval x a := by
  induction a with
  | nil => simp [integerCoefficientScale, integerCoefficientEval]
  | cons a as ih =>
    simp only [integerCoefficientScale, List.map_cons, integerCoefficientEval, Int.cast_mul]
    change (c : R) * (a : R) + x * integerCoefficientEval x (integerCoefficientScale c as) = _
    rw [ih]
    ring

theorem integerCoefficientEval_mul {R : Type*} [CommRing R] (x : R) (a b : List ℤ) :
    integerCoefficientEval x (integerCoefficientMul a b) =
      integerCoefficientEval x a * integerCoefficientEval x b := by
  induction a with
  | nil => simp [integerCoefficientMul, integerCoefficientEval]
  | cons a as ih =>
    rw [integerCoefficientMul, integerCoefficientEval_add, integerCoefficientEval_scale]
    simp only [integerCoefficientEval, Int.cast_zero, zero_add, ih]
    ring

theorem integerCoefficientEval_sum {R : Type*} [CommRing R]
    (x : R) (a : List (List ℤ)) :
    integerCoefficientEval x (a.foldr integerCoefficientAdd []) =
      (a.map (integerCoefficientEval x)).sum := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldr_cons, integerCoefficientEval_add, ih,
      List.map_cons, List.sum_cons]

end Biunimodular.F11
