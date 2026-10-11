/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomial
import Mathlib.Algebra.Polynomial.Eval.SMul

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

theorem integerCoefficientPolynomial_eval {R : Type*} [CommRing R]
    (x : R) (a : List ℤ) :
    (integerCoefficientEval (Polynomial.X : Polynomial R) a).eval x =
      integerCoefficientEval x a := by
  simpa using integerCoefficientEval_map (Polynomial.evalRingHom x) Polynomial.X a

end Biunimodular.F11
