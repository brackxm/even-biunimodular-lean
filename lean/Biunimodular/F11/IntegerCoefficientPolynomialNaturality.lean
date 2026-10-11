/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Mathlib.Algebra.Polynomial.AlgebraMap

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial

theorem integerCoefficientPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : List ℤ) :
    (integerCoefficientEval (X : R[X]) a).map f = integerCoefficientEval (X : S[X]) a := by
  change (Polynomial.mapRingHom f) (integerCoefficientEval (X : R[X]) a) = _
  rw [integerCoefficientEval_map]
  have hX : (Polynomial.mapRingHom f) (X : R[X]) = (X : S[X]) := Polynomial.map_X f
  rw [hX]

theorem integerCoefficientPolynomial_comp {R : Type*} [CommRing R]
    (a : List ℤ) (q : R[X]) :
    (integerCoefficientEval (X : R[X]) a).comp q = integerCoefficientEval q a := by
  change (Polynomial.aeval q : R[X] →ₐ[R] R[X]).toRingHom
    (integerCoefficientEval (X : R[X]) a) = _
  rw [integerCoefficientEval_map]
  have hX : (Polynomial.aeval q : R[X] →ₐ[R] R[X]).toRingHom X = q := Polynomial.aeval_X q
  rw [hX]

end Biunimodular.F11
