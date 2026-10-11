/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252TorusCertificateData11
import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Mathlib.Algebra.MvPolynomial.Funext

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial
noncomputable section

theorem h252EvalCoefficientsC_eq_integer (a : List ℤ) (x : ℂ) :
    h252EvalCoefficientsC a x = integerCoefficientEval x a := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [h252EvalCoefficientsC, integerCoefficientEval, ih]

def h252SparseUniversalEval {R : Type*} [CommRing R]
    (terms : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : R) : R :=
  (terms.map fun t ↦ (t.coefficient : R) * z1 ^ t.exponent.z1 *
    z2 ^ t.exponent.z2 * z3 ^ t.exponent.z3 * z4 ^ t.exponent.z4 *
    w ^ t.exponent.w * z5 ^ t.exponent.z5).sum

theorem h252SparseUniversalEval_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (terms : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : R) :
    f (h252SparseUniversalEval terms z1 z2 z3 z4 w z5) =
      h252SparseUniversalEval terms (f z1) (f z2) (f z3) (f z4) (f w) (f z5) := by
  simp [h252SparseUniversalEval, map_list_sum, List.map_map, Function.comp_def]

theorem h252SparseUniversalEval_complex (terms : List H252SparseTerm6)
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseUniversalEval terms z1 z2 z3 z4 w z5 =
      h252SparseEval11 terms z1 z2 z3 z4 w z5 := rfl

def h252UniversalTorusIdentityLeft {R : Type*} [CommRing R]
    (z1 z2 z3 z4 _w z5 : R) : R :=
  h252TorusD z1 z2 z3 z4 z5 * integerCoefficientEval z5 h252TorusEliminantCoeffs11

def h252UniversalTorusIdentityRight {R : Type*} [CommRing R]
    (z1 z2 z3 z4 w z5 : R) : R :=
  h252SparseUniversalEval h252TorusMultiplier1Sparse11 z1 z2 z3 z4 w z5 *
      h252TorusF1 z1 z2 z3 z4 z5 +
    (h252SparseUniversalEval h252TorusMultiplier2Sparse11 z1 z2 z3 z4 w z5 *
      h252TorusF2 z1 z2 z3 z4 z5 +
    (h252SparseUniversalEval h252TorusMultiplier3Sparse11 z1 z2 z3 z4 w z5 *
      h252TorusF3 z1 z2 z3 z4 z5 +
    (h252SparseUniversalEval h252TorusMultiplier4Sparse11 z1 z2 z3 z4 w z5 *
      h252TorusF4 z1 z2 z3 z4 z5 +
     h252SparseUniversalEval h252TorusMultiplier5Sparse11 z1 z2 z3 z4 w z5 *
      h252TorusF5 z1 z2 z3 z4 z5)))

theorem h252UniversalTorusIdentityLeft_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z1 z2 z3 z4 w z5 : R) :
    f (h252UniversalTorusIdentityLeft z1 z2 z3 z4 w z5) =
      h252UniversalTorusIdentityLeft (f z1) (f z2) (f z3) (f z4) (f w) (f z5) := by
  simp only [h252UniversalTorusIdentityLeft, h252TorusD, map_mul, integerCoefficientEval_map]

theorem h252UniversalTorusIdentityRight_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z1 z2 z3 z4 w z5 : R) :
    f (h252UniversalTorusIdentityRight z1 z2 z3 z4 w z5) =
      h252UniversalTorusIdentityRight (f z1) (f z2) (f z3) (f z4) (f w) (f z5) := by
  simp only [h252UniversalTorusIdentityRight, map_add, map_mul,
    h252SparseUniversalEval_map, h252TorusF1, h252TorusF2, h252TorusF3,
    h252TorusF4, h252TorusF5, map_pow]

/-- The original checked saturated identity holds in every complex algebra,
including the actual quotient coordinate ring. Equality of polynomial
functions over the infinite field converts the existing certificate to a
polynomial identity before specializing to that algebra. -/
theorem h252UniversalTorusIdentity {R : Type*} [CommRing R] [Algebra ℂ R]
    (z1 z2 z3 z4 w z5 : R) :
    h252UniversalTorusIdentityLeft z1 z2 z3 z4 w z5 =
      h252UniversalTorusIdentityRight z1 z2 z3 z4 w z5 := by
  let v : Fin 6 → MvPolynomial (Fin 6) ℂ := MvPolynomial.X
  have hpoly : h252UniversalTorusIdentityLeft (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) =
      h252UniversalTorusIdentityRight (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
    apply MvPolynomial.funext
    intro a
    rw [h252UniversalTorusIdentityLeft_map, h252UniversalTorusIdentityRight_map]
    simp only [v, MvPolynomial.eval_X]
    have h := h252TorusEliminant_saturated_identity11 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)
    simpa only [h252UniversalTorusIdentityLeft, h252UniversalTorusIdentityRight,
      h252SparseUniversalEval_complex, h252TorusEliminantEval11,
      h252EvalCoefficientsC_eq_integer, h252TorusMultiplier1Eval11,
      h252TorusMultiplier2Eval11, h252TorusMultiplier3Eval11,
      h252TorusMultiplier4Eval11, h252TorusMultiplier5Eval11] using h
  let a : Fin 6 → R := ![z1, z2, z3, z4, w, z5]
  have h := congrArg (MvPolynomial.aeval a) hpoly
  change (MvPolynomial.aeval a).toRingHom _ = (MvPolynomial.aeval a).toRingHom _ at h
  rw [h252UniversalTorusIdentityLeft_map, h252UniversalTorusIdentityRight_map] at h
  simpa [v, a] using h

theorem h252UniversalCircleFactor {R : Type*} [CommRing R] [Algebra ℂ R] (z : R) :
    integerCoefficientEval z h252TorusEliminantCoeffs11 *
        integerCoefficientEval z h252CircleQuotientCoeffs11 =
      integerCoefficientEval z h252CircleLiftCoeffs11 := by
  have hpoly :
      integerCoefficientEval (Polynomial.X : ℂ[X]) h252TorusEliminantCoeffs11 *
          integerCoefficientEval Polynomial.X h252CircleQuotientCoeffs11 =
        integerCoefficientEval Polynomial.X h252CircleLiftCoeffs11 := by
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_mul, integerCoefficientPolynomial_eval]
    have h := h252TorusEliminant_circleFactor11 x
    simpa only [h252TorusEliminantEval11, h252CircleQuotientEval11,
      h252CircleLiftEval11, h252EvalCoefficientsC_eq_integer, one_mul] using h
  have h := congrArg (Polynomial.aeval z) hpoly
  change (Polynomial.aeval z).toRingHom _ = (Polynomial.aeval z).toRingHom _ at h
  have hX : (Polynomial.aeval z : ℂ[X] →ₐ[ℂ] R).toRingHom
      (Polynomial.X : ℂ[X]) = z := Polynomial.aeval_X z
  simpa only [map_mul, integerCoefficientEval_map, hX] using h

end

end Biunimodular.F11
