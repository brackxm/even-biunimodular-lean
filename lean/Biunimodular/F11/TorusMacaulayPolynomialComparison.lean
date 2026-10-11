/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusMacaulayPolynomialCriterion

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- The checked cleared Laurent columns give a linear matrix equation at
any solution of their parent equations. -/
theorem torusMacaulay_polynomial_equation
    {R : Type*} [CommRing R] (n : ℕ)
    (rows columns : Array TorusMacaulayRow)
    (polynomials : Array (List RurInverseTerm7))
    (constants : Array (List ℤ)) (global : List RurInverseTerm7)
    (parents : Array (List (List RurInverseTerm7 × List RurInverseTerm7)))
    (z1 z2 z3 z4 w a x : R)
    (htranspose : torusMacaulayTransposeCheck n rows columns)
    (hcheck : ∀ j : Fin n, torusMacaulayColumnZeroCheck columns polynomials constants
      global (parents[j.val]?.getD []) j.val)
    (hparents : ∀ j : Fin n, ∀ p ∈ parents[j.val]?.getD [],
      rurInverseSparseEval p.2 z1 z2 z3 z4 w a x = 0) :
    Matrix.vecMul (fun i : Fin n =>
      rurInverseSparseEval (polynomials[i.val]?.getD []) z1 z2 z3 z4 w a x)
      (torusMacaulaySparseMatrix n rows a) +
    rurInverseSparseEval global z1 z2 z3 z4 w a x •
      (fun j : Fin n => integerCoefficientEval a (constants[j.val]?.getD [])) = 0 := by
  ext j
  change Matrix.vecMul (fun i : Fin n =>
    rurInverseSparseEval (polynomials[i.val]?.getD []) z1 z2 z3 z4 w a x)
    (torusMacaulaySparseMatrix n rows a) j +
    rurInverseSparseEval global z1 z2 z3 z4 w a x *
      integerCoefficientEval a (constants[j.val]?.getD []) = 0
  rw [torusMacaulay_vecMul_columns n rows columns htranspose a
    (fun i => rurInverseSparseEval (polynomials[i]?.getD []) z1 z2 z3 z4 w a x) j]
  have h := torusMacaulayColumnZeroCheck_sound columns polynomials constants global
    (parents[j.val]?.getD []) j.val (hcheck j) z1 z2 z3 z4 w a x (hparents j)
  simpa only [mul_comm] using h

/-- An invertible coefficient matrix compares any two solutions over an
arbitrary ring, including rings with nilpotents. -/
theorem torusMacaulay_polynomial_compare
    {R : Type*} [CommRing R] (n : ℕ)
    (rows columns : Array TorusMacaulayRow)
    (polynomials : Array (List RurInverseTerm7))
    (constants : Array (List ℤ)) (global : List RurInverseTerm7)
    (parents : Array (List (List RurInverseTerm7 × List RurInverseTerm7)))
    (z1 z2 z3 z4 w c1 c2 c3 c4 v a x : R)
    (htranspose : torusMacaulayTransposeCheck n rows columns)
    (hcheck : ∀ j : Fin n, torusMacaulayColumnZeroCheck columns polynomials constants
      global (parents[j.val]?.getD []) j.val)
    (hparents : ∀ j : Fin n, ∀ p ∈ parents[j.val]?.getD [],
      rurInverseSparseEval p.2 z1 z2 z3 z4 w a x = 0)
    (hcparents : ∀ j : Fin n, ∀ p ∈ parents[j.val]?.getD [],
      rurInverseSparseEval p.2 c1 c2 c3 c4 v a x = 0)
    (hdet : IsUnit (torusMacaulaySparseMatrix n rows a).det) :
    ∀ i : Fin n,
      rurInverseSparseEval global c1 c2 c3 c4 v a x *
        rurInverseSparseEval (polynomials[i.val]?.getD []) z1 z2 z3 z4 w a x =
      rurInverseSparseEval global z1 z2 z3 z4 w a x *
        rurInverseSparseEval (polynomials[i.val]?.getD []) c1 c2 c3 c4 v a x := by
  let ev := fun p => rurInverseSparseEval p z1 z2 z3 z4 w a x
  let cev := fun p => rurInverseSparseEval p c1 c2 c3 c4 v a x
  let values : Fin n → R := fun i => ev (polynomials[i.val]?.getD [])
  let point : Fin n → R := fun i => cev (polynomials[i.val]?.getD [])
  let constant : Fin n → R := fun j => integerCoefficientEval a (constants[j.val]?.getD [])
  let m := ev global
  let cm := cev global
  let M := torusMacaulaySparseMatrix n rows a
  have hvalues : Matrix.vecMul values M + m • constant = 0 :=
    torusMacaulay_polynomial_equation n rows columns polynomials constants global
      parents z1 z2 z3 z4 w a x htranspose hcheck hparents
  have hpoint : Matrix.vecMul point M + cm • constant = 0 :=
    torusMacaulay_polynomial_equation n rows columns polynomials constants global
      parents c1 c2 c3 c4 v a x htranspose hcheck hcparents
  have hv : Matrix.vecMul (cm • values) M + (cm*m) • constant = 0 := by
    rw [Matrix.smul_vecMul, mul_smul, ← smul_add, hvalues, smul_zero]
  have hp : Matrix.vecMul (m • point) M + (cm*m) • constant = 0 := by
    rw [mul_comm cm m, Matrix.smul_vecMul, mul_smul, ← smul_add, hpoint, smul_zero]
  have he := torusMacaulay_values_eq_of_unit_det M hdet (cm • values) (m • point)
    ((cm*m) • constant) hv hp
  intro i
  simpa only [ev, cev, values, point, m, cm, Pi.smul_apply, smul_eq_mul] using congrFun he i

end
end Biunimodular.F11
