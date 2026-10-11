/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusMacaulayColumnCertificate
import Biunimodular.F11.TorusOriginalGeneratorsData

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- Cleared monomials can be compared with a known point without introducing
negative powers. A common unit factor is cancelled only when recovering the
individual phase coordinates. -/
theorem torusMacaulay_polynomial_values
    {R : Type*} [CommRing R] (n : ℕ)
    (rows columns : Array TorusMacaulayRow)
    (polynomials points : Array (List RurInverseTerm7))
    (constants : Array (List ℤ)) (global : List RurInverseTerm7)
    (parents pointParents : Array (List (List RurInverseTerm7 × List RurInverseTerm7)))
    (z1 z2 z3 z4 w z5 x : R)
    (htranspose : torusMacaulayTransposeCheck n rows columns)
    (hcheck : ∀ j : Fin n, torusMacaulayColumnZeroCheck columns polynomials constants
      global (parents[j.val]?.getD []) j.val)
    (hpointCheck : ∀ j : Fin n, torusMacaulayColumnZeroCheck columns points constants
      rurInverseSparseOne (pointParents[j.val]?.getD []) j.val)
    (hparents : ∀ j : Fin n, ∀ p ∈ parents[j.val]?.getD [],
      rurInverseSparseEval p.2 z1 z2 z3 z4 w z5 x = 0)
    (hpointParents : ∀ j : Fin n, ∀ p ∈ pointParents[j.val]?.getD [],
      rurInverseSparseEval p.2 z1 z2 z3 z4 w z5 x = 0)
    (hdet : IsUnit (torusMacaulaySparseMatrix n rows z5).det) :
    ∀ i : Fin n, rurInverseSparseEval (polynomials[i.val]?.getD []) z1 z2 z3 z4 w z5 x =
      rurInverseSparseEval global z1 z2 z3 z4 w z5 x *
        rurInverseSparseEval (points[i.val]?.getD []) z1 z2 z3 z4 w z5 x := by
  let ev : List RurInverseTerm7 → R := fun p => rurInverseSparseEval p z1 z2 z3 z4 w z5 x
  let values : Fin n → R := fun i => ev (polynomials[i.val]?.getD [])
  let point : Fin n → R := fun i => ev (points[i.val]?.getD [])
  let constant : Fin n → R := fun j => integerCoefficientEval z5 (constants[j.val]?.getD [])
  let m := ev global
  let M := torusMacaulaySparseMatrix n rows z5
  have hvalues : Matrix.vecMul values M + m • constant = 0 := by
    ext j
    change Matrix.vecMul values M j + m * constant j = 0
    rw [torusMacaulay_vecMul_columns n rows columns htranspose z5
      (fun i => ev (polynomials[i]?.getD [])) j]
    have h := torusMacaulayColumnZeroCheck_sound columns polynomials constants global
      (parents[j.val]?.getD []) j.val (hcheck j) z1 z2 z3 z4 w z5 x (hparents j)
    simpa only [ev, m, constant, mul_comm] using h
  have hpoint : Matrix.vecMul point M + constant = 0 := by
    ext j
    change Matrix.vecMul point M j + constant j = 0
    rw [torusMacaulay_vecMul_columns n rows columns htranspose z5
      (fun i => ev (points[i]?.getD [])) j]
    have h := torusMacaulayColumnZeroCheck_sound columns points constants rurInverseSparseOne
      (pointParents[j.val]?.getD []) j.val (hpointCheck j)
      z1 z2 z3 z4 w z5 x (hpointParents j)
    simpa only [ev, constant, rurInverseSparseOne, rurInverseSparseEval,
      rurInverseSparseTermEval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, pow_zero, Int.cast_one, mul_one, add_zero] using h
  have hscaled : Matrix.vecMul (m • point) M + m • constant = 0 := by
    rw [Matrix.smul_vecMul, ← smul_add, hpoint, smul_zero]
  have he := torusMacaulay_values_eq_of_unit_det M hdet values (m • point)
    (m • constant) hvalues hscaled
  intro i
  simpa only [values, point, m, ev, Pi.smul_apply, smul_eq_mul] using congrFun he i

end
end Biunimodular.F11
