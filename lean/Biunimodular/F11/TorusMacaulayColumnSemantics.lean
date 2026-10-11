/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusMacaulaySparseMatrix
import Biunimodular.F11.TorusSparseZ5

set_option autoImplicit false
namespace Biunimodular.F11

def torusMacaulayRowCoefficients : TorusMacaulayRow → ℕ → List ℤ
  | [], _ => []
  | e :: row, j => integerCoefficientAdd (if e.1 = j then e.2 else [])
      (torusMacaulayRowCoefficients row j)

theorem torusMacaulayRowCoefficients_eval
    {R : Type*} [CommRing R] (x : R) (row : TorusMacaulayRow) (j : ℕ) :
    integerCoefficientEval x (torusMacaulayRowCoefficients row j) =
      (row.map fun e => if e.1 = j then integerCoefficientEval x e.2 else 0).sum := by
  induction row with
  | nil => rfl
  | cons e row ih =>
    by_cases he : e.1 = j <;>
      simp [torusMacaulayRowCoefficients, he, integerCoefficientEval_add,
        integerCoefficientEval_nil, ih]

def torusMacaulayTransposeCheck (n : ℕ) (rows columns : Array TorusMacaulayRow) : Prop :=
  (∀ j : Fin n, ∀ e ∈ columns[j.val]?.getD [], e.1 < n) ∧
  ∀ i j : Fin n, torusMacaulayRowCoefficients (rows[i.val]?.getD []) j.val =
    torusMacaulayRowCoefficients (columns[j.val]?.getD []) i.val

instance (n : ℕ) (rows columns : Array TorusMacaulayRow) :
    Decidable (torusMacaulayTransposeCheck n rows columns) := by
  unfold torusMacaulayTransposeCheck
  infer_instance

theorem torusMacaulay_vecMul_columns
    {R : Type*} [CommRing R] (n : ℕ) (rows columns : Array TorusMacaulayRow)
    (h : torusMacaulayTransposeCheck n rows columns) (x : R) (v : ℕ → R) (j : Fin n) :
    Matrix.vecMul (fun i : Fin n => v i.val) (torusMacaulaySparseMatrix n rows x) j =
      ((columns[j.val]?.getD []).map fun e => integerCoefficientEval x e.2 * v e.1).sum := by
  have he (i : Fin n) : torusMacaulaySparseMatrix n rows x i j =
      ((columns[j.val]?.getD []).map fun e =>
        if e.1 = i.val then integerCoefficientEval x e.2 else 0).sum := by
    change ((rows[i.val]?.getD []).map fun e =>
      if e.1 = j.val then integerCoefficientEval x e.2 else 0).sum = _
    rw [← torusMacaulayRowCoefficients_eval, h.2 i j, torusMacaulayRowCoefficients_eval]
  change (∑ i : Fin n, v i.val * torusMacaulaySparseMatrix n rows x i j) = _
  have hc : (∑ i : Fin n, v i.val * torusMacaulaySparseMatrix n rows x i j) =
      ∑ i : Fin n, torusMacaulaySparseMatrix n rows x i j * v i.val := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hc]
  simp_rw [he]
  exact torusMacaulay_sparse_row_dot n _ (h.1 j) x v

end Biunimodular.F11
