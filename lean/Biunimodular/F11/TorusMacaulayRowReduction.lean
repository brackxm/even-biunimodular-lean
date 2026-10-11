/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusMacaulaySparseMatrix

set_option autoImplicit false
namespace Biunimodular.F11

def torusMacaulayEvaluatedRow {R : Type*} [CommRing R]
    (a : R) (row : TorusMacaulayRow) : List (ℕ × R) :=
  row.map fun e => (e.1, integerCoefficientEval a e.2)

/-- Checking row evaluation once suffices to transfer a modular inverse
from a constant-entry matrix to the original polynomial matrix. -/
theorem torusMacaulaySparseMatrix_eq_of_evaluated_rows
    {R : Type*} [CommRing R] (n : ℕ) (a : R)
    (rows reduced : Array TorusMacaulayRow)
    (h : ∀ i : Fin n,
      torusMacaulayEvaluatedRow a (rows[i.val]?.getD []) =
        torusMacaulayEvaluatedRow a (reduced[i.val]?.getD [])) :
    torusMacaulaySparseMatrix n rows a = torusMacaulaySparseMatrix n reduced a := by
  ext i j
  have he := congrArg (fun r : List (ℕ × R) =>
    (r.map fun e => if e.1 = j.val then e.2 else 0).sum) (h i)
  simpa only [torusMacaulayEvaluatedRow, List.map_map, Function.comp_def,
    torusMacaulaySparseMatrix] using he

end Biunimodular.F11
