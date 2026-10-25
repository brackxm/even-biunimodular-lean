/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.Tactic.NormDet
public import Mathlib.Tactic.NormMatMul
public import Mathlib.Tactic.NormRank
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Certified conductor-77 trace pairing

The trace matrix and its scaled inverse are finite integer data. Reflected
matrix arithmetic verifies their product, rank and determinant independently
of the cyclotomic-field development and without native evaluation axioms.
-/

@[expose] public section

namespace Biunimodular.F11

def periodOrderTraceGramData77 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![41, -1, -1, -36, -1, -1;
     -1, 41, -1, -1, -36, -1;
     -1, -1, 41, -1, -1, -36;
     -36, -1, -1, 41, -1, -1;
     -1, -36, -1, -1, 41, -1;
     -1, -1, -36, -1, -1, 41]

/-- An integral scaled inverse for the conductor-77 trace pairing. -/
def periodOrderTraceDualData77 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![17, 11, 11, 16, 11, 11;
     11, 17, 11, 11, 16, 11;
     11, 11, 17, 11, 11, 16;
     16, 11, 11, 17, 11, 11;
     11, 16, 11, 11, 17, 11;
     11, 11, 16, 11, 11, 17]

/-- The multiplication certificate is checked by reflected matrix arithmetic. -/
theorem periodOrderTraceGramData77_mul_dual :
    periodOrderTraceGramData77 * periodOrderTraceDualData77 = 77 := by
  simp only [periodOrderTraceGramData77, periodOrderTraceDualData77, norm_matmul]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.ofNat_apply]

theorem periodOrderTraceGramData77_rank : periodOrderTraceGramData77.rank = 6 := by
  unfold periodOrderTraceGramData77
  eval_rank

theorem periodOrderTraceGramData77_det :
    Matrix.det periodOrderTraceGramData77 = 7^5 * 11^3 := by
  simp only [periodOrderTraceGramData77, norm_det]
  norm_num

end Biunimodular.F11
