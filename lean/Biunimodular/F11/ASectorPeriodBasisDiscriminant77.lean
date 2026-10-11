/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodBasis77
import Mathlib.RingTheory.Discriminant

set_option autoImplicit false

namespace Biunimodular.F11
noncomputable section

theorem periodFieldOrbit77_mul (i j : Fin 6) :
    periodFieldOrbit77 i * periodFieldOrbit77 j =
      ∑ k : Fin 6, (periodOrderProductCoefficients77 i j k : ℚ) • periodFieldOrbit77 k := by
  apply Subtype.ext
  simpa [periodFieldOrbit77, Algebra.smul_def] using periodOrbit77_mul i j

/-- Multiplication matrices in the actual period basis have the certified integer entries. -/
theorem conductor77PeriodBasis_leftMulMatrix (i : Fin 6) :
    Algebra.leftMulMatrix conductor77PeriodBasis (periodFieldOrbit77 i) =
      fun k j => (periodOrderProductCoefficients77 i j k : ℚ) := by
  ext k j
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', conductor77PeriodBasis_apply]
  rw [periodFieldOrbit77_mul]
  have h := conductor77PeriodBasis.repr_sum_self
    (fun k => (periodOrderProductCoefficients77 i j k : ℚ))
  simpa only [conductor77PeriodBasis_apply] using congrFun h k

theorem periodFieldOrbit77_trace (i : Fin 6) :
    Algebra.trace ℚ conductor77PeriodField (periodFieldOrbit77 i) = 1 := by
  rw [Algebra.trace_eq_matrix_trace conductor77PeriodBasis,
    conductor77PeriodBasis_leftMulMatrix]
  fin_cases i <;> norm_num [Matrix.trace, Matrix.diag,
    periodOrderProductCoefficients77, Fin.sum_univ_succ]

/-- The candidate numeric Gram data is the trace matrix of the actual period basis. -/
theorem conductor77PeriodBasis_traceMatrix :
    Algebra.traceMatrix ℚ conductor77PeriodBasis =
      periodOrderTraceGramData77.map (Int.castRingHom ℚ) := by
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    conductor77PeriodBasis_apply, periodFieldOrbit77_mul, map_sum, map_smul,
    periodFieldOrbit77_trace, smul_eq_mul, mul_one, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [periodOrderProductCoefficients77, periodOrderTraceGramData77,
      Fin.sum_univ_succ]

/-- Discriminant of the actual rational period basis. Maximality of its integer
span is a separate requirement for identifying the number-field discriminant. -/
theorem conductor77PeriodBasis_discr :
    Algebra.discr ℚ conductor77PeriodBasis = 7^5 * 11^3 := by
  rw [Algebra.discr_def, conductor77PeriodBasis_traceMatrix]
  have h := (Int.castRingHom ℚ).map_det periodOrderTraceGramData77
  rw [periodOrderTraceGramData77_det] at h
  convert h.symm using 1 <;> norm_num

end
end Biunimodular.F11
