/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodOrderData77
import Biunimodular.F11.ASectorPeriodSubfieldValues77
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace Biunimodular.F11
open Polynomial
noncomputable section

/-! Exact Gaussian-period products, checked with integer coefficient arithmetic.
The generic evaluation lemmas link the computation to the actual cyclotomic periods.
-/

theorem periodOrderOrbit_eval77 (i : Fin 6) :
    integerCoefficientEval zeta77 (periodOrderOrbitCoefficients77 i) = periodOrbit77 i := by
  fin_cases i <;>
    norm_num [integerCoefficientEval, periodOrderOrbitCoefficients77, periodOrbit77,
      conductor77PeriodOrbitValue, conductor77PeriodOrbitPolynomials] <;> ring

theorem periodOrderPhi_eval77 :
    integerCoefficientEval zeta77 periodOrderPhiCoefficients77 = 0 := by
  have h : integerCoefficientEval zeta77 periodOrderPhiCoefficients77 =
      Polynomial.eval₂ (Int.castRingHom Conductor77Cyclotomic) zeta77 phi77 := by
    norm_num [integerCoefficientEval, periodOrderPhiCoefficients77, phi77]
    ring
  rw [h, phi77_eq_cyclotomic]
  exact zeta77_cyclotomic_root

theorem periodOrbit77_mul (i j : Fin 6) :
    periodOrbit77 i * periodOrbit77 j =
      ∑ k : Fin 6, (periodOrderProductCoefficients77 i j k : Conductor77Cyclotomic) *
        periodOrbit77 k := by
  have h := congrArg (integerCoefficientEval zeta77)
    (periodOrderProduct_coefficient_identity77 i j)
  simp only [integerCoefficientEval_mul, integerCoefficientEval_add,
    periodOrderOrbit_eval77, periodOrderPhi_eval77, zero_mul, add_zero] at h
  rw [h]
  simp only [periodOrderCombinationCoefficients77, integerCoefficientEval_sum,
    List.map_ofFn, Function.comp_apply, integerCoefficientEval_scale,
    periodOrderOrbit_eval77, List.sum_ofFn]

def periodOrderTraceGramData77 : Matrix (Fin 6) (Fin 6) ℤ :=
  ![![41, -1, -1, -36, -1, -1], ![-1, 41, -1, -1, -36, -1], ![-1, -1, 41, -1, -1, -36], ![-36, -1, -1, 41, -1, -1], ![-1, -36, -1, -1, 41, -1], ![-1, -1, -36, -1, -1, 41]]

theorem periodOrderTraceGramData77_det :
    Matrix.det periodOrderTraceGramData77 = 7^5 * 11^3 := by
  native_decide

end
end Biunimodular.F11
