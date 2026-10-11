/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FiberCRT
import Biunimodular.F11.H252LocalizedZ5Coordinate
import Biunimodular.F11.AlgebraProjectionIdeal

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

def h252FiberProjectionCoeffs : Fin 7 → List ℤ :=
  ![h252FiberCRTE1, h252FiberCRTE2, h252FiberCRTE3, h252FiberCRTE4,
    h252FiberCRTE5, h252FiberCRTE6, h252FiberCRTE7]

def h252FiberFactorCoeffs : Fin 7 → List ℤ :=
  ![h252FiberCRTQ1, h252FiberCRTQ2, h252FiberCRTQ3, h252FiberCRTQ4,
    h252FiberCRTQ5, h252FiberCRTQ6, h252FiberCRTQ7]

def h252FiberProjection (i : Fin 7) : H252LocalizedTorusAlgebra :=
  integerCoefficientEval (h252LocalizedTorusVar 4) (h252FiberProjectionCoeffs i)

def h252FiberProjectionIdeal (i : Fin 7) : Ideal H252LocalizedTorusPolynomialRing :=
  algebraProjectionIdeal (Ideal.Quotient.mk h252LocalizedTorusIdeal) (h252FiberProjection i)

theorem h252LocalizedZ5_eliminant_eval_zero :
    integerCoefficientEval (h252LocalizedTorusVar 4) h252TorusEliminantCoeffs11 = 0 := by
  have h := h252LocalizedZ5Coordinate_eliminant_zero
  change (Polynomial.aeval (h252LocalizedTorusVar 4) :
    Polynomial ℂ →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom
      (integerCoefficientEval Polynomial.X h252TorusEliminantCoeffs11) = 0 at h
  rw [integerCoefficientEval_map] at h
  have hX : (Polynomial.aeval (h252LocalizedTorusVar 4) :
      Polynomial ℂ →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom Polynomial.X =
      h252LocalizedTorusVar 4 := Polynomial.aeval_X _
  simpa only [hX] using h

theorem h252FiberProjection_annihilator (i : Fin 7) :
    h252FiberProjection i *
      integerCoefficientEval (h252LocalizedTorusVar 4) (h252FiberFactorCoeffs i) = 0 := by
  fin_cases i
  · change integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTE1 *
      integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ1 = 0
    rw [h252FiberCRTannihilator1, h252LocalizedZ5_eliminant_eval_zero, zero_mul]
  · change integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTE2 *
      integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ2 = 0
    rw [h252FiberCRTannihilator2, h252LocalizedZ5_eliminant_eval_zero, zero_mul]
  · change integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTE3 *
      integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ3 = 0
    rw [h252FiberCRTannihilator3, h252LocalizedZ5_eliminant_eval_zero, zero_mul]
  · change integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTE4 *
      integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ4 = 0
    rw [h252FiberCRTannihilator4, h252LocalizedZ5_eliminant_eval_zero, zero_mul]
  · change integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTE5 *
      integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ5 = 0
    rw [h252FiberCRTannihilator5, h252LocalizedZ5_eliminant_eval_zero, zero_mul]
  · change integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTE6 *
      integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ6 = 0
    rw [h252FiberCRTannihilator6, h252LocalizedZ5_eliminant_eval_zero, zero_mul]
  · change integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTE7 *
      integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ7 = 0
    rw [h252FiberCRTannihilator7, h252LocalizedZ5_eliminant_eval_zero, zero_mul]

theorem h252FiberProjection_partition :
    ∑ i, h252FiberProjection i = (h252FiberCRTScale : H252LocalizedTorusAlgebra) := by
  simpa [h252FiberProjection, h252FiberProjectionCoeffs, Fin.sum_univ_succ,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_assoc] using
    h252FiberCRTpartition (h252LocalizedTorusVar 4)

end
end Biunimodular.F11
