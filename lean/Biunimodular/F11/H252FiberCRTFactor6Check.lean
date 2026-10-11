/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FiberCRTFactor6Data
import Biunimodular.F11.H252TorusCertificateData11

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
theorem h252FiberCRTannihilator6_check : integerCoefficientZeroCheck
    (integerCoefficientAdd (integerCoefficientMul h252FiberCRTE6 h252FiberCRTQ6)
      (integerCoefficientScale (-1) (integerCoefficientMul h252TorusEliminantCoeffs11 h252FiberCRTA6))) = true := by native_decide

theorem h252FiberCRTannihilator6 {R : Type*} [CommRing R] (z : R) :
    integerCoefficientEval z h252FiberCRTE6 * integerCoefficientEval z h252FiberCRTQ6 =
      integerCoefficientEval z h252TorusEliminantCoeffs11 * integerCoefficientEval z h252FiberCRTA6 := by
  have h := integerCoefficientZeroCheck_sound _ h252FiberCRTannihilator6_check z
  rw [integerCoefficientEval_add, integerCoefficientEval_mul,
    integerCoefficientEval_scale, integerCoefficientEval_mul] at h
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

end Biunimodular.F11
