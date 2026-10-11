/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FiberCRTFactor7Data
import Biunimodular.F11.H252TorusCertificateData11

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
theorem h252FiberCRTannihilator7_check : integerCoefficientZeroCheck
    (integerCoefficientAdd (integerCoefficientMul h252FiberCRTE7 h252FiberCRTQ7)
      (integerCoefficientScale (-1) (integerCoefficientMul h252TorusEliminantCoeffs11 h252FiberCRTA7))) = true := by native_decide

theorem h252FiberCRTannihilator7 {R : Type*} [CommRing R] (z : R) :
    integerCoefficientEval z h252FiberCRTE7 * integerCoefficientEval z h252FiberCRTQ7 =
      integerCoefficientEval z h252TorusEliminantCoeffs11 * integerCoefficientEval z h252FiberCRTA7 := by
  have h := integerCoefficientZeroCheck_sound _ h252FiberCRTannihilator7_check z
  rw [integerCoefficientEval_add, integerCoefficientEval_mul,
    integerCoefficientEval_scale, integerCoefficientEval_mul] at h
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

end Biunimodular.F11
