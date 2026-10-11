/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FiberCRTFactor1Data
import Biunimodular.F11.H252FiberCRTFactor2Data
import Biunimodular.F11.H252FiberCRTFactor3Data
import Biunimodular.F11.H252FiberCRTFactor4Data
import Biunimodular.F11.H252FiberCRTFactor5Data
import Biunimodular.F11.H252FiberCRTFactor6Data
import Biunimodular.F11.H252FiberCRTFactor7Data

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
theorem h252FiberCRTpartition_check : integerCoefficientZeroCheck
    (integerCoefficientAdd ([h252FiberCRTE1, h252FiberCRTE2, h252FiberCRTE3, h252FiberCRTE4, h252FiberCRTE5, h252FiberCRTE6, h252FiberCRTE7].foldr integerCoefficientAdd [])
      [-h252FiberCRTScale]) = true := by native_decide

theorem h252FiberCRTpartition {R : Type*} [CommRing R] (z : R) :
    ([h252FiberCRTE1, h252FiberCRTE2, h252FiberCRTE3, h252FiberCRTE4, h252FiberCRTE5, h252FiberCRTE6, h252FiberCRTE7].map (integerCoefficientEval z)).sum = (h252FiberCRTScale : R) := by
  have h := integerCoefficientZeroCheck_sound _ h252FiberCRTpartition_check z
  rw [integerCoefficientEval_add, integerCoefficientEval_sum] at h
  simp only [integerCoefficientEval, Int.cast_neg, mul_zero, add_zero] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

end Biunimodular.F11
