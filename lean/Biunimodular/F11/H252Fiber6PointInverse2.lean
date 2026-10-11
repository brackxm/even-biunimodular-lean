/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6PointData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber6Pointinverse2_check :
    integerCoefficientEqual
      (integerCoefficientAdd (integerCoefficientMul h252Fiber6Pointc2Coeffs h252Fiber6Pointv2Coeffs) [-h252Fiber6PointScale^2])
      (integerCoefficientMul h252FiberCRTQ6 h252Fiber6Pointiq2Coeffs) = true := by native_decide
noncomputable section
theorem h252Fiber6Pointc2_isUnit {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (hq : integerCoefficientEval a h252FiberCRTQ6 = 0) : IsUnit (h252Fiber6Pointc2 a) := by
  apply torusScaledRationalValue_isUnit a h252Fiber6PointScale (ne_of_gt h252Fiber6PointScale_pos) h252Fiber6Pointc2Coeffs h252Fiber6Pointv2Coeffs
  have h := integerCoefficientEval_eq_of_equal a _ _ h252Fiber6Pointinverse2_check
  simp only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton,
    Int.cast_neg, Int.cast_pow, hq, zero_mul] at h
  linear_combination h
end

end Biunimodular.F11
