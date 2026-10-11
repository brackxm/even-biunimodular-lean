/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber5PointData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber5Pointinverse1_check :
    integerCoefficientEqual
      (integerCoefficientAdd (integerCoefficientMul h252Fiber5Pointc1Coeffs h252Fiber5Pointv1Coeffs) [-h252Fiber5PointScale^2])
      (integerCoefficientMul h252FiberCRTQ5 h252Fiber5Pointiq1Coeffs) = true := by native_decide
noncomputable section
theorem h252Fiber5Pointc1_isUnit {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (hq : integerCoefficientEval a h252FiberCRTQ5 = 0) : IsUnit (h252Fiber5Pointc1 a) := by
  apply torusScaledRationalValue_isUnit a h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc1Coeffs h252Fiber5Pointv1Coeffs
  have h := integerCoefficientEval_eq_of_equal a _ _ h252Fiber5Pointinverse1_check
  simp only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton,
    Int.cast_neg, Int.cast_pow, hq, zero_mul] at h
  linear_combination h
end

end Biunimodular.F11
