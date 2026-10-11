/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3PointData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber3Pointinverse3_check :
    integerCoefficientEqual
      (integerCoefficientAdd (integerCoefficientMul h252Fiber3Pointc3Coeffs h252Fiber3Pointv3Coeffs) [-h252Fiber3PointScale^2])
      (integerCoefficientMul h252FiberCRTQ3 h252Fiber3Pointiq3Coeffs) = true := by native_decide
noncomputable section
theorem h252Fiber3Pointc3_isUnit {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (hq : integerCoefficientEval a h252FiberCRTQ3 = 0) : IsUnit (h252Fiber3Pointc3 a) := by
  apply torusScaledRationalValue_isUnit a h252Fiber3PointScale (ne_of_gt h252Fiber3PointScale_pos) h252Fiber3Pointc3Coeffs h252Fiber3Pointv3Coeffs
  have h := integerCoefficientEval_eq_of_equal a _ _ h252Fiber3Pointinverse3_check
  simp only [integerCoefficientEval_add, integerCoefficientEval_mul, integerCoefficientEval_singleton,
    Int.cast_neg, Int.cast_pow, hq, zero_mul] at h
  linear_combination h
end

end Biunimodular.F11
