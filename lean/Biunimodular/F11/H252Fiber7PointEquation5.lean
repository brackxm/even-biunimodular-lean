/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7PointData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def h252Fiber7PointG5Coeffs : List ℤ := [(integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 0, 1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber7PointScale^1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 2)) (integerCoefficientPow h252Fiber7Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber7PointScale^3) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 0, 1] (integerCoefficientPow h252Fiber7Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc2Coeffs 2)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1))), (integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 2))), (integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 2)) (integerCoefficientPow h252Fiber7Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1))), (integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber7Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 2))), (integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc2Coeffs 2)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber7PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber7Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber7Pointc3Coeffs 2)) (integerCoefficientPow h252Fiber7Pointc4Coeffs 1)))].foldr integerCoefficientAdd []
set_option maxHeartbeats 0
theorem h252Fiber7PointG5_check : integerCoefficientEqual h252Fiber7PointG5Coeffs
    (integerCoefficientMul h252FiberCRTQ7 h252Fiber7Pointgq5Coeffs) = true := by native_decide
noncomputable section
theorem h252Fiber7PointG5_homogeneous {R : Type*} [CommRing R] [Algebra ℚ R] (a w x : R) :
    integerCoefficientEval a h252Fiber7PointG5Coeffs = (h252Fiber7PointScale : R)^6 *
      rurInverseSparseEval rurInverseGenerator5 (h252Fiber7Pointc1 a) (h252Fiber7Pointc2 a)
        (h252Fiber7Pointc3 a) (h252Fiber7Pointc4 a) w a x := by
  have h1 := torusScaledRationalValue_scaled a h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos) h252Fiber7Pointc1Coeffs
  have h2 := torusScaledRationalValue_scaled a h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos) h252Fiber7Pointc2Coeffs
  have h3 := torusScaledRationalValue_scaled a h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos) h252Fiber7Pointc3Coeffs
  have h4 := torusScaledRationalValue_scaled a h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos) h252Fiber7Pointc4Coeffs
  change (h252Fiber7PointScale : R)*h252Fiber7Pointc1 a = _ at h1
  change (h252Fiber7PointScale : R)*h252Fiber7Pointc2 a = _ at h2
  change (h252Fiber7PointScale : R)*h252Fiber7Pointc3 a = _ at h3
  change (h252Fiber7PointScale : R)*h252Fiber7Pointc4 a = _ at h4
  simp only [h252Fiber7PointG5Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, integerCoefficientEval_scale, integerCoefficientEval_mul,
    integerCoefficientEval_pow, Int.cast_pow, integerCoefficientEval]
  rw [← h1, ← h2, ← h3, ← h4]
  simp only [rurInverseGenerator5, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Int.cast_one, mul_one, one_mul, add_zero]
  ring
theorem h252Fiber7PointG5_zero {R : Type*} [CommRing R] [Algebra ℚ R] (a w x : R)
    (hq : integerCoefficientEval a h252FiberCRTQ7 = 0) :
    rurInverseSparseEval rurInverseGenerator5 (h252Fiber7Pointc1 a) (h252Fiber7Pointc2 a)
      (h252Fiber7Pointc3 a) (h252Fiber7Pointc4 a) w a x = 0 := by
  have h := integerCoefficientEval_eq_of_equal a _ _ h252Fiber7PointG5_check
  rw [integerCoefficientEval_mul, hq, zero_mul, h252Fiber7PointG5_homogeneous] at h
  apply ((torusIntegerScale_isUnit (R := R) h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos)).pow 6).mul_left_cancel
  simpa only [mul_zero] using h
end

end Biunimodular.F11
