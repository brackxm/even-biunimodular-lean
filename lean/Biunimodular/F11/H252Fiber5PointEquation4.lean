/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber5PointData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def h252Fiber5PointG4Coeffs : List ℤ := [(integerCoefficientScale (h252Fiber5PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber5PointScale^1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 2))), (integerCoefficientScale (h252Fiber5PointScale^3) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 1))), (integerCoefficientScale (h252Fiber5PointScale^1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 2)) (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber5PointScale^3) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 0, 1] (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber5PointScale^1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc2Coeffs 2)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber5PointScale^3) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 0, 1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber5PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 2))), (integerCoefficientScale (h252Fiber5PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 2))), (integerCoefficientScale (h252Fiber5PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber5Pointc1Coeffs 2)) (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 1))), (integerCoefficientScale (h252Fiber5PointScale^2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul [0, 1] (integerCoefficientPow h252Fiber5Pointc2Coeffs 1)) (integerCoefficientPow h252Fiber5Pointc3Coeffs 2)) (integerCoefficientPow h252Fiber5Pointc4Coeffs 1)))].foldr integerCoefficientAdd []
set_option maxHeartbeats 0
theorem h252Fiber5PointG4_check : integerCoefficientEqual h252Fiber5PointG4Coeffs
    (integerCoefficientMul h252FiberCRTQ5 h252Fiber5Pointgq4Coeffs) = true := by native_decide
noncomputable section
theorem h252Fiber5PointG4_homogeneous {R : Type*} [CommRing R] [Algebra ℚ R] (a w x : R) :
    integerCoefficientEval a h252Fiber5PointG4Coeffs = (h252Fiber5PointScale : R)^6 *
      rurInverseSparseEval rurInverseGenerator4 (h252Fiber5Pointc1 a) (h252Fiber5Pointc2 a)
        (h252Fiber5Pointc3 a) (h252Fiber5Pointc4 a) w a x := by
  have h1 := torusScaledRationalValue_scaled a h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc1Coeffs
  have h2 := torusScaledRationalValue_scaled a h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc2Coeffs
  have h3 := torusScaledRationalValue_scaled a h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc3Coeffs
  have h4 := torusScaledRationalValue_scaled a h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc4Coeffs
  change (h252Fiber5PointScale : R)*h252Fiber5Pointc1 a = _ at h1
  change (h252Fiber5PointScale : R)*h252Fiber5Pointc2 a = _ at h2
  change (h252Fiber5PointScale : R)*h252Fiber5Pointc3 a = _ at h3
  change (h252Fiber5PointScale : R)*h252Fiber5Pointc4 a = _ at h4
  simp only [h252Fiber5PointG4Coeffs, integerCoefficientEval_sum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, integerCoefficientEval_scale, integerCoefficientEval_mul,
    integerCoefficientEval_pow, Int.cast_pow, integerCoefficientEval]
  rw [← h1, ← h2, ← h3, ← h4]
  simp only [rurInverseGenerator4, rurInverseSparseEval, rurInverseSparseTermEval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Int.cast_one, mul_one, one_mul, add_zero]
  ring
theorem h252Fiber5PointG4_zero {R : Type*} [CommRing R] [Algebra ℚ R] (a w x : R)
    (hq : integerCoefficientEval a h252FiberCRTQ5 = 0) :
    rurInverseSparseEval rurInverseGenerator4 (h252Fiber5Pointc1 a) (h252Fiber5Pointc2 a)
      (h252Fiber5Pointc3 a) (h252Fiber5Pointc4 a) w a x = 0 := by
  have h := integerCoefficientEval_eq_of_equal a _ _ h252Fiber5PointG4_check
  rw [integerCoefficientEval_mul, hq, zero_mul, h252Fiber5PointG4_homogeneous] at h
  apply ((torusIntegerScale_isUnit (R := R) h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos)).pow 6).mul_left_cancel
  simpa only [mul_zero] using h
end

end Biunimodular.F11
