/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurInverseGeneratorsData
import Biunimodular.F11.H252LocalizedTorusEliminationIdeal

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
variable {R : Type*} [CommRing R]

theorem rurInverseGenerator1_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseGenerator1 z1 z2 z3 z4 w z5 x = h252TorusF1 z1 z2 z3 z4 z5 := by
  simp [rurInverseGenerator1, rurInverseSparseEval, rurInverseSparseTermEval, h252TorusF1]
 ; ring

theorem rurInverseGenerator2_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseGenerator2 z1 z2 z3 z4 w z5 x = h252TorusF2 z1 z2 z3 z4 z5 := by
  simp [rurInverseGenerator2, rurInverseSparseEval, rurInverseSparseTermEval, h252TorusF2]
 ; ring

theorem rurInverseGenerator3_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseGenerator3 z1 z2 z3 z4 w z5 x = h252TorusF3 z1 z2 z3 z4 z5 := by
  simp [rurInverseGenerator3, rurInverseSparseEval, rurInverseSparseTermEval, h252TorusF3]
 ; ring

theorem rurInverseGenerator4_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseGenerator4 z1 z2 z3 z4 w z5 x = h252TorusF4 z1 z2 z3 z4 z5 := by
  simp [rurInverseGenerator4, rurInverseSparseEval, rurInverseSparseTermEval, h252TorusF4]
 ; ring

theorem rurInverseGenerator5_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseGenerator5 z1 z2 z3 z4 w z5 x = h252TorusF5 z1 z2 z3 z4 z5 := by
  simp [rurInverseGenerator5, rurInverseSparseEval, rurInverseSparseTermEval, h252TorusF5]
 ; ring

theorem rurInverseGenerator6_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseGenerator6 z1 z2 z3 z4 w z5 x = h252TorusS z1 z2 z3 z4 w z5 := by
  simp [rurInverseGenerator6, rurInverseSparseEval, rurInverseSparseTermEval, h252TorusS, h252TorusD]
 ; ring

theorem rurInverseGenerator7_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseGenerator7 z1 z2 z3 z4 w z5 x = z5 ^ 2 - 2 * x * z5 - 1 := by
  simp [rurInverseGenerator7, rurInverseSparseEval, rurInverseSparseTermEval]
 ; ring

theorem rurInverseSparseOne_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseSparseOne z1 z2 z3 z4 w z5 x = 1 := by
  simp [rurInverseSparseOne, rurInverseSparseEval, rurInverseSparseTermEval]

theorem rurInverseVariable1_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseVariable1 z1 z2 z3 z4 w z5 x = z1 := by
  simp [rurInverseVariable1, rurInverseSparseEval, rurInverseSparseTermEval]

theorem rurInverseVariable2_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseVariable2 z1 z2 z3 z4 w z5 x = z2 := by
  simp [rurInverseVariable2, rurInverseSparseEval, rurInverseSparseTermEval]

theorem rurInverseVariable3_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseVariable3 z1 z2 z3 z4 w z5 x = z3 := by
  simp [rurInverseVariable3, rurInverseSparseEval, rurInverseSparseTermEval]

theorem rurInverseVariable4_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseVariable4 z1 z2 z3 z4 w z5 x = z4 := by
  simp [rurInverseVariable4, rurInverseSparseEval, rurInverseSparseTermEval]

theorem rurInverseVariable5_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseVariable5 z1 z2 z3 z4 w z5 x = z5 := by
  simp [rurInverseVariable5, rurInverseSparseEval, rurInverseSparseTermEval]

theorem rurInverseVariable6_eval (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval rurInverseVariable6 z1 z2 z3 z4 w z5 x = w := by
  simp [rurInverseVariable6, rurInverseSparseEval, rurInverseSparseTermEval]

noncomputable section

theorem rurInverseGenerator1_quotient_zero :
    rurInverseSparseEval rurInverseGenerator1 (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [rurInverseGenerator1_eval]
  simpa [h252LocalizedTorusGenerators, h252LocalizedTorusVar, h252TorusF1] using
    h252LocalizedTorus_generator_zero 0

theorem rurInverseGenerator2_quotient_zero :
    rurInverseSparseEval rurInverseGenerator2 (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [rurInverseGenerator2_eval]
  simpa [h252LocalizedTorusGenerators, h252LocalizedTorusVar, h252TorusF2] using
    h252LocalizedTorus_generator_zero 1

theorem rurInverseGenerator3_quotient_zero :
    rurInverseSparseEval rurInverseGenerator3 (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [rurInverseGenerator3_eval]
  simpa [h252LocalizedTorusGenerators, h252LocalizedTorusVar, h252TorusF3] using
    h252LocalizedTorus_generator_zero 2

theorem rurInverseGenerator4_quotient_zero :
    rurInverseSparseEval rurInverseGenerator4 (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [rurInverseGenerator4_eval]
  simpa [h252LocalizedTorusGenerators, h252LocalizedTorusVar, h252TorusF4] using
    h252LocalizedTorus_generator_zero 3

theorem rurInverseGenerator5_quotient_zero :
    rurInverseSparseEval rurInverseGenerator5 (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [rurInverseGenerator5_eval]
  simpa [h252LocalizedTorusGenerators, h252LocalizedTorusVar, h252TorusF5] using
    h252LocalizedTorus_generator_zero 4

theorem rurInverseGenerator6_quotient_zero :
    rurInverseSparseEval rurInverseGenerator6 (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [rurInverseGenerator6_eval]
  simpa [h252LocalizedTorusGenerators, h252LocalizedTorusVar, h252TorusS, h252TorusD] using
    h252LocalizedTorus_generator_zero 5

theorem rurInverseGenerator7_quotient_zero :
    rurInverseSparseEval rurInverseGenerator7 (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [rurInverseGenerator7_eval]
  have htwo : (Ideal.Quotient.mk h252LocalizedTorusIdeal)
      (2 : H252LocalizedTorusPolynomialRing) = (2 : H252LocalizedTorusAlgebra) := by
    rw [show (2 : H252LocalizedTorusPolynomialRing) = 1 + 1 by ring, map_add, map_one]
    ring
  simpa [h252LocalizedTorusGenerators, h252LocalizedTorusVar, htwo] using
    h252LocalizedTorus_generator_zero 6

theorem rurInverseGenerator8_quotient_zero :
    rurInverseSparseEval rurInverseGenerator8 (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  rw [rurInverseGenerator8, rurInverseSparseEval_ofX]
  have h := h252LocalizedTorusCoordinate_eliminant_zero
  change (Polynomial.aeval (h252LocalizedTorusVar 6) :
    Polynomial ℂ →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom
      (integerCoefficientEval Polynomial.X h252RurHCoeffs) = 0 at h
  rw [integerCoefficientEval_map] at h
  have hX : (Polynomial.aeval (h252LocalizedTorusVar 6) :
      Polynomial ℂ →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom Polynomial.X =
      h252LocalizedTorusVar 6 := Polynomial.aeval_X _
  simpa only [hX] using h

/-- A checked integer linear combination of the eight actual generators
implies that its target vanishes in the original localized quotient. -/
theorem rurInverseSparseCertificate_target_zero
    (m1 m2 m3 m4 m5 m6 m7 m8 target : List RurInverseTerm7)
    (h : rurInverseSparseNormalize (rurInverseSparseSumProducts [
      (m1, rurInverseGenerator1), (m2, rurInverseGenerator2),
      (m3, rurInverseGenerator3), (m4, rurInverseGenerator4),
      (m5, rurInverseGenerator5), (m6, rurInverseGenerator6),
      (m7, rurInverseGenerator7), (m8, rurInverseGenerator8),
      (rurInverseSparseScale (-1) target, rurInverseSparseOne)]) = []) :
    rurInverseSparseEval target (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  have hs := rurInverseSparseZeroCheck_sound _ h (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    rurInverseGenerator1_quotient_zero, rurInverseGenerator2_quotient_zero,
    rurInverseGenerator3_quotient_zero, rurInverseGenerator4_quotient_zero,
    rurInverseGenerator5_quotient_zero, rurInverseGenerator6_quotient_zero,
    rurInverseGenerator7_quotient_zero, rurInverseGenerator8_quotient_zero,
    rurInverseSparseOne_eval, rurInverseSparseEval_scale,
    Int.cast_neg, Int.cast_one, mul_zero, zero_add, add_zero, mul_one] at hs
  linear_combination -hs

end
end Biunimodular.F11
