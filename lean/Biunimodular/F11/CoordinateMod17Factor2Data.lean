/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateMod17Factor1Data
import Biunimodular.F11.IntegerCoefficientModular
import Biunimodular.F11.FiniteFieldIrreducibilityIterCriterion

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
def coordinateMod17Factor2Coeffs : List ℤ := [1, 7, 8, 5, 5, 3, -4, -4, -2, -6] ++ [1]
def coordinateMod17Factor2q1Coeffs : List ℤ := [-7, 4, 5, 4, 6, 4, 6, 1]
def coordinateMod17Factor2q10Coeffs : List ℤ := [-5, 0, 6, 0, -6, -7, -4, 8, 4, -8, 1, -7, -8, -1, -7, -7, -1, -6, -4, -1, 4, 2, 4, 6, -8, 3, 7, -3, 2, 2, 0, -1, 1, 4, -1, 7, -8, -3, 2, 0, -8, 5, -6, -4, -5, -8, 8, 6, 0, 8, 7, 2, -3, -5, 4, -6, -4, 0, -4, 4, 3, -8, 7, -7, -7, -2, -1, 2, 3, -3, 7, 4, 5, 5, -6, 4, -7, -7, -7, -7, -1, -5, -1, 2, 5, -6, -1, 1, 7, -8, -2, 6, 5, -4, -2, -5, -8, -1, 1, -1, -2, 0, 2, -5, 5, 7, 3, -1, 3, 1, -5, 7, -8, 0, 0, -6, 8, -6, -3, 8, 7, -1, -6, -3, -7, -4, 6, 1, -5, 0, 3, -2, -6, 5, 4, 2, 8, -7, 4, -7, -2, -7, -2, -6]
def coordinateMod17Factor2q2Coeffs : List ℤ := [3, 7, 7, 4, -6, 3, -7, 8, -8, 5, -8, 0, -7, 7, 8, 8, -8, 7, -7, 1, -1, 8, -8, -2, -4, -2, 6, -8, 4, -3, -3, -3, 0, 8, -6, -6, 6, -2, -4, 5, 5, -7, -5, -4, 4, 6, 6, 7, -3, 4, -8, -7, 5, 6, 7, 2, -5, -2, -6, -4, -3, 6, 3, -4, -2, 2, -7, 7, 6, -5, 2, 3, 5, 2, 5, -4, -7, 2, -3, -6, 4, -4, 8, -5, -7, 4, -4, 0, 2, 7, 2, -4, 0, 4, -8, -5, -1, 0, 4, 5, -4, -1, -2, 7, 3, 2, 4, -6, 4, 4, -5, 7, -8, 0, 0, -6, 8, -6, -3, 8, 7, -1, -6, -3, -7, -4, 6, 1, -5, 0, 3, -2, -6, 5, 4, 2, 8, -7, 4, -7, -2, -7, -2, -6]
def coordinateMod17Factor2q3Coeffs : List ℤ := [6, -1, 4, -4, 3, 3, -6, 5, -8, -3, 5, -5, 1, 3, 5, -8, 5, 1, -6, 5, 6, 1, -4, 1, -3, -5, 2, -2, 3, 6, 1, -2, -7, -8, 0, 2, 2, 8, -8, -7, -2, -1, -2, 7, 2, 2, -7, -3, 3, 1, 7, -5, -4, 5, -3, 5, -8, -2, 0, 7, 0, -6, -5, -5, 8, -7, -8, 2, -2, 7, 1, -1, 1, -1, -3, -8, -5, -3, -5, -6, 6, 5, 1, 5, 3, 2, -4, 8, -8, 1, 4, 7, 8, 5, -3, -8, -1, -7, -8, 0, 3, -4, -2, 1, -8, 8, -3, 4, 0, 7, -1, 2, -7, 8, 6, 0, -8, 4, 2, 0, 8, 2, 3, -3, 0, -6, 2, 3, 2, 0, -8, -6, -1, -2, -5, 6, 7, -4, -5, -4, -6, -4, -6, -1]
def coordinateMod17Factor2q4Coeffs : List ℤ := [6, 4, -6, 1, 7, 3, 2, 6, 3, 8, -6, -3, 8, -6, -1, -6, -5, -6, 1, 6, -1, -7, 1, -1, 7, 1, 0, 2, -8, 5, 1, -8, 0, -8, 6, -1, -8, 6, -5, 1, 6, -2, -2, -7, 1, 0, 3, -3, 3, -3, 2, 3, -3, 6, 5, 8, -3, -3, -4, -6, -2, -4, 2, 1, 0, 4, -1, -8, -1, 3, 6, -1, 6, -3, -7, -5, -2, -5, 1, -4, -4, 1, 6, -5, 5, -4, 7, 7, 2, 5, -2, 5, -4, -1, -4, 6, 0, -1, -6, 5, 4, -5, -4, -8, 5, -1, -8, -6, -1, -5, -6, 3, 5, -4, -3, -1, -6, -3, 7, 7, 0, -4, 6, 1, -4, 8, 0, -7, 1, 0, -4, -3, 8, -1, 6, 3, -5, -2, 6, -2, -3, -2, -3, 8]
def coordinateMod17Factor2q5Coeffs : List ℤ := [-1, 4, -7, -5, 2, 1, 8, -1, 8, -6, 7, -2, 2, 3, 4, -3, -7, -8, 0, -4, 6, 7, -1, -2, 3, -5, 6, -3, 1, -6, 4, 4, 7, -1, 0, 7, -2, 5, -2, -6, 1, -6, -2, 1, 0, 5, -4, 8, 3, 8, 1, 0, -7, 3, 4, -6, 5, -5, -2, -5, -3, 3, -3, 1, 8, -6, -7, -7, 8, -8, -5, 2, 3, 0, -5, -8, 4, -6, -5, -7, 7, -3, -3, 6, 6, -7, -4, -6, -3, 8, 5, 2, -3, -7, 7, 5, 1, -6, 1, -7, 1, 0, -3, 2, -3, -1, -6, -2, 6, -7, -1, -3, 4, -2, 7, 7, 4, 6, 3, 2, 4, -5, 2, 0, -6, -8, 1, 8, -6, 0, 7, 1, 3, 6, -2, -1, -4, -5, -2, -5, 1, -5, 1, 3]
def coordinateMod17Factor2q6Coeffs : List ℤ := [1, -3, 2, 6, -2, -7, -1, 3, 5, 2, -8, -6, -8, -7, -3, 2, 6, -6, 6, 6, 7, -5, -3, 5, 5, -3, 8, 6, 0, -3, 8, 4, 2, 4, -6, 7, 5, 0, -1, -3, -5, 1, -8, 0, -6, -3, -1, 6, 7, 3, -3, -4, -2, 3, 8, 8, 6, -5, -2, 3, 2, 7, 3, 3, -7, 8, -3, 3, 8, -3, -3, 3, 7, 6, 4, 2, -5, 4, 6, 6, 1, 2, -1, 7, -2, 0, -2, -3, -6, 8, -5, 3, -2, 5, -3, -2, -2, 1, -1, 8, 7, 4, 3, -3, 7, 7, 0, 2, -1, -6, 7, 7, -4, 3, -2, 8, -8, 1, -8, -5, 5, -5, 7, 5, -2, -4, -3, -8, 6, 0, -7, -1, -3, -6, 2, 1, 4, 5, 2, 5, -1, 5, -1, -3]
def coordinateMod17Factor2q7Coeffs : List ℤ := [3, -7, 7, -2, 0, -2, -2, -1, 1, 2, -6, 1, -6, 3, -4, -4, 3, 4, -8, -7, 1, -3, 3, -1, 1, 2, -8, 8, -2, -8, 2, 7, -2, 5, 7, -7, 2, 5, -3, -3, -4, -7, 3, -6, -6, 8, 5, -2, -6, -2, -6, 1, 3, -7, 3, 2, 3, 1, -3, -1, 7, 0, -7, 5, -4, 4, 1, 1, -8, 2, -6, -8, -7, 8, -2, 6, 0, -5, 7, 2, 7, 8, 1, 5, 7, -7, -7, 0, -6, 1, 1, -7, 2, -6, 0, -2, 7, 1, -7, 8, 5, -6, -2, 1, 2, 2, -4, 6, 0, -4, -4, 3, 0, 5, 8, 7, -3, 1, -8, 2, -6, 1, -6, 8, -6, 8, 7]
def coordinateMod17Factor2q8Coeffs : List ℤ := [4, 0, -1, -1, 2, -6, -4, -3, 5, 2, -3, 0, 8, -8, -3, 7, 1, -4, 6, 7, 8, 8, 1, -2, -6, -2, 5, 0, -8, -7, 2, -5, -4, -3, -6, -8, -6, 4, -1, -7, -2, -8, 1, -3, 8, 8, 8, -8, 1, -8, 0, 5, 0, -4, 4, -8, -6, 5, -1, -7, -3, -5, -5, 0, 2, -5, 2, 8, 4, -5, 7, 7, -8, 3, 8, 1, -5, 7, -2, -5, -1, 7, -1, 8, -4, 3, 8, 0, -4, -8, -6, -1, -4, 5, -7, -2, -4, -2, 0, 7, 5, 1, -5, -6, -7, 2, -2, -1, 0, -7, -3, 8, -5, -6, 4, 4, -5, 1, -8, 6, -5, 2, 6, 0, -1, -7, 3, 7, -1, 0, 4, 3, -8, 1, -6, -3, 5, 2, -6, 2, 3, 2, 3, -8]
def coordinateMod17Factor2q9Coeffs : List ℤ := [7, -8, 0, -3, -6, 8, 8, 8, 7, -2, 1, 5, -7, 6, 1, -6, 6, 1, -5, 4, 4, 6, 7, -4, 5, -6, 8, 0, 8, -3, 2, 4, 3, -1, 6, -1, -8, -6, 5, 3, -8, 8, 4, -1, 2, -1, -1, 6, -8, 6, 0, 5, -6, -7, 2, -5, -5, -6, 5, -8, -1, 7, 5, 6, 2, 2, 7, -8, -1, -5, 8, 8, 5, -3, 6, -5, -7, -4, 8, -7, -2, 6, 7, -6, 4, -2, 7, -7, -1, 3, 3, 6, -2, -1, 3, -4, 8, -2, -1, -8, -2, -6, -4, -6, -4, 8, -1, 4, 6, 0, 1, 0, 6, -4, -3, 4, -7, 2, 1, 6, -3, -6, -6, -5, -1, 0, -5, -5, 8, 0, 2, -7, -4, -8, -3, 7, -6, 1, -3, 1, -7, 1, -7, -4]
def coordinateMod17Factor2r0Coeffs : List ℤ := [0, 1]
def coordinateMod17Factor2r1Coeffs : List ℤ := [7, -6, 6, -2, -8, 0, 3, 1, 7, -6]
def coordinateMod17Factor2r10Coeffs : List ℤ := [0, 1]
def coordinateMod17Factor2r2Coeffs : List ℤ := [4, 6, 5, -5, 8, -4, 4, -5, 5, -1]
def coordinateMod17Factor2r3Coeffs : List ℤ := [-2, -7, 6, 5, 2, -8, 5, -8, -7, 8]
def coordinateMod17Factor2r4Coeffs : List ℤ := [-8, 5, -2, -4, 1, 0, -8, 8, -8, 3]
def coordinateMod17Factor2r5Coeffs : List ℤ := [-7, 3, 4, -7, 6, -8, -4, 2, 6, -3]
def coordinateMod17Factor2r6Coeffs : List ℤ := [-8, -4, -6, -1, 5, -8, 5, -8, 7]
def coordinateMod17Factor2r7Coeffs : List ℤ := [6, 3, 1, -6, -5, -8, 7, 4, -7, -8]
def coordinateMod17Factor2r8Coeffs : List ℤ := [2, 6, 3, 5, -7, -7, 5, 8, 7, -4]
def coordinateMod17Factor2r9Coeffs : List ℤ := [-5, -7, 0, -2, -2, -8, 0, -2, 7, -6]
def coordinateMod17Factor2u1Coeffs : List ℤ := [-7, 7, -2, -8, 8, -4, 0, 4]
def coordinateMod17Factor2u2Coeffs : List ℤ := [2, -5, 8, -7, 0, 8, 7, 0, -1]
def coordinateMod17Factor2u5Coeffs : List ℤ := [1, 7, 1, -5, -3, 2, 6, -3, 3]
def coordinateMod17Factor2v1Coeffs : List ℤ := [6, -5, -4, 7, 8, 6, 6, -7, -5]
def coordinateMod17Factor2v2Coeffs : List ℤ := [4, -3, -7, 0, -3, -1, 5, 2, 1, -1]
def coordinateMod17Factor2v5Coeffs : List ℤ := [0, 2, 4, 4, -2, 2, -2, 8, -5, 1]

noncomputable section
def coordinateMod17Factor2 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2Coeffs
theorem coordinateMod17Factor2_monic : coordinateMod17Factor2.Monic := (integerCoefficientPolynomial_monic_degree (R := ZMod 17) _).1
theorem coordinateMod17Factor2_degree : coordinateMod17Factor2.natDegree = 10 := by
  have h := (integerCoefficientPolynomial_monic_degree (R := ZMod 17) [1, 7, 8, 5, 5, 3, -4, -4, -2, -6]).2
  simpa only [coordinateMod17Factor2, coordinateMod17Factor2Coeffs, List.length_cons, List.length_nil] using h
def coordinateMod17Factor2r0 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r0Coeffs
def coordinateMod17Factor2r1 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r1Coeffs
def coordinateMod17Factor2r2 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r2Coeffs
def coordinateMod17Factor2r3 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r3Coeffs
def coordinateMod17Factor2r4 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r4Coeffs
def coordinateMod17Factor2r5 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r5Coeffs
def coordinateMod17Factor2r6 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r6Coeffs
def coordinateMod17Factor2r7 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r7Coeffs
def coordinateMod17Factor2r8 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r8Coeffs
def coordinateMod17Factor2r9 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r9Coeffs
def coordinateMod17Factor2r10 : (ZMod 17)[X] := integerCoefficientEval X coordinateMod17Factor2r10Coeffs
end
end Biunimodular.F11
