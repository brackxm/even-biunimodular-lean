/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientModular
import Biunimodular.F11.FiniteFieldIrreducibilityIterCriterion

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11
open Polynomial
instance h252Fiber5Prime3 : Fact (Nat.Prime 3) := ⟨by decide⟩
def h252Fiber5Mod3Factor1Coeffs : List ℤ := [1, 0, 1, 1, 0, 1, -1, 1, 0, -1, -1, 1, 1, -1, -1, 1, 0, 0, -1, -1, 1, 1, 1, -1, -1, -1, -1, 0, 0, 1, -1, 1, -1, 0, 0, -1, 0, -1, 0, -1] ++ [1]
def h252Fiber5Mod3Factor1q1Coeffs : List ℤ := []
def h252Fiber5Mod3Factor1q10Coeffs : List ℤ := [-1, -1, -1, 1, 0, 0, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 1, -1, -1, 1, 1, 0, 1, 1, -1, 1, 1, -1, 1, -1, 0, 1, -1, 1, -1, 1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 1, 0, -1, -1, 0, 1, -1, 0, 1, -1, -1, -1, -1, 0, 1, 1, -1, 0, 1, 1, 0, -1, 0, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1q11Coeffs : List ℤ := [1, 0, -1, 1, -1, 0, -1, -1, 0, -1, 1, 1, 1, 0, 0, -1, 0, 1, 1, -1, 0, 1, 0, -1, 0, 1, 0, 0, -1, -1, -1, 1, -1, 0, 1, -1, -1, -1, -1, -1, 1, 0, 0, -1, 1, -1, -1, 0, -1, -1, 1, 0, -1, 0, -1, 1, -1, -1, -1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1]
def h252Fiber5Mod3Factor1q12Coeffs : List ℤ := [-1, 0, 0, -1, 1, 1, 1, 0, -1, 0, -1, -1, 1, 0, 0, -1, 1, -1, -1, -1, -1, 0, 0, -1, 1, -1, -1, 1, 1, 1, -1, 0, -1, -1, -1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, -1, 0, -1, 0, -1, 1, 1, 1, 0, -1, 0, 1, -1, 0, -1, 0, -1, 0, -1, -1, -1]
def h252Fiber5Mod3Factor1q13Coeffs : List ℤ := [-1, 1, 0, 1, 0, -1, 1, 1, -1, 1, -1, 1, 1, 1, 0, -1, 1, -1, -1, 1, 1, 1, 0, 0, 0, 0, -1, -1, 0, 1, -1, 1, 0, -1, 0, -1, 1, -1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, -1, 1, 0, 1, 0, -1, -1, 1, 1, 0, -1, 1, -1, 1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 0, 1, -1, -1, -1]
def h252Fiber5Mod3Factor1q14Coeffs : List ℤ := [1, 1, 1, 0, -1, 0, -1, 0, 1, 0, 0, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, 0, 0, 1, 0, 0, 0, 1, 0, -1, 1, 1, 0, 1, 0, -1, 1, -1, 1, 1, -1, 1, 1, -1, 1, -1, 0, -1, 1, 0, 1, -1, 0, -1, 0, -1, 1, 0, -1, 0, -1, 1, 0, 1, 1, -1, -1, 1, -1, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1q15Coeffs : List ℤ := [1, 1, -1, 0, -1, 0, -1, 1, -1, 0, 1, 1, -1, 1, 1, 0, 1, -1, 0, 1, 0, -1, 1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 0, -1, 1, 1, 0, 0, 0, 0, -1, -1, 1, -1, 0, 0, 1, 1, -1, 1, 1, 0, 0, 0, 0, -1, 1, -1, -1, -1, -1]
def h252Fiber5Mod3Factor1q16Coeffs : List ℤ := [1, 1, 1, 1, 1, 0, -1, 1, 0, -1, 1, -1, 0, 1, 1, -1, 0, 0, 1, -1, 0, 0, 0, 0, -1, -1, 1, -1, 0, 0, 0, 1, 1, 0, 1, 1, 0, -1, 0, 1, 1, 0, -1, -1, 1, 1, -1, 0, -1, -1, 0, 1, 0, -1, 1, -1, 1, 0, -1, 1, 1, 1, 0, -1, 0, 1, -1, 0, -1, 0, -1, 0, -1, -1, -1]
def h252Fiber5Mod3Factor1q17Coeffs : List ℤ := [1, -1, 1, 0, 0, 0, 1, 1, -1, 1, 0, 1, -1, 0, -1, 1, 0, 0, 0, 1, -1, -1, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, 1, 0, -1, -1, 0, 0, -1, 1, 0, -1, 0, 0, 1, -1, 1, 0, -1, 1, 1, 0, -1, -1, 0, 1, 0, 1, -1, -1, 0, -1, 0, -1, 0, -1, -1, -1]
def h252Fiber5Mod3Factor1q18Coeffs : List ℤ := [0, 0, 0, 1, 0, -1, 0, 1, 0, 1, -1, -1, -1, 1, -1, 0, 0, 1, 1, 1, 0, -1, 0, 1, -1, -1, 1, 0, 0, -1, 0, 1, 0, 1, -1, 1, 0, 0, 0, 1, 0, 1, 0, -1, 1, 1, 1, -1, 1, 0, 0, 1, -1, -1, 0, 1, 0, 1, 0, 1, 1, 1, -1, 0, -1, 0, -1, 1, 1, 1, 0, 1, 1, 0, 1, -1, -1, -1]
def h252Fiber5Mod3Factor1q19Coeffs : List ℤ := [-1, -1, -1, 0, 1, 0, -1, 1, 0, 1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, 1, 1, -1, -1, 1, 0, 0, 1, 1, 1, 0, 1, 1, -1, 1, 0, 0, -1, -1, 1, 1, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, 1, 1, 1, 0, -1, 1, 0, 0, 1, 0, 0, -1, 1, 0, 0, -1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1q2Coeffs : List ℤ := []
def h252Fiber5Mod3Factor1q20Coeffs : List ℤ := [1, 1, -1, -1, -1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, -1, 1, 1, -1, -1, -1, 0, 0, -1, -1, -1, -1, 0, -1, 1, 1, -1, -1, 1, 0, -1, 1, 0, 0, -1, -1, 0, 0, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, 0, 0, 0, -1, 1, -1, -1, -1, -1]
def h252Fiber5Mod3Factor1q21Coeffs : List ℤ := [-1, 0, 0, 0, 1, -1, 1, -1, 1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, 1, -1, 0, 1, 1, 1, 1, 1, -1, 0, -1, 1, -1, 1, 1, -1, 0, 1, -1, -1, 1, 1, -1, 0, 1, 1, 0, 1, 1, -1, 1, 1, 1, 0, 0, 0, 1, 0, 0, -1, 1, -1, 0, 0, -1, -1, -1, 0, -1, -1, 1, 0, 1, 1, 0, 1, -1, -1, -1]
def h252Fiber5Mod3Factor1q22Coeffs : List ℤ := [-1, 1, 1, 0, 1, 0, 1, -1, 1, -1, 0, -1, 0, 1, -1, 1, 0, 1, -1, -1, 1, 0, 1, 1, 1, 0, 1, -1, 1, 1, -1, -1, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, -1, 1, 0, 1, -1, 1, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 1, 1, -1, 0, 1, 1, 1, -1, 1, -1, -1, -1, -1]
def h252Fiber5Mod3Factor1q23Coeffs : List ℤ := [0, 0, 1, 0, 0, 1, -1, 0, 1, 1, 0, 0, -1, 1, 1, 1, 0, -1, -1, 1, -1, 1, 0, -1, -1, 1, -1, 1, 1, 1, 0, 1, -1, -1, 0, 1, 0, 0, 0, 0, -1, -1, 1, 0, -1, -1, -1, 1, 0, 0, 1, 0, 0, 1, -1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, -1, 1, 1, 1, 0, 1, 1, 0, 1, -1, -1, -1]
def h252Fiber5Mod3Factor1q24Coeffs : List ℤ := [1, 1, 0, -1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, -1, 0, 1, -1, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0, 0, 1, -1, -1, -1, 1, 1, -1, -1, -1, 0, 1, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, -1, 1, 1, -1, 1, 1, -1, 1, -1, 0, 0, 1, 1, -1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1q25Coeffs : List ℤ := [-1, -1, 0, -1, 0, -1, 1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 1, -1, -1, 0, 0, -1, -1, 1, 0, 1, -1, -1, 1, -1, 0, 1, -1, -1, -1, 1, 0, 0, -1, -1, 1, -1, 1, 1, 0, 0, 0, 0, 0, -1, 0, -1, -1, 1, -1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 0, 0, 0, 0, 1, -1, 1, 1, 1, 1]
def h252Fiber5Mod3Factor1q26Coeffs : List ℤ := [0, 0, -1, 0, 1, 0, 1, 1, -1, -1, 1, 1, 0, 0, 1, 0, 0, 0, 1, -1, 1, 0, -1, -1, 1, 0, 0, 0, -1, 0, -1, 1, -1, 1, 0, 1, 1, 1, -1, -1, 1, 1, 0, -1, 1, 1, -1, 0, 0, -1, 0, -1, 1, 1, 0, -1, 0, 1, 1, 1, -1, -1, -1, 0, 0, 1, 0, -1, -1, -1, -1, -1, -1, 1, -1, -1, -1, -1]
def h252Fiber5Mod3Factor1q27Coeffs : List ℤ := [1, -1, -1, 0, 1, 1, -1, 0, 1, 0, -1, 0, 1, -1, 0, 1, 0, -1, 1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 0, 1, 1, 0, 0, 0, 0, 1, 0, -1, 0, -1, -1, -1, 0, 1, -1, -1, -1, -1, 0, -1, 1, 0, 0, -1, 0, 0, -1, -1, -1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, -1, -1, -1]
def h252Fiber5Mod3Factor1q28Coeffs : List ℤ := [0, -1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, -1, 1, -1, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, -1, 1, 1, -1, -1, 0, -1, 1, 0, 0, 1, 1, 1, -1, 1, 0, 1, -1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 1, -1, 1, -1, 0, 0, -1, 0, 1, 0, 1, -1, -1, -1]
def h252Fiber5Mod3Factor1q29Coeffs : List ℤ := [0, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, 1, 0, 1, -1, 0, 0, -1, -1, 0, -1, 1, 1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 1, 0, -1, -1, 0, -1, 1, 1, 1, 1, -1, 0, 0, -1, 1, 1, -1, 0, 1, 1, 1, -1, 1, -1, -1, -1, -1]
def h252Fiber5Mod3Factor1q3Coeffs : List ℤ := []
def h252Fiber5Mod3Factor1q30Coeffs : List ℤ := [1, 1, -1, -1, 1, 1, 1, 0, -1, -1, -1, -1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, -1, -1, -1, -1, -1, -1, -1, 0, -1, 1, 1, -1, 1, 0, -1, -1, -1, 0, -1, -1, 1, 0, -1, 0, -1, 1, -1, -1, -1, 1, 0, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1]
def h252Fiber5Mod3Factor1q31Coeffs : List ℤ := [1, -1, -1, -1, 0, 0, 0, 0, 0, -1, -1, 1, 0, 1, 0, -1, -1, 1, -1, 1, 1, 1, -1, 0, 0, 1, -1, 1, 1, -1, 1, 1, -1, 0, 0, 1, 1, 1, -1, -1, 0, 0, 1, 0, -1, 1, 0, 1, 1, 0, -1, 0, -1, 1, 1, 0, -1, 0, 0, 1, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1q32Coeffs : List ℤ := [1, 1, -1, 0, -1, 1, 0, -1, 1, 0, 0, 1, -1, -1, 0, 1, -1, 1, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, -1, 1, -1, 0, -1, 0, 0, 1, 1, 1, 0, -1, 1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -1, 1, -1, 0, -1, 0, -1, -1, -1, 0, 1, 1, 0, 0, 0, -1, -1, 0, 1, -1, 1, -1, 0, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1q33Coeffs : List ℤ := [0, 0, 1, 1, 0, -1, -1, 1, -1, -1, -1, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 0, 1, -1, -1, -1, 0, -1, 1, 1, 0, -1, -1, 1, 1, 1, 0, 1, 0, -1, -1, 1, 0, 1, 0, 1, -1, -1, -1, 0, -1, -1, 0, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1q34Coeffs : List ℤ := [1, -1, 1, 1, 0, 1, 0, -1, -1, 1, -1, -1, -1, 1, 1, 0, -1, 0, -1, -1, -1, 0, 1, -1, -1, 1, -1, 0, 1, 1, 1, 0, 0, 1, 0, -1, -1, 0, 1, -1, 1, 1, -1, 1, 1, -1, 0, 0, 0, 0, -1, -1, 1, 1, 1, 1, -1, 0, 1, 0, 1, 1, 0, 1, 1, -1, 1, 0, -1, 1, 0, 1, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1q35Coeffs : List ℤ := [-1, -1, 0, -1, 0, 1, -1, 0, -1, 1, 1, 0, 1, -1, -1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, -1, -1, -1, 1, -1, 1, 0, 0, 0, 1, 1, 0, -1, -1, 0, 1, 1, -1, -1, -1, 1, 0, -1, 1, -1, 0, 0, 1, -1, -1, 1, -1, 1, 0, -1, 1, 0, 1, 0, -1, 0, 0, -1, 0, 0, 0, -1, 1, -1, -1, -1, -1]
def h252Fiber5Mod3Factor1q36Coeffs : List ℤ := [0, 0, 0, 0, 0, 0, -1, 1, 0, 1, -1, 0, -1, -1, 1, 0, -1, 1, -1, 0, 1, 0, -1, 1, -1, 1, 0, -1, -1, 1, 1, 1, 0, -1, 1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, 1, 1, -1, 0, 1, 0, -1, 1, -1, 0, -1, 1, 0, -1, 1, 1, -1, -1, 1, -1, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1q37Coeffs : List ℤ := [-1, 1, -1, 0, 0, 0, -1, -1, 1, -1, 1, 1, 0, 0, 0, 0, 0, 1, 1, -1, -1, -1, 1, 1, 1, 0, 1, 1, -1, 0, -1, 1, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, -1, 1, 0, 1, -1, 1, 1, -1, 0, 0, 0, 0, 1, 1, 1, -1, -1, -1, 0, 0, 0, -1, -1, 0, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1, 1]
def h252Fiber5Mod3Factor1q38Coeffs : List ℤ := [-1, 1, -1, 1, 1, -1, -1, -1, 1, 0, -1, 0, 1, 1, -1, -1, -1, -1, 0, 1, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, -1, -1, 1, 0, 0, -1, -1, 1, 0, 1, -1, 1, -1, -1, 0, -1, 0, 1, 1, 0, 0, 1, -1, 1, -1, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1q39Coeffs : List ℤ := [-1, 0, 0, 1, 1, 1, -1, -1, 0, -1, 1, 0, 1, -1, -1, 1, -1, 0, 0, -1, 1, -1, 1, 0, -1, -1, 1, -1, 1, 1, 0, 0, -1, -1, 1, -1, 1, -1, 0, -1, 1, 0, 0, 0, 0, 1, 1, -1, 1, 1, -1, -1, -1, 0, 1, -1, 0, 0, -1, 0, -1, -1, 1, -1, 1, 0, 1, -1, 0, 1, 1, 1, -1, 1, -1, -1, -1, -1]
def h252Fiber5Mod3Factor1q4Coeffs : List ℤ := [1, 0, -1, 1, -1, -1, -1, 1, -1, 0, 1, 1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 0, 1, -1, -1, 1, -1, -1, -1, 0, 1, 1, -1, 0, -1, -1, 0, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1q40Coeffs : List ℤ := [-1, -1, 1, -1, 0, 1, -1, 1, 0, -1, 0, 1, -1, -1, -1, -1, -1, 0, 1, 1, -1, 1, 1, 1, 0, 1, -1, -1, 1, 1, -1, -1, -1, 1, 0, 1, 0, -1, 1, 1, 1, 0, -1, 0, 1, -1, 1, 1, 0, -1, 0, -1, 1, 1, 1, 1, 0, 1, -1, -1, 0, -1, 0, 1, 1, 1, 1, 0, -1, 0, 1, 0, -1, 0, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1q5Coeffs : List ℤ := [-1, 0, -1, -1, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1, 0, 1, 0, -1, -1, -1, 1, 1, 0, 1, -1, -1, 0, -1, 1, 0, 0, 0, -1, -1, 0, 0, -1, 0, 1, -1, 0, -1, 0, 1, 1, 0, -1, -1, 0, 1, -1, 0, 1, 1, -1, -1, 0, 1, 1, 1, 1, -1, 1, -1, -1, -1, -1]
def h252Fiber5Mod3Factor1q6Coeffs : List ℤ := [0, 0, -1, 0, -1, 0, 0, 1, 1, 1, 0, -1, -1, 1, 1, -1, 1, -1, 0, -1, -1, -1, 0, 0, 0, -1, 1, 0, 1, -1, -1, 1, 0, 1, 1, 0, 0, 1, -1, -1, 1, -1, -1, 0, -1, 0, -1, 0, -1, 0, -1, -1, -1, 1, 1, -1, -1, 1, 0, 0, 1, 1, 0, -1, -1, 1, 0, -1, -1, 0, 1, 0, 0, -1, 0, -1, -1, -1]
def h252Fiber5Mod3Factor1q7Coeffs : List ℤ := [-1, 0, 1, 0, 1, 0, -1, 0, 0, -1, -1, 1, 1, 1, 0, -1, 1, 1, 1, -1, -1, 1, 1, 0, 0, 1, 0, -1, -1, 1, 1, 1, -1, 1, 0, 0, -1, 0, 1, -1, -1, -1, 1, 0, -1, 0, 0, 1, 0, 0, -1, -1, 1, -1, 1, 0, -1, -1, 1, 0, -1, 1, 1, 0, -1, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1q8Coeffs : List ℤ := [-1, 1, 1, 1, -1, -1, -1, 0, 1, 0, -1, 1, 1, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, -1, -1, 1, -1, 1, -1, 0, 1, 1, -1, 1, 0, -1, 0, 1, -1, 1, 1, 0, -1, -1, 1, 1, 0, -1, 0, 0, 0, -1, 1, -1, 0, -1, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, -1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1q9Coeffs : List ℤ := [-1, 1, 0, 0, 1, -1, 0, 0, 0, -1, 1, 0, -1, 1, 1, 1, 1, -1, 0, 0, 1, 1, 1, 0, 1, -1, 1, -1, -1, 0, 1, 1, 0, -1, 1, -1, 0, 0, 1, -1, 0, 0, 1, 0, -1, 1, 1, 0, -1, 0, -1, 1, -1, 1, -1, 1, -1, 0, 0, -1, 0, 1, 0, 1, -1, -1, -1, 0, -1, -1, 0, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1r0Coeffs : List ℤ := [0, 1]
def h252Fiber5Mod3Factor1r1Coeffs : List ℤ := [0, 0, 0, 1]
def h252Fiber5Mod3Factor1r10Coeffs : List ℤ := [1, 1, -1, 0, -1, 1, 1, 0, 1, -1, 1, 1, -1, -1, 1, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, -1, -1, 0, 0, -1, 0, 1, 0, 1, -1, 1]
def h252Fiber5Mod3Factor1r11Coeffs : List ℤ := [0, 0, 0, -1, -1, -1, 1, -1, -1, 1, -1, 0, 0, 0, 0, -1, 0, 0, 1, 1, 1, -1, 0, 1, 0, -1, -1, 1, -1, 1, 0, 1, 1, 0, -1, -1]
def h252Fiber5Mod3Factor1r12Coeffs : List ℤ := [1, 0, 1, -1, -1, 1, 1, -1, 0, 1, -1, -1, -1, 1, 1, 1, 0, 1, 1, 0, 1, 1, -1, 0, -1, 0, 1, 1, -1, -1, 1, 1, 0, 0, -1, 1, 0, 1, 0, -1]
def h252Fiber5Mod3Factor1r13Coeffs : List ℤ := [-1, -1, 1, -1, -1, 1, 0, -1, -1, -1, 1, -1, 0, -1, -1, 1, 1, 1, -1, -1, 0, 1, 0, -1, -1, -1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1r14Coeffs : List ℤ := [1, -1, 1, 0, -1, 1, 0, 0, 0, 1, 0, 1, 1, -1, 0, -1, -1, 1, 1, -1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, -1, -1, 1, 0, -1, -1, 0, 1, -1]
def h252Fiber5Mod3Factor1r15Coeffs : List ℤ := [0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1, 1, 0, 0, 1, 0, 0, 1, -1, 1, -1, 1, 1, -1, -1, 0, 0, 1, 1, 0, -1, -1]
def h252Fiber5Mod3Factor1r16Coeffs : List ℤ := [-1, -1, 1, -1, 0, 0, -1, 0, 0, 1, 0, 0, -1, -1, 1, -1, 1, 1, 0, 0, -1, 0, 0, 1, 1, 1, -1, 1, -1, 0, -1, 1, 0, -1, 0, -1, -1]
def h252Fiber5Mod3Factor1r17Coeffs : List ℤ := [1, 1, 1, -1, 0, 1, -1, -1, -1, -1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, 1, 1, -1, -1, -1, 0, -1, -1, 1, 1, -1, 1, 1, 1, 0, 1, -1, 0, 0, -1]
def h252Fiber5Mod3Factor1r18Coeffs : List ℤ := [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, -1, 0, -1, 1, -1, 1, 1, -1, 1, -1, 1, 0, 0, 0, -1, -1, 1, 1, 1, 0, 1, 0, -1, 1, 1, 0, 1, 1]
def h252Fiber5Mod3Factor1r19Coeffs : List ℤ := [-1, 1, -1, -1, 1, -1, 0, -1, 1, 1, -1, -1, -1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, -1, 1, 0, 0, -1, -1, 0, 1, 0, 0, 0, 1, -1]
def h252Fiber5Mod3Factor1r2Coeffs : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def h252Fiber5Mod3Factor1r20Coeffs : List ℤ := [1, -1, 0, 0, 1, 1, 1, -1, 1, 1, 0, -1, 1, -1, 0, 1, 1, 1, 0, 0, 1, -1, 0, 1, 0, 0, -1, -1, 0, 1, 1, 1, -1, -1, -1, 1, 0, 0, 0, -1]
def h252Fiber5Mod3Factor1r21Coeffs : List ℤ := [-1, 0, 1, 0, -1, -1, 0, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 0, -1, 0, 1, 1, -1, 0, 0, 0, 0, 1, 1, 1, -1, 0, 0, -1, 0, 0, 1, 1, -1]
def h252Fiber5Mod3Factor1r22Coeffs : List ℤ := [0, -1, 0, 0, 0, 0, 0, 1, 1, 1, 1, -1, 0, 1, -1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 1, 0, -1, -1, 0, 0, -1]
def h252Fiber5Mod3Factor1r23Coeffs : List ℤ := [0, 0, -1, -1, -1, 1, 1, 1, 0, -1, 1, 1, -1, 1, 0, 0, -1, 0, -1, 1, -1, 1, 1, 1, 0, 0, -1, -1, 1, -1, -1, 1, -1, 1, 1, 0, 0, 1, 1]
def h252Fiber5Mod3Factor1r24Coeffs : List ℤ := [-1, -1, -1, -1, 1, 0, -1, 1, 0, 0, -1, 1, -1, -1, -1, -1, 1, -1, 0, 1, -1, -1, 0, 1, 1, 0, 0, 1, -1, 1, 1, 0, -1, 0, 1, 1, 1, 0, -1, 1]
def h252Fiber5Mod3Factor1r25Coeffs : List ℤ := [0, 1, 1, -1, 1, 0, -1, 1, -1, -1, -1, 1, -1, 0, 0, 0, -1, -1, -1, 1, 0, 1, -1, -1, 0, 1, 0, 1, 0, -1, 1, -1, -1, 1, 0, 1, 0, -1, 1, -1]
def h252Fiber5Mod3Factor1r26Coeffs : List ℤ := [0, 0, 1, 1, 0, 1, -1, -1, -1, 1, 0, 1, 0, 1, -1, 1, 0, 0, 0, 0, 1, -1, 1, -1, 0, 1, 0, -1, 1, -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1]
def h252Fiber5Mod3Factor1r27Coeffs : List ℤ := [-1, 1, 0, 0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, -1, 0, 1, 0, 1, -1, -1, 0, 0, -1, 0, -1]
def h252Fiber5Mod3Factor1r28Coeffs : List ℤ := [-1, 1, -1, 1, -1, 0, 1, -1, -1, 1, 0, -1, 0, 1, 1, 0, 0, 1, 1, -1, 0, 1, 0, -1, 0, 1, 0, 1, -1, -1, -1, -1, 0, 0, 1, 0, 0, 1, 1, -1]
def h252Fiber5Mod3Factor1r29Coeffs : List ℤ := [-1, 0, -1, 1, -1, 0, -1, 0, -1, 0, -1, -1, -1, 1, 1, 0, 0, 1, -1, 1, 0, 0, 1, 1, 1, -1, 0, 0, 0, -1, 0, 1, 0, 1, -1, 1]
def h252Fiber5Mod3Factor1r3Coeffs : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def h252Fiber5Mod3Factor1r30Coeffs : List ℤ := [1, -1, 0, -1, -1, 0, 1, -1, 1, 1, -1, 1, -1, 0, 0, 0, -1, 1, -1, -1, -1, 0, -1, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 0, -1, 0, 0, 1]
def h252Fiber5Mod3Factor1r31Coeffs : List ℤ := [0, 1, 0, 0, -1, 1, 0, -1, 1, 1, -1, 0, -1, 1, -1, 1, 1, -1, 0, 1, 0, -1, 1, 0, -1, 0, -1, -1, 0, 1, 0, 1, -1, 0, 0, 1, 1, -1, 0, 1]
def h252Fiber5Mod3Factor1r32Coeffs : List ℤ := [-1, -1, 0, -1, 1, -1, 1, -1, -1, 1, 0, -1, 0, 1, -1, -1, 1, -1, -1, 0, -1, -1, 0, 0, -1, 0, 1, 1, 1, 0, 1, 0, 0, -1, 1, 0, 0, 1]
def h252Fiber5Mod3Factor1r33Coeffs : List ℤ := [-1, 0, -1, 1, -1, -1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0, -1, -1, 1, -1, 1, 1, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 1, -1, 0, 1, 1]
def h252Fiber5Mod3Factor1r34Coeffs : List ℤ := [1, 1, 1, -1, 0, -1, 0, 0, 1, -1, 1, 1, -1, 0, -1, 1, -1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 0, 1, -1]
def h252Fiber5Mod3Factor1r35Coeffs : List ℤ := [-1, 1, 1, 1, 1, 1, 0, -1, 0, 0, 1, -1, -1, 1, 1, 0, -1, -1, 1, 1, 0, -1, 1, 0, 1, 0, -1, 1, 0, 0, 0, -1, -1, 1, 1, 0, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1r36Coeffs : List ℤ := [-1, 0, 0, 1, 0, 0, -1, -1, 1, 0, 0, 0, 0, 1, 1, 1, -1, -1, 0, 0, -1, 1, 0, -1, 0, 1, 0, 1, -1, 1, 0, 1, 1, -1, 1, 1, 1, -1, -1, 1]
def h252Fiber5Mod3Factor1r37Coeffs : List ℤ := [0, -1, -1, 0, 0, -1, -1, 1, 1, 1, -1, 1, -1, -1, 0, 0, 0, 1, 1, -1, 0, 1, 0, 1, 1, 0, 1, 1, 0, -1, -1, 0, 0, 1, 1, 1, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1r38Coeffs : List ℤ := [1, -1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, 0, -1, 1, 0, -1, -1, 1, 1, 0, -1, -1, -1, -1, 1, 0, 1, 0, 1, 0, 0, 1, 1, -1, 0, 1, 1, -1]
def h252Fiber5Mod3Factor1r39Coeffs : List ℤ := [-1, 0, 1, -1, -1, -1, 0, 0, -1, 0, 1, 0, -1, 1, -1, 1, -1, -1, -1, 0, 1, 0, -1, 1, -1, 0, 0, 1, 1, 0, 1, 1, 0, 1, -1, -1, -1, 1, 0, 1]
def h252Fiber5Mod3Factor1r4Coeffs : List ℤ := [-1, 0, 0, 1, -1, 0, -1, 1, 1, 1, -1, -1, 1, 1, -1, 0, 0, 1, 1, 1, -1, 1, -1, 0, 0, -1, -1, -1, 1, 0, 0, 1, -1, 1, 1, 1, -1]
def h252Fiber5Mod3Factor1r40Coeffs : List ℤ := [0, 1]
def h252Fiber5Mod3Factor1r5Coeffs : List ℤ := [0, 0, -1, -1, 1, 0, 0, -1, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 1, -1, 1, 1, -1, 1, 0, 0, 1, -1, 0, 1, -1, -1]
def h252Fiber5Mod3Factor1r6Coeffs : List ℤ := [0, 0, 1, 0, -1, 1, 0, 1, 1, -1, 0, -1, -1, 0, 0, 1, 1, 0, -1, -1, 0, -1, 1, 1, 0, 1, 0, -1, 1, -1, 1, -1, 0, -1, -1, 0, -1, 0, 0, 1]
def h252Fiber5Mod3Factor1r7Coeffs : List ℤ := [1, 0, 0, 1, 1, 0, 0, -1, -1, -1, 1, -1, 1, -1, 1, 0, -1, -1, 1, 0, 1, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, -1, 0, 0, 0, 1, 1]
def h252Fiber5Mod3Factor1r8Coeffs : List ℤ := [-1, -1, 0, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0, 1, 0, 0, 0, 1, 1, -1, 0, -1, 1, 0, 1, 0, -1, 1, -1, -1, 0, -1, 0, 1, -1, 1, 0, 0, 1]
def h252Fiber5Mod3Factor1r9Coeffs : List ℤ := [0, -1, 1, -1, 1, -1, 0, -1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, -1, -1, 1, 0, 1, 0, 0, 0, -1, 1, -1, 1, 0, 0, 1, -1, -1, 1, 0, -1, 1, 1]
def h252Fiber5Mod3Factor1u1Coeffs : List ℤ := [1]
def h252Fiber5Mod3Factor1u10Coeffs : List ℤ := [1, -1, 0, 0, -1, 1, -1, 0, -1, 0, 0, -1, 0, -1, -1, 1, 0, -1, -1, -1, 1, -1, 0, 0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 1, -1, -1]
def h252Fiber5Mod3Factor1u2Coeffs : List ℤ := [1, 0, 0, -1, 0, 1, -1, 0, 1]
def h252Fiber5Mod3Factor1u20Coeffs : List ℤ := [0, 1, 1, -1, 1, 1, -1, -1, -1, 1, 1, 0, -1, 0, 1, -1, 0, 0, -1, 1, 1, -1, 0, 0, -1, -1, 1, 0, -1, 1, -1, 1, -1, 0, -1, 1, 0, 1, 1]
def h252Fiber5Mod3Factor1u4Coeffs : List ℤ := [0, 0, 1, 0, 1, 0, 1, 0, 0, 1, -1, 1, 1, 1, -1, -1, 0, -1, -1, -1, 1, 1, 0, 1, -1, 1, -1, 0, 1, 1, 0, 0, 1, -1, 0, -1]
def h252Fiber5Mod3Factor1u5Coeffs : List ℤ := [1, 1, 0, 1, 0, -1, 0, -1, 1, 0, -1, 1, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1, -1, 1, -1, -1, 0, -1, 1, -1, 1, 1, -1, 1, 1, 1, 0, 1]
def h252Fiber5Mod3Factor1u8Coeffs : List ℤ := [-1, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, 1, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, -1, 1, 0, -1, -1, -1, -1, -1, -1, -1, 1, 1]
def h252Fiber5Mod3Factor1v1Coeffs : List ℤ := [0, 1, 1, 1, -1, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, 1, -1, -1, 0, 0, -1, -1, 1, 1, 1, 1, -1, 0, 0, -1, 0, -1, -1, -1, 1, -1]
def h252Fiber5Mod3Factor1v10Coeffs : List ℤ := [0, 1, -1, 1, 1, 0, 0, -1, 0, -1, 0, 1, -1, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 1, 1, 1, 1, 0, 1, 0, 1, -1, -1, 0, 0, 1, 1, 1]
def h252Fiber5Mod3Factor1v2Coeffs : List ℤ := [0, 1, 0, 0, 1, 0, -1, 0, -1, 1, 0, 1, 1, -1, 0, 0, -1, -1, 0, -1, 1, 0, 1, 1, -1, 1, 0, -1, 1, 0, 1, -1, -1, 0, 1, 1, -1, 1, 1, -1]
def h252Fiber5Mod3Factor1v20Coeffs : List ℤ := [1, 1, 1, -1, 0, 0, 0, -1, 0, 1, -1, 0, -1, 0, 0, 1, 0, -1, 0, 0, -1, 0, 1, 0, -1, 1, 1, 0, 0, 1, 1, -1, 0, 1, -1, 1, 0, -1, 0, 1]
def h252Fiber5Mod3Factor1v4Coeffs : List ℤ := [-1, 1, 0, -1, -1, 1, 1, -1, 0, -1, -1, -1, 1, 1, 0, -1, 1, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 1, 0, 1, -1, 0, 0, 0, 0, 1, 0, 1, 0, -1]
def h252Fiber5Mod3Factor1v5Coeffs : List ℤ := [1, 0, -1, 0, -1, 1, 0, 0, -1, -1, 0, 0, -1, 1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, -1, -1, 1, 0, 0, 1, -1, 0, 1, -1, 1, 1, 1]
def h252Fiber5Mod3Factor1v8Coeffs : List ℤ := [1, 0, 1, 1, 0, -1, 0, -1, -1, -1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, -1, 0, 0, -1, 0, 0, -1, 1, 0, 1, 0, 0, -1, 0, -1, -1, 0, -1]

noncomputable section
def h252Fiber5Mod3Factor1 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1Coeffs
theorem h252Fiber5Mod3Factor1_monic : h252Fiber5Mod3Factor1.Monic := (integerCoefficientPolynomial_monic_degree (R := ZMod 3) _).1
theorem h252Fiber5Mod3Factor1_degree : h252Fiber5Mod3Factor1.natDegree = 40 := by
  have h := (integerCoefficientPolynomial_monic_degree (R := ZMod 3) [1, 0, 1, 1, 0, 1, -1, 1, 0, -1, -1, 1, 1, -1, -1, 1, 0, 0, -1, -1, 1, 1, 1, -1, -1, -1, -1, 0, 0, 1, -1, 1, -1, 0, 0, -1, 0, -1, 0, -1]).2
  simpa only [h252Fiber5Mod3Factor1, h252Fiber5Mod3Factor1Coeffs, List.length_cons, List.length_nil] using h
def h252Fiber5Mod3Factor1r0 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r0Coeffs
def h252Fiber5Mod3Factor1r1 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r1Coeffs
def h252Fiber5Mod3Factor1r2 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r2Coeffs
def h252Fiber5Mod3Factor1r3 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r3Coeffs
def h252Fiber5Mod3Factor1r4 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r4Coeffs
def h252Fiber5Mod3Factor1r5 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r5Coeffs
def h252Fiber5Mod3Factor1r6 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r6Coeffs
def h252Fiber5Mod3Factor1r7 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r7Coeffs
def h252Fiber5Mod3Factor1r8 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r8Coeffs
def h252Fiber5Mod3Factor1r9 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r9Coeffs
def h252Fiber5Mod3Factor1r10 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r10Coeffs
def h252Fiber5Mod3Factor1r11 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r11Coeffs
def h252Fiber5Mod3Factor1r12 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r12Coeffs
def h252Fiber5Mod3Factor1r13 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r13Coeffs
def h252Fiber5Mod3Factor1r14 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r14Coeffs
def h252Fiber5Mod3Factor1r15 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r15Coeffs
def h252Fiber5Mod3Factor1r16 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r16Coeffs
def h252Fiber5Mod3Factor1r17 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r17Coeffs
def h252Fiber5Mod3Factor1r18 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r18Coeffs
def h252Fiber5Mod3Factor1r19 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r19Coeffs
def h252Fiber5Mod3Factor1r20 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r20Coeffs
def h252Fiber5Mod3Factor1r21 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r21Coeffs
def h252Fiber5Mod3Factor1r22 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r22Coeffs
def h252Fiber5Mod3Factor1r23 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r23Coeffs
def h252Fiber5Mod3Factor1r24 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r24Coeffs
def h252Fiber5Mod3Factor1r25 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r25Coeffs
def h252Fiber5Mod3Factor1r26 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r26Coeffs
def h252Fiber5Mod3Factor1r27 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r27Coeffs
def h252Fiber5Mod3Factor1r28 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r28Coeffs
def h252Fiber5Mod3Factor1r29 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r29Coeffs
def h252Fiber5Mod3Factor1r30 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r30Coeffs
def h252Fiber5Mod3Factor1r31 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r31Coeffs
def h252Fiber5Mod3Factor1r32 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r32Coeffs
def h252Fiber5Mod3Factor1r33 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r33Coeffs
def h252Fiber5Mod3Factor1r34 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r34Coeffs
def h252Fiber5Mod3Factor1r35 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r35Coeffs
def h252Fiber5Mod3Factor1r36 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r36Coeffs
def h252Fiber5Mod3Factor1r37 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r37Coeffs
def h252Fiber5Mod3Factor1r38 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r38Coeffs
def h252Fiber5Mod3Factor1r39 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r39Coeffs
def h252Fiber5Mod3Factor1r40 : (ZMod 3)[X] := integerCoefficientEval X h252Fiber5Mod3Factor1r40Coeffs
end
end Biunimodular.F11
