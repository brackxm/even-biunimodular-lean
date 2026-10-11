/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-- Degree-six invariant factor for the F11 classification. -/
def invariantA : ℤ[X] :=
  X^6 - 6320*X^5 + 10298240*X^4 - 1009036608*X^3 +
    1012283392*X^2 - 84262912*X + 692224

/-- Degree-eight invariant factor for the F11 classification. -/
def invariantB : ℤ[X] :=
  279841*X^8 - 9805544*X^7 + 210448304*X^6 -
    1535826944*X^5 + 6984915200*X^4 - 8382980096*X^3 +
    3230461952*X^2 - 376668160*X + 7929856

/-- Monic reduction of A modulo 3, coefficient list low-to-high:
`1 + 2X + X² + 2X⁴ + X⁵ + X⁶`. -/
def invariantA3 : (ZMod 3)[X] :=
  1 + 2*X + X^2 + 2*X^4 + X^5 + X^6

/-- Monic reduction of B modulo 5, coefficient list low-to-high:
`1 + 2X² + 4X³ + X⁵ + 4X⁶ + X⁷ + X⁸`. -/
def invariantB5 : (ZMod 5)[X] :=
  1 + 2*X^2 + 4*X^3 + X^5 + 4*X^6 + X^7 + X^8

/-- Exact reduction identity for A. -/
theorem invariantA_mod3 :
    invariantA.map (Int.castRingHom (ZMod 3)) = invariantA3 := by
  norm_num [invariantA, invariantA3]
  reduce_mod_char
  ring

/-- Exact reduction identity for B. -/
theorem invariantB_mod5 :
    invariantB.map (Int.castRingHom (ZMod 5)) = invariantB5 := by
  norm_num [invariantB, invariantB5]
  reduce_mod_char
  ring

end

end Biunimodular.F11
