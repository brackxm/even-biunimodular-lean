/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.CharP.Lemmas
import Biunimodular.F11.InvariantPolynomialData

set_option autoImplicit false

noncomputable section

namespace Biunimodular.F11

open Polynomial

def b5r1 : (ZMod 5)[X] := X ^ 5

def b5r2 : (ZMod 5)[X] := X ^ 7 + X ^ 6 - X ^ 3 + X ^ 2 - X

def b5r3 : (ZMod 5)[X] :=
  X ^ 7 - X ^ 6 - 2 * X ^ 5 - 2 * X ^ 4 + 2 * X ^ 3 - 2 * X ^ 2 - 2 * X + 2

def b5r4 : (ZMod 5)[X] := -2 * X ^ 5 - 2 * X ^ 4 + 2 * X ^ 3 + 1

def b5r5 : (ZMod 5)[X] :=
  -2 * X ^ 7 + X ^ 6 - X ^ 5 - 2 * X ^ 4 + X ^ 3 - X - 2

def b5r6 : (ZMod 5)[X] := X ^ 7 - X ^ 5 + 2 * X ^ 4 - 2 * X ^ 3 - X ^ 2 + 1

def b5r7 : (ZMod 5)[X] :=
  -X ^ 7 - X ^ 6 - X ^ 4 - 2 * X ^ 3 + 2 * X ^ 2 - 2 * X + 2

def b5r8 : (ZMod 5)[X] := X

def b5q2 : (ZMod 5)[X] :=
  X ^ 17 - X ^ 16 + 2 * X ^ 15 + X ^ 14 + 2 * X ^ 13 - 2 * X ^ 12 -
    2 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 7 + X ^ 6 + X ^ 5 - 2 * X ^ 4 -
    X ^ 3 - X ^ 2 + X

def b5q3 : (ZMod 5)[X] :=
  X ^ 27 - X ^ 26 + 2 * X ^ 25 + X ^ 24 + 2 * X ^ 23 - X ^ 22 - X ^ 21 +
    2 * X ^ 20 - X ^ 19 + X ^ 16 + X ^ 15 + X ^ 14 + 2 * X ^ 13 + X ^ 12 +
    2 * X ^ 11 + X ^ 10 - X ^ 9 - X ^ 8 - X ^ 7 + 2 * X ^ 4 + 2 * X ^ 3 +
    X ^ 2 + 2 * X - 2

def b5q4 : (ZMod 5)[X] :=
  X ^ 27 - X ^ 26 + 2 * X ^ 25 + X ^ 24 + 2 * X ^ 23 + 2 * X ^ 22 + X ^ 21 -
    2 * X ^ 20 + 2 * X ^ 19 + X ^ 18 + 2 * X ^ 17 - 2 * X ^ 16 + 2 * X ^ 15 -
    2 * X ^ 14 + 2 * X ^ 13 - X ^ 12 + 2 * X ^ 11 + X ^ 8 - X ^ 7 - 2 * X ^ 6 -
    X ^ 5 + X ^ 4 - X ^ 3 - 2 * X ^ 2 + 1

def b5q5 : (ZMod 5)[X] :=
  -2 * X ^ 17 + 2 * X ^ 16 + X ^ 15 - 2 * X ^ 14 + X ^ 13 + 2 * X ^ 12 +
    2 * X ^ 11 + X ^ 10 + 2 * X ^ 9 + 2 * X ^ 7 + X ^ 6 + 2 * X ^ 5 - X ^ 2 + X - 2

def b5q6 : (ZMod 5)[X] :=
  -2 * X ^ 27 + 2 * X ^ 26 + X ^ 25 - 2 * X ^ 24 + X ^ 23 - X ^ 21 +
    2 * X ^ 20 + X ^ 18 - 2 * X ^ 17 - X ^ 16 + X ^ 15 + X ^ 14 - 2 * X ^ 13 -
    X ^ 12 + X ^ 11 + 2 * X ^ 10 + X ^ 9 + 2 * X ^ 8 - 2 * X ^ 6 +
    2 * X ^ 5 - X ^ 4 - X ^ 3 + 2 * X ^ 2 + 2

def b5q7 : (ZMod 5)[X] :=
  X ^ 27 - X ^ 26 + 2 * X ^ 25 + X ^ 24 + 2 * X ^ 23 - 2 * X ^ 22 -
    2 * X ^ 19 - 2 * X ^ 18 + X ^ 17 + 2 * X ^ 16 - X ^ 15 + 2 * X ^ 14 +
    2 * X ^ 13 - 2 * X ^ 12 - X ^ 11 - X ^ 10 + X ^ 8 - 2 * X ^ 7 - X ^ 6 +
    2 * X ^ 5 - 2 * X ^ 4 + 2 * X ^ 3 + 2 * X - 1

def b5q8 : (ZMod 5)[X] :=
  -X ^ 27 + X ^ 26 - 2 * X ^ 25 - X ^ 24 - 2 * X ^ 23 + X ^ 22 + X ^ 21 -
    2 * X ^ 20 + X ^ 19 - X ^ 16 - X ^ 15 - X ^ 14 - 2 * X ^ 13 - 2 * X ^ 12 -
    X ^ 11 + 2 * X ^ 10 - X ^ 8 - 2 * X ^ 6 - X ^ 5 + 2 * X ^ 4 - X ^ 3 +
    X ^ 2 - X + 2

end Biunimodular.F11
