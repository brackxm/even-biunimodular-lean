/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Biunimodular.F11

/-! Generated finite replay metadata for the degree-eight 8/7/5 computation. -/

def canonicalEightCycleData : List Nat := [0,1,2,3,4,5,6,7]

def normalizedSevenCycleCount : Nat := 720
def fullEightSevenCount : Nat := 708
def exceptionalSevenCycleCount : Nat := 12
def exceptionalGroupCount : Nat := 2
def exceptionalGroupOrder : Nat := 336
def fiveCycleCount : Nat := 1344

def exceptionalSevenCycleTails : List (List Nat) := [
  [1,4,2,5,6,3],
  [1,4,3,2,5,6],
  [2,1,5,4,6,3],
  [2,3,4,6,1,5],
  [3,6,4,5,1,2],
  [3,6,5,2,4,1],
  [4,2,6,1,3,5],
  [4,5,3,1,2,6],
  [5,1,6,4,3,2],
  [5,3,1,6,2,4],
  [6,2,1,3,5,4],
  [6,5,2,3,4,1]
]

def exceptionalGroupRepresentatives : List (List Nat) := [
  [0,4,5,0,2,6,3],
  [0,4,5,2,3,6,0]
]

theorem degreeEight875_metadata_shapes :
    canonicalEightCycleData.length = 8 ∧
    normalizedSevenCycleCount = 720 ∧
    fullEightSevenCount + exceptionalSevenCycleCount = normalizedSevenCycleCount ∧
    exceptionalSevenCycleTails.length = 12 ∧
    exceptionalGroupRepresentatives.length = 2 ∧
    exceptionalGroupOrder = 336 ∧
    fiveCycleCount = 1344 := by
  native_decide

end Biunimodular.F11
