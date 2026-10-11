/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusOriginalGeneratorsData
import Biunimodular.F11.TorusSparseZ5

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def torusFiberOriginal1 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 1, 1, 0⟩⟩,
  ⟨-1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩
]

def torusFiberOriginal2 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 1, 1, 0⟩⟩,
  ⟨-1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩
]

def torusFiberOriginal3 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 1, 1, 0⟩⟩,
  ⟨-1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩
]

def torusFiberOriginal4 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 1, 1, 0⟩⟩,
  ⟨-1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩
]

def torusFiberOriginal5 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 1, 1, 0⟩⟩,
  ⟨-1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩
]

def torusFiberOriginal6 : List RurInverseTerm7 := [
  ⟨1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 0, 0, 0, 0, 0, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨2, 0, 1, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨0, 2, 1, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 0, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 2, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 0, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 2, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 2, 1, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 0, 1, 2, 0⟩⟩
]

def torusFiberOriginal7 : List RurInverseTerm7 := [
  ⟨1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩,
  ⟨1, ⟨0, 1, 0, 0, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 0, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 2, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 0, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 2, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 1, 1, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 1, 1, 2, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 2, 1, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 0, 1, 2, 0⟩⟩
]

def torusFiberOriginal8 : List RurInverseTerm7 := [
  ⟨1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩,
  ⟨1, ⟨0, 0, 1, 0, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 0, 1, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 2, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 1, 1, 0, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 1, 1, 2, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 1, 1, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 1, 1, 2, 0⟩⟩,
  ⟨1, ⟨2, 0, 1, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨0, 2, 1, 1, 1, 1, 0⟩⟩
]

def torusFiberOriginal9 : List RurInverseTerm7 := [
  ⟨1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩,
  ⟨1, ⟨0, 0, 0, 1, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 0, 1, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 1, 1, 0, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 1, 1, 2, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 1, 1, 0, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 1, 1, 2, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 0, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 2, 1, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 0, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 2, 1, 1, 1, 0⟩⟩
]

def torusFiberOriginal10 : List RurInverseTerm7 := [
  ⟨1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩,
  ⟨1, ⟨0, 0, 0, 0, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 1, 1, 0, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 1, 1, 0, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 1, 1, 2, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 0, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 2, 1, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 0, 1, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 2, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 0, 1, 1, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 2, 1, 1, 1, 0⟩⟩
]


end Biunimodular.F11
