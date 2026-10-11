/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RurInverseSparsePolynomial

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def rurInverseGenerator1 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨2, 0, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨0, 2, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 0, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 2, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 0, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 2, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 2, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 0, 0, 2, 0⟩⟩
]

def rurInverseGenerator2 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 0, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 2, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 0, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 2, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 1, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 1, 0, 2, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 2, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 0, 0, 2, 0⟩⟩
]

def rurInverseGenerator3 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 0, 0, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 2, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 1, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 1, 0, 2, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 1, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 1, 0, 2, 0⟩⟩,
  ⟨1, ⟨2, 0, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨0, 2, 1, 1, 0, 1, 0⟩⟩
]

def rurInverseGenerator4 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 2, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 0, 0, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 1, 0, 0, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 1, 0, 2, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 1, 0, 0, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 1, 0, 2, 0⟩⟩,
  ⟨1, ⟨1, 1, 2, 0, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 0, 2, 0, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 0, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 2, 1, 0, 1, 0⟩⟩
]

def rurInverseGenerator5 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 1, 0, 2, 0⟩⟩,
  ⟨1, ⟨1, 1, 1, 1, 0, 0, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 1, 0, 0, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 1, 0, 2, 0⟩⟩,
  ⟨1, ⟨1, 2, 1, 0, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 1, 2, 0, 1, 0⟩⟩,
  ⟨1, ⟨2, 1, 1, 0, 0, 1, 0⟩⟩,
  ⟨1, ⟨0, 1, 1, 2, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 2, 0, 1, 0, 1, 0⟩⟩,
  ⟨1, ⟨1, 0, 2, 1, 0, 1, 0⟩⟩
]

def rurInverseGenerator6 : List RurInverseTerm7 := [
  ⟨1, ⟨1, 1, 1, 1, 1, 1, 0⟩⟩,
  ⟨-1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩
]

def rurInverseGenerator7 : List RurInverseTerm7 := [
  ⟨1, ⟨0, 0, 0, 0, 0, 2, 0⟩⟩,
  ⟨-2, ⟨0, 0, 0, 0, 0, 1, 1⟩⟩,
  ⟨-1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩
]

def rurInverseSparseOne : List RurInverseTerm7 := [⟨1, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩]


end Biunimodular.F11
