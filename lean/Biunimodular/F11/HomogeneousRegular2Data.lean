/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegularOriginalData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-!
-/

def homogeneousRegular2S1_1 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0⟩⟩,
  ⟨⟨6, -6, -8, 2, 2⟩, ⟨1, 0, 0, 0, 0, 1⟩⟩,
  ⟨⟨-3, 0, 1, 0, 0⟩, ⟨0, 1, 0, 1, 0, 0⟩⟩,
  ⟨⟨6, -6, -8, 2, 2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
  ⟨⟨5, 0, -5, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
  ⟨⟨6, -6, -8, 2, 2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
  ⟨⟨-6, 2, 8, -1, -2⟩, ⟨0, 0, 0, 2, 0, 0⟩⟩,
  ⟨⟨6, -5, -8, 2, 2⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
  ⟨⟨3, -3, -4, 1, 1⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
  ⟨⟨6, -6, -8, 2, 2⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
  ⟨⟨3, -3, -4, 1, 1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
]
def homogeneousRegular2S1_2 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨-5, 0, 5, 0, -1⟩, ⟨1, 0, 0, 0, 1, 0⟩⟩,
  ⟨⟨-6, 6, 8, -2, -2⟩, ⟨1, 0, 0, 0, 0, 1⟩⟩,
  ⟨⟨6, -2, -8, 1, 2⟩, ⟨0, 1, 0, 0, 1, 0⟩⟩,
  ⟨⟨-6, 6, 8, -2, -2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
  ⟨⟨3, 0, -1, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
  ⟨⟨-6, 6, 8, -2, -2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
  ⟨⟨-6, 5, 8, -2, -2⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
  ⟨⟨-6, 6, 8, -2, -2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
  ⟨⟨-1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 2, 0⟩⟩,
  ⟨⟨-3, 3, 4, -1, -1⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
  ⟨⟨-3, 3, 4, -1, -1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
]
def homogeneousRegular2W1_1 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨3, -3, -4, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
]

def homogeneousRegular2Syzygies : List (List FixedSliceSparsePolynomial) :=
  [[homogeneousRegular2S1_1, homogeneousRegular2S1_2]]

def homogeneousRegular2LastWitnesses : List (List FixedSliceSparsePolynomial) :=
  [[homogeneousRegular2W1_1]]

def homogeneousRegular2LastComponents : List FixedSliceSparsePolynomial :=
  [homogeneousRegular2S1_2]

def homogeneousRegular2Scales : List ℕ :=
  [1]

end Biunimodular.F11
