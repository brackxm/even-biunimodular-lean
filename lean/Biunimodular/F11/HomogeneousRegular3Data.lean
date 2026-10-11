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

def homogeneousRegular3S1_1 : FixedSliceSparsePolynomial :=
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
def homogeneousRegular3S1_2 : FixedSliceSparsePolynomial :=
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
def homogeneousRegular3S1_3 : FixedSliceSparsePolynomial :=
  []
def homogeneousRegular3W1_1 : FixedSliceSparsePolynomial :=
  []
def homogeneousRegular3W1_2 : FixedSliceSparsePolynomial :=
  []
def homogeneousRegular3S2_1 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 0, 0⟩⟩,
  ⟨⟨0, 6, 6, -2, -2⟩, ⟨1, 0, 0, 0, 0, 1⟩⟩,
  ⟨⟨-1, -3, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 0⟩⟩,
  ⟨⟨0, 6, 6, -2, -2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
  ⟨⟨0, 5, 3, -2, -1⟩, ⟨0, 0, 2, 0, 0, 0⟩⟩,
  ⟨⟨-2, -5, -2, 2, 1⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
  ⟨⟨2, 6, 2, -2, -1⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
  ⟨⟨0, 3, 3, -1, -1⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
  ⟨⟨0, 6, 6, -2, -2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
  ⟨⟨0, 6, 6, -2, -2⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
  ⟨⟨0, 3, 3, -1, -1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
]
def homogeneousRegular3S2_2 : FixedSliceSparsePolynomial :=
  []
def homogeneousRegular3S2_3 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨2, 5, 2, -2, -1⟩, ⟨1, 0, 0, 0, 1, 0⟩⟩,
  ⟨⟨0, -6, -6, 2, 2⟩, ⟨1, 0, 0, 0, 0, 1⟩⟩,
  ⟨⟨-1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 1, 0⟩⟩,
  ⟨⟨0, -6, -6, 2, 2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
  ⟨⟨-2, -6, -2, 2, 1⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
  ⟨⟨0, -6, -6, 2, 2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
  ⟨⟨0, -5, -3, 2, 1⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
  ⟨⟨0, -6, -6, 2, 2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
  ⟨⟨1, 3, 0, -1, 0⟩, ⟨0, 0, 0, 0, 2, 0⟩⟩,
  ⟨⟨0, -3, -3, 1, 1⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
  ⟨⟨0, -3, -3, 1, 1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
]
def homogeneousRegular3W2_1 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨0, 3, 3, -1, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
]
def homogeneousRegular3W2_2 : FixedSliceSparsePolynomial :=
  []
def homogeneousRegular3S3_1 : FixedSliceSparsePolynomial :=
  []
def homogeneousRegular3S3_2 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 0, 0⟩⟩,
  ⟨⟨0, 6, 6, -2, -2⟩, ⟨1, 0, 0, 0, 0, 1⟩⟩,
  ⟨⟨-1, -3, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 0⟩⟩,
  ⟨⟨0, 6, 6, -2, -2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
  ⟨⟨0, 5, 3, -2, -1⟩, ⟨0, 0, 2, 0, 0, 0⟩⟩,
  ⟨⟨-2, -5, -2, 2, 1⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
  ⟨⟨2, 6, 2, -2, -1⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
  ⟨⟨0, 3, 3, -1, -1⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
  ⟨⟨0, 6, 6, -2, -2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
  ⟨⟨0, 6, 6, -2, -2⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
  ⟨⟨0, 3, 3, -1, -1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
]
def homogeneousRegular3S3_3 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨1, 3, 0, -1, 0⟩, ⟨1, 0, 0, 1, 0, 0⟩⟩,
  ⟨⟨0, -6, -6, 2, 2⟩, ⟨1, 0, 0, 0, 0, 1⟩⟩,
  ⟨⟨-2, -6, -2, 2, 1⟩, ⟨0, 1, 0, 1, 0, 0⟩⟩,
  ⟨⟨0, -6, -6, 2, 2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
  ⟨⟨2, 5, 2, -2, -1⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
  ⟨⟨0, -6, -6, 2, 2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
  ⟨⟨-1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 2, 0, 0⟩⟩,
  ⟨⟨0, -5, -3, 2, 1⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
  ⟨⟨0, -3, -3, 1, 1⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
  ⟨⟨0, -6, -6, 2, 2⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
  ⟨⟨0, -3, -3, 1, 1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
]
def homogeneousRegular3W3_1 : FixedSliceSparsePolynomial :=
  []
def homogeneousRegular3W3_2 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨0, 3, 3, -1, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
]
def homogeneousRegular3S4_1 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨11, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0⟩⟩,
  ⟨⟨-66, -132, -44, 44, 22⟩, ⟨0, 1, 1, 0, 0, 1⟩⟩,
  ⟨⟨-110, -374, -154, 132, 66⟩, ⟨0, 1, 0, 1, 0, 1⟩⟩,
  ⟨⟨-33, -33, 11, 11, 0⟩, ⟨0, 0, 2, 1, 0, 0⟩⟩,
  ⟨⟨-22, 176, 132, -66, -44⟩, ⟨0, 0, 2, 0, 0, 1⟩⟩,
  ⟨⟨44, 88, 11, -33, -11⟩, ⟨0, 0, 1, 2, 0, 0⟩⟩,
  ⟨⟨-55, -121, -44, 44, 22⟩, ⟨0, 0, 1, 1, 1, 0⟩⟩,
  ⟨⟨-33, -66, -22, 22, 11⟩, ⟨0, 0, 1, 1, 0, 1⟩⟩,
  ⟨⟨44, 242, 110, -88, -44⟩, ⟨0, 0, 1, 0, 1, 1⟩⟩,
  ⟨⟨-33, -154, -88, 55, 33⟩, ⟨0, 0, 1, 0, 0, 2⟩⟩,
  ⟨⟨-66, -132, -44, 44, 22⟩, ⟨0, 0, 0, 2, 0, 1⟩⟩,
  ⟨⟨-44, -308, -176, 110, 66⟩, ⟨0, 0, 0, 1, 1, 1⟩⟩,
  ⟨⟨0, 88, 66, -33, -22⟩, ⟨0, 0, 0, 1, 0, 2⟩⟩
]
def homogeneousRegular3S4_2 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨-44, -88, -11, 33, 11⟩, ⟨0, 1, 1, 0, 1, 0⟩⟩,
  ⟨⟨66, 132, 44, -44, -22⟩, ⟨0, 1, 1, 0, 0, 1⟩⟩,
  ⟨⟨110, 242, 88, -88, -44⟩, ⟨0, 1, 0, 0, 1, 1⟩⟩,
  ⟨⟨55, 187, 77, -66, -33⟩, ⟨0, 0, 2, 0, 1, 0⟩⟩,
  ⟨⟨22, -176, -132, 66, 44⟩, ⟨0, 0, 2, 0, 0, 1⟩⟩,
  ⟨⟨0, -187, -132, 66, 44⟩, ⟨0, 0, 1, 1, 1, 0⟩⟩,
  ⟨⟨110, 242, 88, -88, -44⟩, ⟨0, 0, 1, 1, 0, 1⟩⟩,
  ⟨⟨44, 209, 110, -77, -44⟩, ⟨0, 0, 1, 0, 2, 0⟩⟩,
  ⟨⟨55, 121, 44, -44, -22⟩, ⟨0, 0, 1, 0, 1, 1⟩⟩,
  ⟨⟨33, 154, 88, -55, -33⟩, ⟨0, 0, 1, 0, 0, 2⟩⟩,
  ⟨⟨88, 418, 220, -154, -88⟩, ⟨0, 0, 0, 1, 1, 1⟩⟩,
  ⟨⟨44, 110, 44, -44, -22⟩, ⟨0, 0, 0, 0, 2, 1⟩⟩,
  ⟨⟨22, -33, -44, 11, 11⟩, ⟨0, 0, 0, 0, 1, 2⟩⟩
]
def homogeneousRegular3S4_3 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨-44, -209, -110, 77, 44⟩, ⟨0, 1, 0, 1, 1, 0⟩⟩,
  ⟨⟨110, 374, 154, -132, -66⟩, ⟨0, 1, 0, 1, 0, 1⟩⟩,
  ⟨⟨-110, -242, -88, 88, 44⟩, ⟨0, 1, 0, 0, 1, 1⟩⟩,
  ⟨⟨55, 308, 176, -110, -66⟩, ⟨0, 0, 1, 1, 1, 0⟩⟩,
  ⟨⟨-44, -110, -44, 44, 22⟩, ⟨0, 0, 1, 1, 0, 1⟩⟩,
  ⟨⟨-154, -484, -198, 176, 88⟩, ⟨0, 0, 1, 0, 1, 1⟩⟩,
  ⟨⟨33, 33, -11, -11, 0⟩, ⟨0, 0, 0, 2, 1, 0⟩⟩,
  ⟨⟨66, 132, 44, -44, -22⟩, ⟨0, 0, 0, 2, 0, 1⟩⟩,
  ⟨⟨-66, -187, -77, 66, 33⟩, ⟨0, 0, 0, 1, 2, 0⟩⟩,
  ⟨⟨-22, -55, -22, 22, 11⟩, ⟨0, 0, 0, 1, 1, 1⟩⟩,
  ⟨⟨0, -88, -66, 33, 22⟩, ⟨0, 0, 0, 1, 0, 2⟩⟩,
  ⟨⟨-44, -110, -44, 44, 22⟩, ⟨0, 0, 0, 0, 2, 1⟩⟩,
  ⟨⟨-22, 33, 44, -11, -11⟩, ⟨0, 0, 0, 0, 1, 2⟩⟩
]
def homogeneousRegular3W4_1 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨-16, -56, -24, 19, 10⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
  ⟨⟨16, 144, 90, -52, -32⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
]
def homogeneousRegular3W4_2 : FixedSliceSparsePolynomial :=
  [
  ⟨⟨38, 111, 46, -41, -21⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
  ⟨⟨-16, -144, -90, 52, 32⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
]

def homogeneousRegular3Syzygies : List (List FixedSliceSparsePolynomial) :=
  [[homogeneousRegular3S1_1, homogeneousRegular3S1_2, homogeneousRegular3S1_3], [homogeneousRegular3S2_1, homogeneousRegular3S2_2, homogeneousRegular3S2_3], [homogeneousRegular3S3_1, homogeneousRegular3S3_2, homogeneousRegular3S3_3], [homogeneousRegular3S4_1, homogeneousRegular3S4_2, homogeneousRegular3S4_3]]

def homogeneousRegular3LastWitnesses : List (List FixedSliceSparsePolynomial) :=
  [[homogeneousRegular3W1_1, homogeneousRegular3W1_2], [homogeneousRegular3W2_1, homogeneousRegular3W2_2], [homogeneousRegular3W3_1, homogeneousRegular3W3_2], [homogeneousRegular3W4_1, homogeneousRegular3W4_2]]

def homogeneousRegular3LastComponents : List FixedSliceSparsePolynomial :=
  [homogeneousRegular3S1_3, homogeneousRegular3S2_3, homogeneousRegular3S3_3, homogeneousRegular3S4_3]

def homogeneousRegular3Scales : List ℕ :=
  [1, 1, 1, 11]

end Biunimodular.F11
