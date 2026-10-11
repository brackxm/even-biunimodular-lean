/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RationalSparseOperations
import Biunimodular.F11.HomogeneousRegularOriginalData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion3Original1 : RationalSparsePolynomial :=
  ⟨1, by decide, homogeneousRegularOriginal1⟩

def homogeneousCompletion3Original2 : RationalSparsePolynomial :=
  ⟨1, by decide, homogeneousRegularOriginal2⟩

def homogeneousCompletion3Original3 : RationalSparsePolynomial :=
  ⟨1, by decide, homogeneousRegularOriginal3⟩

def homogeneousCompletion3Original : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Original1, homogeneousCompletion3Original2, homogeneousCompletion3Original3]

def homogeneousCompletion3G1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨1, 0, 0, 0, 0, 1⟩⟩,
    ⟨⟨-1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 1, 0⟩⟩,
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨-1, -1, 1, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨1, -2, -1, 1, 0⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨1, 2, -3, -1, 1⟩, ⟨0, 0, 0, 0, 2, 0⟩⟩,
    ⟨⟨1, 0, -3, 0, 1⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨1, 0, -3, 0, 1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3G2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
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
  ]⟩

def homogeneousCompletion3G3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
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
  ]⟩

def homogeneousCompletion3G4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 0⟩⟩,
    ⟨⟨2, -6, 0, 2, 0⟩, ⟨0, 1, 0, 1, 0, 1⟩⟩,
    ⟨⟨-10, 4, 16, -2, -4⟩, ⟨0, 1, 0, 0, 1, 1⟩⟩,
    ⟨⟨-3, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0⟩⟩,
    ⟨⟨-4, 0, 8, 0, -2⟩, ⟨0, 0, 1, 1, 0, 1⟩⟩,
    ⟨⟨-6, 6, 8, -2, -2⟩, ⟨0, 0, 1, 0, 1, 1⟩⟩,
    ⟨⟨4, -3, -4, 1, 1⟩, ⟨0, 0, 0, 2, 1, 0⟩⟩,
    ⟨⟨6, -4, -8, 2, 2⟩, ⟨0, 0, 0, 2, 0, 1⟩⟩,
    ⟨⟨-4, 2, 7, -1, -2⟩, ⟨0, 0, 0, 1, 2, 0⟩⟩,
    ⟨⟨-2, 0, 4, 0, -1⟩, ⟨0, 0, 0, 1, 1, 1⟩⟩,
    ⟨⟨3, -3, -1, 1, 0⟩, ⟨0, 0, 0, 1, 0, 2⟩⟩,
    ⟨⟨-4, 0, 8, 0, -2⟩, ⟨0, 0, 0, 0, 2, 1⟩⟩,
    ⟨⟨-5, 3, 5, -1, -1⟩, ⟨0, 0, 0, 0, 1, 2⟩⟩
  ]⟩

def homogeneousCompletion3G5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 0⟩⟩,
    ⟨⟨-4, -6, 10, 4, -4⟩, ⟨0, 1, 1, 0, 0, 1⟩⟩,
    ⟨⟨-4, -4, 6, 2, -2⟩, ⟨0, 1, 0, 0, 1, 1⟩⟩,
    ⟨⟨-1, -2, 0, 1, 0⟩, ⟨0, 0, 2, 0, 1, 0⟩⟩,
    ⟨⟨-2, 4, 2, -2, 0⟩, ⟨0, 0, 2, 0, 0, 1⟩⟩,
    ⟨⟨-1, 4, 1, -2, 0⟩, ⟨0, 0, 1, 1, 1, 0⟩⟩,
    ⟨⟨-4, -4, 6, 2, -2⟩, ⟨0, 0, 1, 1, 0, 1⟩⟩,
    ⟨⟨-1, -4, 2, 2, -1⟩, ⟨0, 0, 1, 0, 2, 0⟩⟩,
    ⟨⟨-2, -2, 3, 1, -1⟩, ⟨0, 0, 1, 0, 1, 1⟩⟩,
    ⟨⟨0, -1, -2, 0, 1⟩, ⟨0, 0, 1, 0, 0, 2⟩⟩,
    ⟨⟨-2, -8, 4, 4, -2⟩, ⟨0, 0, 0, 1, 1, 1⟩⟩,
    ⟨⟨0, 2, -4, -2, 2⟩, ⟨0, 0, 0, 0, 2, 1⟩⟩,
    ⟨⟨-2, -1, 5, 1, -2⟩, ⟨0, 0, 0, 0, 1, 2⟩⟩
  ]⟩

def homogeneousCompletion3G6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 1, 0, 0⟩⟩,
    ⟨⟨-6, -12, -4, 4, 2⟩, ⟨0, 1, 1, 0, 0, 1⟩⟩,
    ⟨⟨-10, -34, -14, 12, 6⟩, ⟨0, 1, 0, 1, 0, 1⟩⟩,
    ⟨⟨-3, -3, 1, 1, 0⟩, ⟨0, 0, 2, 1, 0, 0⟩⟩,
    ⟨⟨-2, 16, 12, -6, -4⟩, ⟨0, 0, 2, 0, 0, 1⟩⟩,
    ⟨⟨4, 8, 1, -3, -1⟩, ⟨0, 0, 1, 2, 0, 0⟩⟩,
    ⟨⟨-5, -11, -4, 4, 2⟩, ⟨0, 0, 1, 1, 1, 0⟩⟩,
    ⟨⟨-3, -6, -2, 2, 1⟩, ⟨0, 0, 1, 1, 0, 1⟩⟩,
    ⟨⟨4, 22, 10, -8, -4⟩, ⟨0, 0, 1, 0, 1, 1⟩⟩,
    ⟨⟨-3, -14, -8, 5, 3⟩, ⟨0, 0, 1, 0, 0, 2⟩⟩,
    ⟨⟨-6, -12, -4, 4, 2⟩, ⟨0, 0, 0, 2, 0, 1⟩⟩,
    ⟨⟨-4, -28, -16, 10, 6⟩, ⟨0, 0, 0, 1, 1, 1⟩⟩,
    ⟨⟨0, 8, 6, -3, -2⟩, ⟨0, 0, 0, 1, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3G7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 2, 1, 1, 0⟩⟩,
    ⟨⟨-4, 0, 2, 0, 0⟩, ⟨0, 0, 2, 1, 0, 1⟩⟩,
    ⟨⟨6, 6, -2, -2, 0⟩, ⟨0, 0, 2, 0, 1, 1⟩⟩,
    ⟨⟨-3, -2, 1, 1, 0⟩, ⟨0, 0, 1, 2, 1, 0⟩⟩,
    ⟨⟨2, 6, 0, -2, 0⟩, ⟨0, 0, 1, 2, 0, 1⟩⟩,
    ⟨⟨3, 5, -1, -2, 0⟩, ⟨0, 0, 1, 1, 2, 0⟩⟩,
    ⟨⟨1, 3, 0, -1, 0⟩, ⟨0, 0, 1, 1, 1, 1⟩⟩,
    ⟨⟨3, 5, -1, -2, 0⟩, ⟨0, 0, 1, 1, 0, 2⟩⟩,
    ⟨⟨2, 6, 0, -2, 0⟩, ⟨0, 0, 1, 0, 2, 1⟩⟩,
    ⟨⟨-3, -2, 1, 1, 0⟩, ⟨0, 0, 1, 0, 1, 2⟩⟩,
    ⟨⟨6, 6, -2, -2, 0⟩, ⟨0, 0, 0, 2, 1, 1⟩⟩,
    ⟨⟨-4, 0, 2, 0, 0⟩, ⟨0, 0, 0, 1, 2, 1⟩⟩,
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 2⟩⟩
  ]⟩

def homogeneousCompletion3G : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3G1, homogeneousCompletion3G2, homogeneousCompletion3G3, homogeneousCompletion3G4, homogeneousCompletion3G5, homogeneousCompletion3G6, homogeneousCompletion3G7]

def homogeneousCompletion3M1_1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 0, 3, 0, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3M1_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M1_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M1_4 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨-1, 13, -7, -5, 2⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨-32, 20, 18, -6, -2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3M1_5 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨12, 9, -26, -6, 9⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨-12, 2, 48, 6, -20⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3M1_6 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M1_7 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨3, -5, 3, 2, -2⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
    ⟨⟨-18, -12, 12, 6, -2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-18, -38, -4, 14, 4⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3M2_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M2_2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-3, 3, 4, -1, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3M2_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M2_4 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨23, -13, -37, 5, 9⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨32, -20, -18, 6, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3M2_5 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M2_6 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨17, 10, -2, -3, -1⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨16, 144, 90, -52, -32⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3M2_7 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨-11, -6, 9, 1, -2⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
    ⟨⟨18, 12, -12, -6, 2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨26, 16, -8, -6, 0⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩
  ]⟩

def homogeneousCompletion3M3_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M3_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M3_3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, -3, -3, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3M3_4 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3M3_5 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨10, 13, -7, -5, 2⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨12, -2, -48, -6, 20⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3M3_6 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨16, 56, 24, -19, -10⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨-16, -144, -90, 52, 32⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3M3_7 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨-3, -22, -12, 8, 4⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
    ⟨⟨18, 38, 4, -14, -4⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-26, -16, 8, 6, 0⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩
  ]⟩

def homogeneousCompletion3M : Matrix (Fin 3) (Fin 7) RationalSparsePolynomial :=
  ![![homogeneousCompletion3M1_1, homogeneousCompletion3M1_2, homogeneousCompletion3M1_3, homogeneousCompletion3M1_4, homogeneousCompletion3M1_5, homogeneousCompletion3M1_6, homogeneousCompletion3M1_7], ![homogeneousCompletion3M2_1, homogeneousCompletion3M2_2, homogeneousCompletion3M2_3, homogeneousCompletion3M2_4, homogeneousCompletion3M2_5, homogeneousCompletion3M2_6, homogeneousCompletion3M2_7], ![homogeneousCompletion3M3_1, homogeneousCompletion3M3_2, homogeneousCompletion3M3_3, homogeneousCompletion3M3_4, homogeneousCompletion3M3_5, homogeneousCompletion3M3_6, homogeneousCompletion3M3_7]]

def homogeneousCompletion3N1_1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 2, 3, -1, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3N1_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N1_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N2_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N2_2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3N2_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N3_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N3_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N3_3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 0, -4, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3N4_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N4_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N4_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N5_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N5_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N5_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N6_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N6_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N6_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N7_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N7_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N7_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3N : Matrix (Fin 7) (Fin 3) RationalSparsePolynomial :=
  ![![homogeneousCompletion3N1_1, homogeneousCompletion3N1_2, homogeneousCompletion3N1_3], ![homogeneousCompletion3N2_1, homogeneousCompletion3N2_2, homogeneousCompletion3N2_3], ![homogeneousCompletion3N3_1, homogeneousCompletion3N3_2, homogeneousCompletion3N3_3], ![homogeneousCompletion3N4_1, homogeneousCompletion3N4_2, homogeneousCompletion3N4_3], ![homogeneousCompletion3N5_1, homogeneousCompletion3N5_2, homogeneousCompletion3N5_3], ![homogeneousCompletion3N6_1, homogeneousCompletion3N6_2, homogeneousCompletion3N6_3], ![homogeneousCompletion3N7_1, homogeneousCompletion3N7_2, homogeneousCompletion3N7_3]]

def homogeneousCompletion3EW1_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3EW1_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3EW1_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3EW2_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3EW2_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3EW2_3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3EW : Matrix (Fin 2) (Fin 3) RationalSparsePolynomial :=
  ![![homogeneousCompletion3EW1_1, homogeneousCompletion3EW1_2, homogeneousCompletion3EW1_3], ![homogeneousCompletion3EW2_1, homogeneousCompletion3EW2_2, homogeneousCompletion3EW2_3]]

def homogeneousCompletion3ForwardDen : Fin 7 → ℕ :=
  ![1, 1, 1, 11, 11, 11, 11]

def homogeneousCompletion3ReverseDen : Fin 3 → ℕ :=
  ![1, 1, 1]

def homogeneousCompletion3ResidualDen : Fin 3 → ℕ :=
  ![11, 11, 11]


def homogeneousCompletion3ForwardTerms (j : Fin 7) :=
  (List.ofFn fun i : Fin 3 => (homogeneousCompletion3M i j, homogeneousCompletion3Original i)) ++
    [(rationalSparseNeg (homogeneousCompletion3G j), rationalSparseOne)]

def homogeneousCompletion3ReverseTerms (j : Fin 3) :=
  (List.ofFn fun i : Fin 7 => (homogeneousCompletion3N i j, homogeneousCompletion3G i)) ++
    [(rationalSparseNeg (homogeneousCompletion3Original j), rationalSparseOne)]

def homogeneousCompletion3ResidualTerms (j : Fin 3) :=
  (if j.val = 2 then [(rationalSparseOne, rationalSparseOne)] else []) ++
    (List.ofFn fun i : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3M (Fin.last 2) i), homogeneousCompletion3N i j)) ++
    (List.ofFn fun i : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3EW i j), homogeneousCompletion3Original i.castSucc))

end Biunimodular.F11
