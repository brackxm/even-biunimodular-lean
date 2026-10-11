/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion3Pair1_2U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_2V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_2D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-6, 6, 8, -2, -2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_2D2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_2D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_2D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 1, -1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_2D5 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_2D6 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_2D7 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_2D : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair1_2D1, homogeneousCompletion3Pair1_2D2, homogeneousCompletion3Pair1_2D3, homogeneousCompletion3Pair1_2D4, homogeneousCompletion3Pair1_2D5, homogeneousCompletion3Pair1_2D6, homogeneousCompletion3Pair1_2D7]

def homogeneousCompletion3Pair1_2W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_2W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_2W : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair1_2W1, homogeneousCompletion3Pair1_2W2]


def homogeneousCompletion3Pair1_2SPTerms :=
  [(homogeneousCompletion3Pair1_2U, homogeneousCompletion3G 0), (rationalSparseNeg homogeneousCompletion3Pair1_2V, homogeneousCompletion3G 1)] ++
    (List.ofFn fun k : Fin 7 => (rationalSparseNeg (homogeneousCompletion3Pair1_2D k), homogeneousCompletion3G k))

def homogeneousCompletion3Pair1_2LastTerms :=
  [(homogeneousCompletion3Pair1_2U, homogeneousCompletion3M (Fin.last 2) 0),
    (rationalSparseNeg homogeneousCompletion3Pair1_2V, homogeneousCompletion3M (Fin.last 2) 1)] ++
    (List.ofFn fun k : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3Pair1_2D k), homogeneousCompletion3M (Fin.last 2) k)) ++
    (List.ofFn fun k : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3Pair1_2W k), homogeneousCompletion3Original k.castSucc))

def homogeneousCompletion3Pair1_3U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_3V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_3D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, -6, -6, 2, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_3D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_3D3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_3D4 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_3D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 4, 0, -1, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_3D6 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_3D7 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_3D : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair1_3D1, homogeneousCompletion3Pair1_3D2, homogeneousCompletion3Pair1_3D3, homogeneousCompletion3Pair1_3D4, homogeneousCompletion3Pair1_3D5, homogeneousCompletion3Pair1_3D6, homogeneousCompletion3Pair1_3D7]

def homogeneousCompletion3Pair1_3W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_3W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_3W : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair1_3W1, homogeneousCompletion3Pair1_3W2]


def homogeneousCompletion3Pair1_3SPTerms :=
  [(homogeneousCompletion3Pair1_3U, homogeneousCompletion3G 0), (rationalSparseNeg homogeneousCompletion3Pair1_3V, homogeneousCompletion3G 2)] ++
    (List.ofFn fun k : Fin 7 => (rationalSparseNeg (homogeneousCompletion3Pair1_3D k), homogeneousCompletion3G k))

def homogeneousCompletion3Pair1_3LastTerms :=
  [(homogeneousCompletion3Pair1_3U, homogeneousCompletion3M (Fin.last 2) 0),
    (rationalSparseNeg homogeneousCompletion3Pair1_3V, homogeneousCompletion3M (Fin.last 2) 2)] ++
    (List.ofFn fun k : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3Pair1_3D k), homogeneousCompletion3M (Fin.last 2) k)) ++
    (List.ofFn fun k : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3Pair1_3W k), homogeneousCompletion3Original k.castSucc))

def homogeneousCompletion3Pair1_4U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_4V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_4D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨10, -4, -16, 2, 4⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨3, -1, -1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
    ⟨⟨6, -6, -8, 2, 2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-4, 3, 4, -1, -1⟩, ⟨0, 0, 0, 2, 0, 0⟩⟩,
    ⟨⟨4, -2, -7, 1, 2⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
    ⟨⟨-4, 2, 2, 0, -1⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨4, 0, -8, 0, 2⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨1, 1, -5, 1, 1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_4D2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 6, -6, -2, 2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨2, 4, -6, -2, 2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨3, 9, -31, -5, 12⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_4D3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-2, 0, 6, 0, -2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-12, 0, 16, 0, -4⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_4D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩,
    ⟨⟨-1, -1, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨1, -2, -1, 1, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨1, 2, -3, -1, 1⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨-1, -4, 5, 4, -3⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_4D5 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_4D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨4, -2, -4, 2, 0⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_4D7 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_4D : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair1_4D1, homogeneousCompletion3Pair1_4D2, homogeneousCompletion3Pair1_4D3, homogeneousCompletion3Pair1_4D4, homogeneousCompletion3Pair1_4D5, homogeneousCompletion3Pair1_4D6, homogeneousCompletion3Pair1_4D7]

def homogeneousCompletion3Pair1_4W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_4W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_4W : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair1_4W1, homogeneousCompletion3Pair1_4W2]


def homogeneousCompletion3Pair1_4SPTerms :=
  [(homogeneousCompletion3Pair1_4U, homogeneousCompletion3G 0), (rationalSparseNeg homogeneousCompletion3Pair1_4V, homogeneousCompletion3G 3)] ++
    (List.ofFn fun k : Fin 7 => (rationalSparseNeg (homogeneousCompletion3Pair1_4D k), homogeneousCompletion3G k))

def homogeneousCompletion3Pair1_4LastTerms :=
  [(homogeneousCompletion3Pair1_4U, homogeneousCompletion3M (Fin.last 2) 0),
    (rationalSparseNeg homogeneousCompletion3Pair1_4V, homogeneousCompletion3M (Fin.last 2) 3)] ++
    (List.ofFn fun k : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3Pair1_4D k), homogeneousCompletion3M (Fin.last 2) k)) ++
    (List.ofFn fun k : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3Pair1_4W k), homogeneousCompletion3Original k.castSucc))

def homogeneousCompletion3Pair1_5U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨4, 4, -6, -2, 2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨1, 2, 0, -1, 0⟩, ⟨0, 0, 2, 0, 0, 0⟩⟩,
    ⟨⟨1, -4, -1, 2, 0⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
    ⟨⟨1, 4, -2, -2, 1⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
    ⟨⟨-2, -8, 19, 7, -9⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨2, 8, -4, -4, 2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨0, -2, 4, 2, -2⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨10, 25, -41, -17, 18⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_5D3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨6, 6, -16, -4, 6⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨0, -6, 8, 4, -4⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨4, 12, -18, -8, 8⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨28, 69, -120, -48, 53⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, -2, -1, 1, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨2, 16, -16, -10, 8⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩,
    ⟨⟨-1, -1, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨1, 2, -3, -1, 1⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨13, -10, -11, 6, 1⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨4, 32, -40, -22, 20⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5D7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨5, 1, -9, -1, 3⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5D : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair1_5D1, homogeneousCompletion3Pair1_5D2, homogeneousCompletion3Pair1_5D3, homogeneousCompletion3Pair1_5D4, homogeneousCompletion3Pair1_5D5, homogeneousCompletion3Pair1_5D6, homogeneousCompletion3Pair1_5D7]

def homogeneousCompletion3Pair1_5W1 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨6, -1, -24, -3, 10⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair1_5W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair1_5W : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair1_5W1, homogeneousCompletion3Pair1_5W2]


def homogeneousCompletion3Pair1_5SPTerms :=
  [(homogeneousCompletion3Pair1_5U, homogeneousCompletion3G 0), (rationalSparseNeg homogeneousCompletion3Pair1_5V, homogeneousCompletion3G 4)] ++
    (List.ofFn fun k : Fin 7 => (rationalSparseNeg (homogeneousCompletion3Pair1_5D k), homogeneousCompletion3G k))

def homogeneousCompletion3Pair1_5LastTerms :=
  [(homogeneousCompletion3Pair1_5U, homogeneousCompletion3M (Fin.last 2) 0),
    (rationalSparseNeg homogeneousCompletion3Pair1_5V, homogeneousCompletion3M (Fin.last 2) 4)] ++
    (List.ofFn fun k : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3Pair1_5D k), homogeneousCompletion3M (Fin.last 2) k)) ++
    (List.ofFn fun k : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3Pair1_5W k), homogeneousCompletion3Original k.castSucc))

end Biunimodular.F11
