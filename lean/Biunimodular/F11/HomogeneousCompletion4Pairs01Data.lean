/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair1_2U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_2V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_2D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-6, 6, 8, -2, -2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_2D2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_2D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D4 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 1, -1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_2D6 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D7 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D8 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D9 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D10 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D11 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D12 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D13 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D14 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D15 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2D : Fin 15 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair1_2D1, homogeneousCompletion4Pair1_2D2, homogeneousCompletion4Pair1_2D3, homogeneousCompletion4Pair1_2D4, homogeneousCompletion4Pair1_2D5, homogeneousCompletion4Pair1_2D6, homogeneousCompletion4Pair1_2D7, homogeneousCompletion4Pair1_2D8, homogeneousCompletion4Pair1_2D9, homogeneousCompletion4Pair1_2D10, homogeneousCompletion4Pair1_2D11, homogeneousCompletion4Pair1_2D12, homogeneousCompletion4Pair1_2D13, homogeneousCompletion4Pair1_2D14, homogeneousCompletion4Pair1_2D15]

def homogeneousCompletion4Pair1_2W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2W3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_2W : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair1_2W1, homogeneousCompletion4Pair1_2W2, homogeneousCompletion4Pair1_2W3]


def homogeneousCompletion4Pair1_2SPTerms :=
  [(homogeneousCompletion4Pair1_2U, homogeneousCompletion4G 0), (rationalSparseNeg homogeneousCompletion4Pair1_2V, homogeneousCompletion4G 1)] ++
    (List.ofFn fun k : Fin 15 => (rationalSparseNeg (homogeneousCompletion4Pair1_2D k), homogeneousCompletion4G k))

def homogeneousCompletion4Pair1_2LastTerms :=
  [(homogeneousCompletion4Pair1_2U, homogeneousCompletion4M (Fin.last 3) 0),
    (rationalSparseNeg homogeneousCompletion4Pair1_2V, homogeneousCompletion4M (Fin.last 3) 1)] ++
    (List.ofFn fun k : Fin 15 =>
      (rationalSparseNeg (homogeneousCompletion4Pair1_2D k), homogeneousCompletion4M (Fin.last 3) k)) ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion4Pair1_2W k), homogeneousCompletion4Original k.castSucc))

def homogeneousCompletion4Pair1_3U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_3V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_3D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, -6, -6, 2, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_3D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_3D4 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D5 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 4, 0, -1, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_3D7 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D8 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D9 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D10 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D11 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D12 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D13 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D14 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D15 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3D : Fin 15 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair1_3D1, homogeneousCompletion4Pair1_3D2, homogeneousCompletion4Pair1_3D3, homogeneousCompletion4Pair1_3D4, homogeneousCompletion4Pair1_3D5, homogeneousCompletion4Pair1_3D6, homogeneousCompletion4Pair1_3D7, homogeneousCompletion4Pair1_3D8, homogeneousCompletion4Pair1_3D9, homogeneousCompletion4Pair1_3D10, homogeneousCompletion4Pair1_3D11, homogeneousCompletion4Pair1_3D12, homogeneousCompletion4Pair1_3D13, homogeneousCompletion4Pair1_3D14, homogeneousCompletion4Pair1_3D15]

def homogeneousCompletion4Pair1_3W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3W3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_3W : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair1_3W1, homogeneousCompletion4Pair1_3W2, homogeneousCompletion4Pair1_3W3]


def homogeneousCompletion4Pair1_3SPTerms :=
  [(homogeneousCompletion4Pair1_3U, homogeneousCompletion4G 0), (rationalSparseNeg homogeneousCompletion4Pair1_3V, homogeneousCompletion4G 2)] ++
    (List.ofFn fun k : Fin 15 => (rationalSparseNeg (homogeneousCompletion4Pair1_3D k), homogeneousCompletion4G k))

def homogeneousCompletion4Pair1_3LastTerms :=
  [(homogeneousCompletion4Pair1_3U, homogeneousCompletion4M (Fin.last 3) 0),
    (rationalSparseNeg homogeneousCompletion4Pair1_3V, homogeneousCompletion4M (Fin.last 3) 2)] ++
    (List.ofFn fun k : Fin 15 =>
      (rationalSparseNeg (homogeneousCompletion4Pair1_3D k), homogeneousCompletion4M (Fin.last 3) k)) ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion4Pair1_3W k), homogeneousCompletion4Original k.castSucc))

def homogeneousCompletion4Pair1_4U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_4V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_4D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 2, -6, 0, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_4D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_4D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, -6, 3, 2, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_4D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 2, -3, -1, 1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_4D7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-2, 1, 4, 0, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_4D8 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D9 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D10 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D11 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D12 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D13 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D14 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D15 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4D : Fin 15 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair1_4D1, homogeneousCompletion4Pair1_4D2, homogeneousCompletion4Pair1_4D3, homogeneousCompletion4Pair1_4D4, homogeneousCompletion4Pair1_4D5, homogeneousCompletion4Pair1_4D6, homogeneousCompletion4Pair1_4D7, homogeneousCompletion4Pair1_4D8, homogeneousCompletion4Pair1_4D9, homogeneousCompletion4Pair1_4D10, homogeneousCompletion4Pair1_4D11, homogeneousCompletion4Pair1_4D12, homogeneousCompletion4Pair1_4D13, homogeneousCompletion4Pair1_4D14, homogeneousCompletion4Pair1_4D15]

def homogeneousCompletion4Pair1_4W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4W3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_4W : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair1_4W1, homogeneousCompletion4Pair1_4W2, homogeneousCompletion4Pair1_4W3]


def homogeneousCompletion4Pair1_4SPTerms :=
  [(homogeneousCompletion4Pair1_4U, homogeneousCompletion4G 0), (rationalSparseNeg homogeneousCompletion4Pair1_4V, homogeneousCompletion4G 3)] ++
    (List.ofFn fun k : Fin 15 => (rationalSparseNeg (homogeneousCompletion4Pair1_4D k), homogeneousCompletion4G k))

def homogeneousCompletion4Pair1_4LastTerms :=
  [(homogeneousCompletion4Pair1_4U, homogeneousCompletion4M (Fin.last 3) 0),
    (rationalSparseNeg homogeneousCompletion4Pair1_4V, homogeneousCompletion4M (Fin.last 3) 3)] ++
    (List.ofFn fun k : Fin 15 =>
      (rationalSparseNeg (homogeneousCompletion4Pair1_4D k), homogeneousCompletion4M (Fin.last 3) k)) ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion4Pair1_4W k), homogeneousCompletion4Original k.castSucc))

def homogeneousCompletion4Pair1_5U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_5V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_5D1 : RationalSparsePolynomial :=
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

def homogeneousCompletion4Pair1_5D2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 4, -6, -2, 2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-5, -15, 13, -1, 0⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_5D3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-2, 0, 6, 0, -2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-12, 0, 16, 0, -4⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_5D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 6, -6, -2, 2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-12, 12, 4, -4, 0⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_5D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩,
    ⟨⟨-1, -1, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨1, -2, -1, 1, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨1, 2, -3, -1, 1⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨-27, -20, 71, 6, -21⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_5D6 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5D7 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5D8 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-12, -12, 42, 2, -12⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_5D9 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨10, 2, -22, 0, 6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair1_5D10 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5D11 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5D12 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5D13 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5D14 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5D15 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5D : Fin 15 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair1_5D1, homogeneousCompletion4Pair1_5D2, homogeneousCompletion4Pair1_5D3, homogeneousCompletion4Pair1_5D4, homogeneousCompletion4Pair1_5D5, homogeneousCompletion4Pair1_5D6, homogeneousCompletion4Pair1_5D7, homogeneousCompletion4Pair1_5D8, homogeneousCompletion4Pair1_5D9, homogeneousCompletion4Pair1_5D10, homogeneousCompletion4Pair1_5D11, homogeneousCompletion4Pair1_5D12, homogeneousCompletion4Pair1_5D13, homogeneousCompletion4Pair1_5D14, homogeneousCompletion4Pair1_5D15]

def homogeneousCompletion4Pair1_5W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5W3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair1_5W : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair1_5W1, homogeneousCompletion4Pair1_5W2, homogeneousCompletion4Pair1_5W3]


def homogeneousCompletion4Pair1_5SPTerms :=
  [(homogeneousCompletion4Pair1_5U, homogeneousCompletion4G 0), (rationalSparseNeg homogeneousCompletion4Pair1_5V, homogeneousCompletion4G 4)] ++
    (List.ofFn fun k : Fin 15 => (rationalSparseNeg (homogeneousCompletion4Pair1_5D k), homogeneousCompletion4G k))

def homogeneousCompletion4Pair1_5LastTerms :=
  [(homogeneousCompletion4Pair1_5U, homogeneousCompletion4M (Fin.last 3) 0),
    (rationalSparseNeg homogeneousCompletion4Pair1_5V, homogeneousCompletion4M (Fin.last 3) 4)] ++
    (List.ofFn fun k : Fin 15 =>
      (rationalSparseNeg (homogeneousCompletion4Pair1_5D k), homogeneousCompletion4M (Fin.last 3) k)) ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion4Pair1_5W k), homogeneousCompletion4Original k.castSucc))

end Biunimodular.F11
