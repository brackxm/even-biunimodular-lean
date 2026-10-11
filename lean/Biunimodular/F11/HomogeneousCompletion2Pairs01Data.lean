/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion2BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion2Pair1_2U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_2V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_2D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-6, 6, 8, -2, -2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_2D2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 0, -6, 0, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_2D3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 1, -1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_2D : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion2Pair1_2D1, homogeneousCompletion2Pair1_2D2, homogeneousCompletion2Pair1_2D3]

def homogeneousCompletion2Pair1_2W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2Pair1_2W : Fin 1 → RationalSparsePolynomial :=
  ![homogeneousCompletion2Pair1_2W1]


def homogeneousCompletion2Pair1_2SPTerms :=
  [(homogeneousCompletion2Pair1_2U, homogeneousCompletion2G 0), (rationalSparseNeg homogeneousCompletion2Pair1_2V, homogeneousCompletion2G 1)] ++
    (List.ofFn fun k : Fin 3 => (rationalSparseNeg (homogeneousCompletion2Pair1_2D k), homogeneousCompletion2G k))

def homogeneousCompletion2Pair1_2LastTerms :=
  [(homogeneousCompletion2Pair1_2U, homogeneousCompletion2M (Fin.last 1) 0),
    (rationalSparseNeg homogeneousCompletion2Pair1_2V, homogeneousCompletion2M (Fin.last 1) 1)] ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion2Pair1_2D k), homogeneousCompletion2M (Fin.last 1) k)) ++
    (List.ofFn fun k : Fin 1 =>
      (rationalSparseNeg (homogeneousCompletion2Pair1_2W k), homogeneousCompletion2Original k.castSucc))

def homogeneousCompletion2Pair1_3U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_3V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_3D1 : RationalSparsePolynomial :=
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

def homogeneousCompletion2Pair1_3D2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 6, -6, -2, 2⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨-2, 0, 6, 0, -2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨2, 4, -6, -2, 2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨7, 17, -31, -9, 12⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_3D3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 1, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩,
    ⟨⟨-1, -1, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨1, -2, -1, 1, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨1, 2, -3, -1, 1⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨-1, -4, 5, 4, -3⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_3D : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion2Pair1_3D1, homogeneousCompletion2Pair1_3D2, homogeneousCompletion2Pair1_3D3]

def homogeneousCompletion2Pair1_3W1 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨16, -10, -9, 3, 1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair1_3W : Fin 1 → RationalSparsePolynomial :=
  ![homogeneousCompletion2Pair1_3W1]


def homogeneousCompletion2Pair1_3SPTerms :=
  [(homogeneousCompletion2Pair1_3U, homogeneousCompletion2G 0), (rationalSparseNeg homogeneousCompletion2Pair1_3V, homogeneousCompletion2G 2)] ++
    (List.ofFn fun k : Fin 3 => (rationalSparseNeg (homogeneousCompletion2Pair1_3D k), homogeneousCompletion2G k))

def homogeneousCompletion2Pair1_3LastTerms :=
  [(homogeneousCompletion2Pair1_3U, homogeneousCompletion2M (Fin.last 1) 0),
    (rationalSparseNeg homogeneousCompletion2Pair1_3V, homogeneousCompletion2M (Fin.last 1) 2)] ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion2Pair1_3D k), homogeneousCompletion2M (Fin.last 1) k)) ++
    (List.ofFn fun k : Fin 1 =>
      (rationalSparseNeg (homogeneousCompletion2Pair1_3W k), homogeneousCompletion2Original k.castSucc))

def homogeneousCompletion2Pair2_3U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair2_3V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair2_3D1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨16, -10, -24, 4, 6⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨3, -1, -1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
    ⟨⟨6, -6, -8, 2, 2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-4, 3, 4, -1, -1⟩, ⟨0, 0, 0, 2, 0, 0⟩⟩,
    ⟨⟨4, -2, -7, 1, 2⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
    ⟨⟨-4, 2, 2, 0, -1⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨4, 0, -8, 0, 2⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨1, 1, -5, 1, 1⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion2Pair2_3D2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-2, 6, 0, -2, 0⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨-2, 0, 6, 0, -2⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨2, 4, -6, -2, 2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨7, 17, -31, -9, 12⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion2Pair2_3D3 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-3, 0, 1, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩,
    ⟨⟨-1, -1, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨1, -2, -1, 1, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨1, 2, -3, -1, 1⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨-1, -4, 5, 4, -3⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion2Pair2_3D : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion2Pair2_3D1, homogeneousCompletion2Pair2_3D2, homogeneousCompletion2Pair2_3D3]

def homogeneousCompletion2Pair2_3W1 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨16, -10, -9, 3, 1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2Pair2_3W : Fin 1 → RationalSparsePolynomial :=
  ![homogeneousCompletion2Pair2_3W1]


def homogeneousCompletion2Pair2_3SPTerms :=
  [(homogeneousCompletion2Pair2_3U, homogeneousCompletion2G 1), (rationalSparseNeg homogeneousCompletion2Pair2_3V, homogeneousCompletion2G 2)] ++
    (List.ofFn fun k : Fin 3 => (rationalSparseNeg (homogeneousCompletion2Pair2_3D k), homogeneousCompletion2G k))

def homogeneousCompletion2Pair2_3LastTerms :=
  [(homogeneousCompletion2Pair2_3U, homogeneousCompletion2M (Fin.last 1) 1),
    (rationalSparseNeg homogeneousCompletion2Pair2_3V, homogeneousCompletion2M (Fin.last 1) 2)] ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion2Pair2_3D k), homogeneousCompletion2M (Fin.last 1) k)) ++
    (List.ofFn fun k : Fin 1 =>
      (rationalSparseNeg (homogeneousCompletion2Pair2_3W k), homogeneousCompletion2Original k.castSucc))

end Biunimodular.F11
