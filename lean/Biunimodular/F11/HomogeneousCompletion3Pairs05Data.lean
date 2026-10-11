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

def homogeneousCompletion3Pair4_6U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_6V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_6D1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair4_6D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair4_6D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair4_6D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨10, 34, 14, -12, -6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_6D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-4, 16, 20, -6, -6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_6D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, -6, 0, 2, 0⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_6D7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 4, 0, -1, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_6D : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair4_6D1, homogeneousCompletion3Pair4_6D2, homogeneousCompletion3Pair4_6D3, homogeneousCompletion3Pair4_6D4, homogeneousCompletion3Pair4_6D5, homogeneousCompletion3Pair4_6D6, homogeneousCompletion3Pair4_6D7]

def homogeneousCompletion3Pair4_6W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair4_6W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair4_6W : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair4_6W1, homogeneousCompletion3Pair4_6W2]


def homogeneousCompletion3Pair4_6SPTerms :=
  [(homogeneousCompletion3Pair4_6U, homogeneousCompletion3G 3), (rationalSparseNeg homogeneousCompletion3Pair4_6V, homogeneousCompletion3G 5)] ++
    (List.ofFn fun k : Fin 7 => (rationalSparseNeg (homogeneousCompletion3Pair4_6D k), homogeneousCompletion3G k))

def homogeneousCompletion3Pair4_6LastTerms :=
  [(homogeneousCompletion3Pair4_6U, homogeneousCompletion3M (Fin.last 2) 3),
    (rationalSparseNeg homogeneousCompletion3Pair4_6V, homogeneousCompletion3M (Fin.last 2) 5)] ++
    (List.ofFn fun k : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3Pair4_6D k), homogeneousCompletion3M (Fin.last 2) k)) ++
    (List.ofFn fun k : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3Pair4_6W k), homogeneousCompletion3Original k.castSucc))

def homogeneousCompletion3Pair4_7U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_7V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_7D1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair4_7D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair4_7D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair4_7D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨3, 2, -1, -1, 0⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
    ⟨⟨-3, -5, 1, 2, 0⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
    ⟨⟨25, -27, -46, 11, 12⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-6, -6, 2, 2, 0⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨4, 0, -2, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨-49, 44, 64, -16, -16⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_7D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-16, -2, 18, 0, -4⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-14, 10, 16, -4, -4⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨211, -120, -225, 45, 52⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_7D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨6, -6, -2, 2, 0⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-8, 6, 8, -2, -2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-123, 43, 171, -20, -42⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_7D7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-3, 1, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨4, -3, -4, 1, 1⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨-4, 2, 7, -1, -2⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨58, -20, -78, 10, 19⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_7D : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair4_7D1, homogeneousCompletion3Pair4_7D2, homogeneousCompletion3Pair4_7D3, homogeneousCompletion3Pair4_7D4, homogeneousCompletion3Pair4_7D5, homogeneousCompletion3Pair4_7D6, homogeneousCompletion3Pair4_7D7]

def homogeneousCompletion3Pair4_7W1 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨3, 7, -1, -3, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨4, -16, -18, 6, 6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_7W2 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨-7, -9, -1, 3, 1⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨-4, 16, 18, -6, -6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair4_7W : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair4_7W1, homogeneousCompletion3Pair4_7W2]


def homogeneousCompletion3Pair4_7SPTerms :=
  [(homogeneousCompletion3Pair4_7U, homogeneousCompletion3G 3), (rationalSparseNeg homogeneousCompletion3Pair4_7V, homogeneousCompletion3G 6)] ++
    (List.ofFn fun k : Fin 7 => (rationalSparseNeg (homogeneousCompletion3Pair4_7D k), homogeneousCompletion3G k))

def homogeneousCompletion3Pair4_7LastTerms :=
  [(homogeneousCompletion3Pair4_7U, homogeneousCompletion3M (Fin.last 2) 3),
    (rationalSparseNeg homogeneousCompletion3Pair4_7V, homogeneousCompletion3M (Fin.last 2) 6)] ++
    (List.ofFn fun k : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3Pair4_7D k), homogeneousCompletion3M (Fin.last 2) k)) ++
    (List.ofFn fun k : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3Pair4_7W k), homogeneousCompletion3Original k.castSucc))

def homogeneousCompletion3Pair5_6U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_6V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_6D1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair5_6D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair5_6D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair5_6D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨6, 30, 20, -10, -8⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_6D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨6, 12, 4, -4, -2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_6D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-4, -6, 10, 4, -4⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_6D7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, 1, -1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_6D : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair5_6D1, homogeneousCompletion3Pair5_6D2, homogeneousCompletion3Pair5_6D3, homogeneousCompletion3Pair5_6D4, homogeneousCompletion3Pair5_6D5, homogeneousCompletion3Pair5_6D6, homogeneousCompletion3Pair5_6D7]

def homogeneousCompletion3Pair5_6W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair5_6W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair5_6W : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair5_6W1, homogeneousCompletion3Pair5_6W2]


def homogeneousCompletion3Pair5_6SPTerms :=
  [(homogeneousCompletion3Pair5_6U, homogeneousCompletion3G 4), (rationalSparseNeg homogeneousCompletion3Pair5_6V, homogeneousCompletion3G 5)] ++
    (List.ofFn fun k : Fin 7 => (rationalSparseNeg (homogeneousCompletion3Pair5_6D k), homogeneousCompletion3G k))

def homogeneousCompletion3Pair5_6LastTerms :=
  [(homogeneousCompletion3Pair5_6U, homogeneousCompletion3M (Fin.last 2) 4),
    (rationalSparseNeg homogeneousCompletion3Pair5_6V, homogeneousCompletion3M (Fin.last 2) 5)] ++
    (List.ofFn fun k : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3Pair5_6D k), homogeneousCompletion3M (Fin.last 2) k)) ++
    (List.ofFn fun k : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3Pair5_6W k), homogeneousCompletion3Original k.castSucc))

def homogeneousCompletion3Pair5_7U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_7V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_7D1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair5_7D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair5_7D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion3Pair5_7D4 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨3, 2, -1, -1, 0⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
    ⟨⟨-3, -5, 1, 2, 0⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
    ⟨⟨21, -31, -40, 13, 10⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-6, -6, 2, 2, 0⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨4, 0, -2, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨-49, 44, 64, -16, -16⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_7D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-6, -6, 2, 2, 0⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-14, 10, 16, -4, -4⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨211, -120, -225, 45, 52⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_7D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, -6, 8, 4, -4⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-8, 6, 8, -2, -2⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-123, 43, 171, -20, -42⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_7D7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, -2, 0, 1, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨4, -3, -4, 1, 1⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨-4, 2, 7, -1, -2⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨58, -20, -78, 10, 19⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_7D : Fin 7 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair5_7D1, homogeneousCompletion3Pair5_7D2, homogeneousCompletion3Pair5_7D3, homogeneousCompletion3Pair5_7D4, homogeneousCompletion3Pair5_7D5, homogeneousCompletion3Pair5_7D6, homogeneousCompletion3Pair5_7D7]

def homogeneousCompletion3Pair5_7W1 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨3, 7, -1, -3, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨4, -16, -18, 6, 6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_7W2 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨-7, -9, -1, 3, 1⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨-4, 16, 18, -6, -6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion3Pair5_7W : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion3Pair5_7W1, homogeneousCompletion3Pair5_7W2]


def homogeneousCompletion3Pair5_7SPTerms :=
  [(homogeneousCompletion3Pair5_7U, homogeneousCompletion3G 4), (rationalSparseNeg homogeneousCompletion3Pair5_7V, homogeneousCompletion3G 6)] ++
    (List.ofFn fun k : Fin 7 => (rationalSparseNeg (homogeneousCompletion3Pair5_7D k), homogeneousCompletion3G k))

def homogeneousCompletion3Pair5_7LastTerms :=
  [(homogeneousCompletion3Pair5_7U, homogeneousCompletion3M (Fin.last 2) 4),
    (rationalSparseNeg homogeneousCompletion3Pair5_7V, homogeneousCompletion3M (Fin.last 2) 6)] ++
    (List.ofFn fun k : Fin 7 =>
      (rationalSparseNeg (homogeneousCompletion3Pair5_7D k), homogeneousCompletion3M (Fin.last 2) k)) ++
    (List.ofFn fun k : Fin 2 =>
      (rationalSparseNeg (homogeneousCompletion3Pair5_7W k), homogeneousCompletion3Original k.castSucc))

end Biunimodular.F11
