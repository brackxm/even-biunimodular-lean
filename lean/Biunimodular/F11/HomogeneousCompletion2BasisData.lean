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

def homogeneousCompletion2Original1 : RationalSparsePolynomial :=
  ⟨1, by decide, homogeneousRegularOriginal1⟩

def homogeneousCompletion2Original2 : RationalSparsePolynomial :=
  ⟨1, by decide, homogeneousRegularOriginal2⟩

def homogeneousCompletion2Original : Fin 2 → RationalSparsePolynomial :=
  ![homogeneousCompletion2Original1, homogeneousCompletion2Original2]

def homogeneousCompletion2G1 : RationalSparsePolynomial :=
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

def homogeneousCompletion2G2 : RationalSparsePolynomial :=
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

def homogeneousCompletion2G3 : RationalSparsePolynomial :=
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

def homogeneousCompletion2G : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion2G1, homogeneousCompletion2G2, homogeneousCompletion2G3]

def homogeneousCompletion2M1_1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 0, 3, 0, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2M1_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2M1_3 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨-1, 13, -7, -5, 2⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨-32, 20, 18, -6, -2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion2M2_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2M2_2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-3, 3, 4, -1, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2M2_3 : RationalSparsePolynomial :=
  ⟨11, by decide, [
    ⟨⟨23, -13, -37, 5, 9⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨32, -20, -18, 6, 2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion2M : Matrix (Fin 2) (Fin 3) RationalSparsePolynomial :=
  ![![homogeneousCompletion2M1_1, homogeneousCompletion2M1_2, homogeneousCompletion2M1_3], ![homogeneousCompletion2M2_1, homogeneousCompletion2M2_2, homogeneousCompletion2M2_3]]

def homogeneousCompletion2N1_1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 2, 3, -1, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2N1_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2N2_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2N2_2 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion2N3_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2N3_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2N : Matrix (Fin 3) (Fin 2) RationalSparsePolynomial :=
  ![![homogeneousCompletion2N1_1, homogeneousCompletion2N1_2], ![homogeneousCompletion2N2_1, homogeneousCompletion2N2_2], ![homogeneousCompletion2N3_1, homogeneousCompletion2N3_2]]

def homogeneousCompletion2EW1_1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2EW1_2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion2EW : Matrix (Fin 1) (Fin 2) RationalSparsePolynomial :=
  ![![homogeneousCompletion2EW1_1, homogeneousCompletion2EW1_2]]

def homogeneousCompletion2ForwardDen : Fin 3 → ℕ :=
  ![1, 1, 11]

def homogeneousCompletion2ReverseDen : Fin 2 → ℕ :=
  ![1, 1]

def homogeneousCompletion2ResidualDen : Fin 2 → ℕ :=
  ![11, 11]


def homogeneousCompletion2ForwardTerms (j : Fin 3) :=
  (List.ofFn fun i : Fin 2 => (homogeneousCompletion2M i j, homogeneousCompletion2Original i)) ++
    [(rationalSparseNeg (homogeneousCompletion2G j), rationalSparseOne)]

def homogeneousCompletion2ReverseTerms (j : Fin 2) :=
  (List.ofFn fun i : Fin 3 => (homogeneousCompletion2N i j, homogeneousCompletion2G i)) ++
    [(rationalSparseNeg (homogeneousCompletion2Original j), rationalSparseOne)]

def homogeneousCompletion2ResidualTerms (j : Fin 2) :=
  (if j.val = 1 then [(rationalSparseOne, rationalSparseOne)] else []) ++
    (List.ofFn fun i : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion2M (Fin.last 1) i), homogeneousCompletion2N i j)) ++
    (List.ofFn fun i : Fin 1 =>
      (rationalSparseNeg (homogeneousCompletion2EW i j), homogeneousCompletion2Original i.castSucc))

end Biunimodular.F11
