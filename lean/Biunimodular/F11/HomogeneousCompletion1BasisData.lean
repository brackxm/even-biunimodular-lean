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

def homogeneousCompletion1Original1 : RationalSparsePolynomial :=
  ⟨1, by decide, homogeneousRegularOriginal1⟩

def homogeneousCompletion1Original : Fin 1 → RationalSparsePolynomial :=
  ![homogeneousCompletion1Original1]

def homogeneousCompletion1G1 : RationalSparsePolynomial :=
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

def homogeneousCompletion1G : Fin 1 → RationalSparsePolynomial :=
  ![homogeneousCompletion1G1]

def homogeneousCompletion1M1_1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 0, 3, 0, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion1M : Matrix (Fin 1) (Fin 1) RationalSparsePolynomial :=
  ![![homogeneousCompletion1M1_1]]

def homogeneousCompletion1N1_1 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-1, 2, 3, -1, -1⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion1N : Matrix (Fin 1) (Fin 1) RationalSparsePolynomial :=
  ![![homogeneousCompletion1N1_1]]

def homogeneousCompletion1EW : Matrix (Fin 0) (Fin 1) RationalSparsePolynomial :=
  ![]

def homogeneousCompletion1ForwardDen : Fin 1 → ℕ :=
  ![1]

def homogeneousCompletion1ReverseDen : Fin 1 → ℕ :=
  ![1]

def homogeneousCompletion1ResidualDen : Fin 1 → ℕ :=
  ![1]


def homogeneousCompletion1ForwardTerms (j : Fin 1) :=
  (List.ofFn fun i : Fin 1 => (homogeneousCompletion1M i j, homogeneousCompletion1Original i)) ++
    [(rationalSparseNeg (homogeneousCompletion1G j), rationalSparseOne)]

def homogeneousCompletion1ReverseTerms (j : Fin 1) :=
  (List.ofFn fun i : Fin 1 => (homogeneousCompletion1N i j, homogeneousCompletion1G i)) ++
    [(rationalSparseNeg (homogeneousCompletion1Original j), rationalSparseOne)]

def homogeneousCompletion1ResidualTerms (j : Fin 1) :=
  (if j.val = 0 then [(rationalSparseOne, rationalSparseOne)] else []) ++
    (List.ofFn fun i : Fin 1 =>
      (rationalSparseNeg (homogeneousCompletion1M (Fin.last 0) i), homogeneousCompletion1N i j)) ++
    (List.ofFn fun i : Fin 0 =>
      (rationalSparseNeg (homogeneousCompletion1EW i j), homogeneousCompletion1Original i.castSucc))

end Biunimodular.F11
