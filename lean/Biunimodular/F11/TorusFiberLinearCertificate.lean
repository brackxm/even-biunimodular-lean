/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusSparseZ5
import Biunimodular.F11.TorusOriginalGeneratorsData
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
namespace Biunimodular.F11

def torusFiberLinearCheck (p v : List RurInverseTerm7) (n : List ℤ) (d : ℤ) : Prop :=
  rurInverseSparseNormalize (rurInverseSparseSumProducts [
    (p, rurInverseSparseOne),
    (rurInverseSparseScale (-d) v, rurInverseSparseOne),
    (rurInverseSparseScale (-1) (rurInverseSparseOfZ5 n), rurInverseSparseOne)]) = []

instance (p v : List RurInverseTerm7) (n : List ℤ) (d : ℤ) :
    Decidable (torusFiberLinearCheck p v n d) := by
  unfold torusFiberLinearCheck
  infer_instance

theorem torusFiberLinearCheck_sound {R : Type*} [CommRing R]
    (p v : List RurInverseTerm7) (n : List ℤ) (d : ℤ)
    (h : torusFiberLinearCheck p v n d) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval p z1 z2 z3 z4 w z5 x =
      (d : R) * rurInverseSparseEval v z1 z2 z3 z4 w z5 x + integerCoefficientEval z5 n := by
  have hs := rurInverseSparseZeroCheck_sound _ h z1 z2 z3 z4 w z5 x
  have hone : rurInverseSparseEval rurInverseSparseOne z1 z2 z3 z4 w z5 x = 1 := by
    simp [rurInverseSparseOne, rurInverseSparseEval, rurInverseSparseTermEval]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hone, rurInverseSparseEval_scale, rurInverseSparseEval_ofZ5,
    Int.cast_neg, Int.cast_one, mul_one, add_zero] at hs
  linear_combination hs

def torusFiberCoordinates : Fin 9 → List RurInverseTerm7 :=
  ![[⟨1,⟨1,0,0,0,0,0,0⟩⟩], [⟨1,⟨0,1,0,0,0,0,0⟩⟩],
    [⟨1,⟨0,0,1,0,0,0,0⟩⟩], [⟨1,⟨0,0,0,1,0,0,0⟩⟩],
    [⟨1,⟨0,1,1,1,1,1,0⟩⟩], [⟨1,⟨1,0,1,1,1,1,0⟩⟩],
    [⟨1,⟨1,1,0,1,1,1,0⟩⟩], [⟨1,⟨1,1,1,0,1,1,0⟩⟩],
    [⟨1,⟨1,1,1,1,1,0,0⟩⟩]]

end Biunimodular.F11
