/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusMacaulayColumnSemantics

set_option autoImplicit false
namespace Biunimodular.F11

def torusMacaulayColumnProducts
    (columns : Array TorusMacaulayRow) (polynomials : Array (List RurInverseTerm7))
    (constants : Array (List ℤ)) (global : List RurInverseTerm7) (j : ℕ) :=
  ((columns[j]?.getD []).map fun e =>
    (rurInverseSparseOfZ5 e.2, polynomials[e.1]?.getD [])) ++
      [(rurInverseSparseOfZ5 (constants[j]?.getD []), global)]

def torusMacaulayColumnZeroCheck
    (columns : Array TorusMacaulayRow) (polynomials : Array (List RurInverseTerm7))
    (constants : Array (List ℤ)) (global : List RurInverseTerm7)
    (parents : List (List RurInverseTerm7 × List RurInverseTerm7)) (j : ℕ) : Prop :=
  rurInverseSparseNormalize (rurInverseSparseSumProducts
    (torusMacaulayColumnProducts columns polynomials constants global j ++ parents)) = []

instance (columns : Array TorusMacaulayRow) (polynomials : Array (List RurInverseTerm7))
    (constants : Array (List ℤ)) (global : List RurInverseTerm7)
    (parents : List (List RurInverseTerm7 × List RurInverseTerm7)) (j : ℕ) :
    Decidable (torusMacaulayColumnZeroCheck columns polynomials constants global parents j) := by
  unfold torusMacaulayColumnZeroCheck
  infer_instance

theorem torusMacaulayColumnZeroCheck_sound
    {R : Type*} [CommRing R]
    (columns : Array TorusMacaulayRow) (polynomials : Array (List RurInverseTerm7))
    (constants : Array (List ℤ)) (global : List RurInverseTerm7)
    (parents : List (List RurInverseTerm7 × List RurInverseTerm7)) (j : ℕ)
    (h : torusMacaulayColumnZeroCheck columns polynomials constants global parents j)
    (z1 z2 z3 z4 w z5 x : R)
    (hparents : ∀ p ∈ parents, rurInverseSparseEval p.2 z1 z2 z3 z4 w z5 x = 0) :
    ((columns[j]?.getD []).map fun e => integerCoefficientEval z5 e.2 *
      rurInverseSparseEval (polynomials[e.1]?.getD []) z1 z2 z3 z4 w z5 x).sum +
      integerCoefficientEval z5 (constants[j]?.getD []) *
        rurInverseSparseEval global z1 z2 z3 z4 w z5 x = 0 := by
  have hp : (parents.map fun p => rurInverseSparseEval p.1 z1 z2 z3 z4 w z5 x *
      rurInverseSparseEval p.2 z1 z2 z3 z4 w z5 x).sum = 0 := by
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rw [hparents p hp, mul_zero]
  have hs := rurInverseSparseZeroCheck_sound _ h z1 z2 z3 z4 w z5 x
  simp only [List.map_append, List.sum_append, hp, add_zero] at hs
  simpa only [torusMacaulayColumnProducts, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, rurInverseSparseEval_ofZ5] using hs

end Biunimodular.F11
