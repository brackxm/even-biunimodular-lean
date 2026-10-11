/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Biunimodular.F11.TorusMacaulayCriterion
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace Biunimodular.F11

abbrev TorusMacaulayRow := List (ℕ × List ℤ)

/-- The proposed inverse is data; malformed entries become zero and cannot
establish an incorrect matrix identity because the identity is checked. -/
def torusMacaulayParseIntegerRow (text : String) : Array ℤ :=
  (text.splitOn " ").toArray.map fun s => s.toInt?.getD 0

def torusMacaulaySparseMatrix {R : Type*} [CommRing R]
    (n : ℕ) (rows : Array TorusMacaulayRow) (x : R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ((rows[i.val]?.getD []).map fun e =>
    if e.1 = j.val then integerCoefficientEval x e.2 else 0).sum

def torusMacaulayIntegerMatrix {R : Type*} [CommRing R]
    (n : ℕ) (rows : Array (Array ℤ)) : Matrix (Fin n) (Fin n) R :=
  fun i j => (((rows[i.val]?.getD #[])[j.val]?.getD 0 : ℤ) : R)

def torusMacaulayModularCheck (n p a : ℕ)
    (rows : Array TorusMacaulayRow) (inverse : Array (Array ℤ)) : Prop :=
  (∀ i : Fin n, ∀ e ∈ rows[i.val]?.getD [], e.1 < n) ∧
  ∀ i j : Fin n, ((rows[i.val]?.getD []).map fun e =>
    integerCoefficientEval (a : ZMod p) e.2 *
      (((inverse[e.1]?.getD #[])[j.val]?.getD 0 : ℤ) : ZMod p)).sum = if i = j then 1 else 0

instance (n p a : ℕ) (rows : Array TorusMacaulayRow) (inverse : Array (Array ℤ)) :
    Decidable (torusMacaulayModularCheck n p a rows inverse) := by
  unfold torusMacaulayModularCheck
  infer_instance

theorem torusMacaulay_sparse_row_dot
    {R : Type*} [CommRing R] (n : ℕ) (row : TorusMacaulayRow)
    (hbound : ∀ e ∈ row, e.1 < n) (x : R) (v : ℕ → R) :
    (∑ k : Fin n, (row.map fun e =>
      if e.1 = k.val then integerCoefficientEval x e.2 else 0).sum * v k.val) =
      (row.map fun e => integerCoefficientEval x e.2 * v e.1).sum := by
  induction row with
  | nil => simp
  | cons e row ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    rw [ih (fun q hq => hbound q (by simp [hq]))]
    congr 1
    have he : e.1 < n := hbound e (by simp)
    rw [Finset.sum_eq_single (⟨e.1, he⟩ : Fin n)]
    · simp
    · intro k _ hk
      have hne : e.1 ≠ k.val := by
        intro h
        exact hk (Fin.ext h.symm)
      simp [hne]
    · simp

theorem torusMacaulayModularCheck_sound (n p a : ℕ)
    (rows : Array TorusMacaulayRow) (inverse : Array (Array ℤ))
    (h : torusMacaulayModularCheck n p a rows inverse) :
    torusMacaulaySparseMatrix n rows (a : ZMod p) *
      torusMacaulayIntegerMatrix n inverse = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ k : Fin n, ((rows[i.val]?.getD []).map fun e =>
      if e.1 = k.val then integerCoefficientEval (a : ZMod p) e.2 else 0).sum *
        (((inverse[k.val]?.getD #[])[j.val]?.getD 0 : ℤ) : ZMod p)) = _
  rw [torusMacaulay_sparse_row_dot n _ (h.1 i) (a : ZMod p)
    (fun k => (((inverse[k]?.getD #[])[j.val]?.getD 0 : ℤ) : ZMod p))]
  exact h.2 i j

theorem torusMacaulaySparseMatrix_map
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) (rows : Array TorusMacaulayRow) (x : R) :
    f.mapMatrix (torusMacaulaySparseMatrix n rows x) =
      torusMacaulaySparseMatrix n rows (f x) := by
  ext i j
  change f (((rows[i.val]?.getD []).map fun e =>
      if e.1 = j.val then integerCoefficientEval x e.2 else 0).sum) = _
  simp [map_list_sum, List.map_map, Function.comp_def, integerCoefficientEval_map,
    apply_ite f, torusMacaulaySparseMatrix]

end Biunimodular.F11
