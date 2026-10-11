/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceSparsePolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Ideal.Operations

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

/-- Interpret the six sparse exponent slots as homogeneous coordinates
`(x5,x4,x3,x2,x1,x0)`, rather than the affine trace coordinate. -/
def homogeneousSparsePolynomial (p : FixedSliceSparsePolynomial) :
    MvPolynomial (Fin 6) ℂ :=
  (p.map fun t => C (fixedSliceAlphaEval t.coefficient) *
    X 5 ^ t.exponent.x5 * X 4 ^ t.exponent.x4 *
    X 3 ^ t.exponent.x3 * X 2 ^ t.exponent.x2 *
    X 1 ^ t.exponent.x1 * X 0 ^ t.exponent.trace).sum

theorem homogeneousSparsePolynomial_eval (p : FixedSliceSparsePolynomial)
    (x : Fin 6 → ℂ) :
    eval x (homogeneousSparsePolynomial p) =
      fixedSliceSparseEval p (x 5) (x 4) (x 3) (x 2) (x 1) (x 0) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [homogeneousSparsePolynomial, List.map_cons, List.sum_cons,
      eval_add, eval_mul, eval_C, eval_pow, eval_X] at *
    exact congrArg (_ + ·) ih

theorem homogeneousSparsePolynomial_normalize (p : FixedSliceSparsePolynomial) :
    homogeneousSparsePolynomial (fixedSliceSparseNormalize p) =
      homogeneousSparsePolynomial p := by
  apply MvPolynomial.funext
  intro x
  simp only [homogeneousSparsePolynomial_eval, fixedSliceSparseEval_normalize]

theorem homogeneousSparsePolynomial_add (p q : FixedSliceSparsePolynomial) :
    homogeneousSparsePolynomial (fixedSliceSparseAdd p q) =
      homogeneousSparsePolynomial p + homogeneousSparsePolynomial q := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_add, homogeneousSparsePolynomial_eval, fixedSliceSparseEval_add]

theorem homogeneousSparsePolynomial_mul (p q : FixedSliceSparsePolynomial) :
    homogeneousSparsePolynomial (fixedSliceSparseMul p q) =
      homogeneousSparsePolynomial p * homogeneousSparsePolynomial q := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_mul, homogeneousSparsePolynomial_eval, fixedSliceSparseEval_mul]

theorem homogeneousSparsePolynomial_sumProducts
    (pairs : List (FixedSliceSparsePolynomial × FixedSliceSparsePolynomial)) :
    homogeneousSparsePolynomial (fixedSliceSparseSumProducts pairs) =
      (pairs.map fun pair => homogeneousSparsePolynomial pair.1 *
        homogeneousSparsePolynomial pair.2).sum := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    simp only [fixedSliceSparseSumProducts, homogeneousSparsePolynomial_add,
      homogeneousSparsePolynomial_mul, List.map_cons, List.sum_cons, ih]

theorem homogeneousSparsePolynomial_combination_mem
    (row generators : List FixedSliceSparsePolynomial)
    (I : Ideal (MvPolynomial (Fin 6) ℂ))
    (hgenerators : ∀ g ∈ generators, homogeneousSparsePolynomial g ∈ I) :
    homogeneousSparsePolynomial
      (fixedSliceSparseSumProducts (row.zip generators)) ∈ I := by
  rw [homogeneousSparsePolynomial_sumProducts]
  apply list_sum_mem
  intro p hp
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hp
  exact I.mul_mem_left _ (hgenerators _ (List.of_mem_zip hpair).2)

/-- Exact sparse identities imply polynomial ideal membership, with no
assumption that the generators vanish at a selected point. -/
theorem fixedSliceSparseSystemIdentity.mem_ideal
    {targets : List FixedSliceSparsePolynomial}
    {rows : List (List FixedSliceSparsePolynomial)}
    {generators : List FixedSliceSparsePolynomial}
    (h : fixedSliceSparseSystemIdentity targets rows generators)
    (I : Ideal (MvPolynomial (Fin 6) ℂ))
    (hgenerators : ∀ g ∈ generators, homogeneousSparsePolynomial g ∈ I) :
    ∀ p ∈ targets, homogeneousSparsePolynomial p ∈ I := by
  intro p hp
  have hm : fixedSliceSparseNormalize p ∈ targets.map fixedSliceSparseNormalize :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [h] at hm
  obtain ⟨combination, hc, heq⟩ := List.mem_map.mp hm
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hc
  have he := congrArg homogeneousSparsePolynomial heq
  simp only [homogeneousSparsePolynomial_normalize] at he
  rw [← he]
  exact homogeneousSparsePolynomial_combination_mem row generators I hgenerators

end
end Biunimodular.F11
