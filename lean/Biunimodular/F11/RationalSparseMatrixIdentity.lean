/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RationalSparseOperations

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

theorem rationalSparseZeroCheck.sub_sum {n δ : ℕ}
    (u v a b : RationalSparsePolynomial) (d g : Fin n → RationalSparsePolynomial)
    (h : rationalSparseZeroCheck δ
      ([(u, a), (rationalSparseNeg v, b)] ++
        List.ofFn (fun k => (rationalSparseNeg (d k), g k)))) :
    rationalSparsePolynomial u * rationalSparsePolynomial a -
      rationalSparsePolynomial v * rationalSparsePolynomial b -
      (∑ k, rationalSparsePolynomial (d k) * rationalSparsePolynomial (g k)) = 0 := by
  have hs := h.sound
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_ofFn, List.sum_append,
    List.sum_cons, List.sum_nil, List.sum_ofFn, Function.comp_apply, rationalSparsePolynomial_neg,
    neg_mul, Finset.sum_neg_distrib, add_zero] at hs
  linear_combination hs

theorem rationalSparseZeroCheck.sub_sum_eq_sum {n r δ : ℕ}
    (u v a b : RationalSparsePolynomial) (d g : Fin n → RationalSparsePolynomial)
    (w f : Fin r → RationalSparsePolynomial)
    (h : rationalSparseZeroCheck δ
      (([(u, a), (rationalSparseNeg v, b)] ++
        List.ofFn (fun k => (rationalSparseNeg (d k), g k))) ++
        List.ofFn (fun k => (rationalSparseNeg (w k), f k)))) :
    rationalSparsePolynomial u * rationalSparsePolynomial a -
      rationalSparsePolynomial v * rationalSparsePolynomial b -
      (∑ k, rationalSparsePolynomial (d k) * rationalSparsePolynomial (g k)) =
      ∑ k, rationalSparsePolynomial (w k) * rationalSparsePolynomial (f k) := by
  have hs := h.sound
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_ofFn, List.sum_append,
    List.sum_cons, List.sum_nil, List.sum_ofFn, Function.comp_apply, rationalSparsePolynomial_neg,
    neg_mul, Finset.sum_neg_distrib, add_zero] at hs
  linear_combination hs

theorem rationalSparseZeroCheck.residual {n b δ : ℕ} (j : Fin (n + 1))
    (m N : Fin b → RationalSparsePolynomial) (w f : Fin n → RationalSparsePolynomial)
    (h : rationalSparseZeroCheck δ
      (((if j.val = n then [(rationalSparseOne, rationalSparseOne)] else []) ++
        List.ofFn (fun k => (rationalSparseNeg (m k), N k))) ++
        List.ofFn (fun k => (rationalSparseNeg (w k), f k)))) :
    (if j = Fin.last n then (1 : MvPolynomial (Fin 6) ℂ) else 0) -
      (∑ k, rationalSparsePolynomial (m k) * rationalSparsePolynomial (N k)) =
      ∑ k, rationalSparsePolynomial (w k) * rationalSparsePolynomial (f k) := by
  classical
  have hs := h.sound
  have hj : j.val = n ↔ j = Fin.last n := by simp [Fin.ext_iff]
  simp only [List.map_append, List.map_ofFn, List.sum_append, List.sum_ofFn, Function.comp_apply,
    rationalSparsePolynomial_neg, neg_mul, Finset.sum_neg_distrib] at hs
  by_cases hlast : j = Fin.last n
  · simp [hlast, rationalSparsePolynomial_one] at hs
    simp only [hlast, ite_true]
    linear_combination hs
  · simp [hj, hlast] at hs
    simp only [hlast, ite_false]
    linear_combination hs

end
end Biunimodular.F11
