/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousSparsePolynomial

set_option autoImplicit false
namespace Biunimodular.F11
open MvPolynomial
noncomputable section
open MvPolynomial

theorem homogeneousSparsePolynomial_scale (n : ℤ) (p : FixedSliceSparsePolynomial) :
    homogeneousSparsePolynomial (fixedSliceSparseScale n p) =
      C (n : ℂ) * homogeneousSparsePolynomial p := by
  apply MvPolynomial.funext
  intro x
  simp only [homogeneousSparsePolynomial_eval, eval_mul, eval_C, fixedSliceSparseEval_scale]

end

/-- A rational sparse polynomial with a positive common denominator. -/
structure RationalSparsePolynomial where
  denominator : ℕ
  positive : 0 < denominator
  numerator : FixedSliceSparsePolynomial
  deriving DecidableEq

noncomputable def rationalSparsePolynomial (p : RationalSparsePolynomial) :
    MvPolynomial (Fin 6) ℂ :=
  C ((p.denominator : ℂ)⁻¹) * homogeneousSparsePolynomial p.numerator

def rationalSparseClearedTerms (d : ℕ)
    (pairs : List (RationalSparsePolynomial × RationalSparsePolynomial)) :
    List (FixedSliceSparsePolynomial × FixedSliceSparsePolynomial) :=
  pairs.map fun pair =>
    (fixedSliceSparseScale (Int.ofNat (d / (pair.1.denominator * pair.2.denominator)))
      pair.1.numerator, pair.2.numerator)

/-- A native check of a rational polynomial identity after one explicit
common denominator has been cleared. Divisibility is checked as well. -/
def rationalSparseZeroCheck (d : ℕ)
    (pairs : List (RationalSparsePolynomial × RationalSparsePolynomial)) : Prop :=
  0 < d ∧
    (∀ pair ∈ pairs, pair.1.denominator * pair.2.denominator ∣ d) ∧
    fixedSliceSparseNormalize
      (fixedSliceSparseSumProducts (rationalSparseClearedTerms d pairs)) = []

noncomputable section

theorem rationalSparsePolynomial_denominator_ne_zero (p : RationalSparsePolynomial) :
    (p.denominator : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt p.positive)

theorem rationalSparsePolynomial_clear_pair (d : ℕ)
    (a b : RationalSparsePolynomial) (h : a.denominator * b.denominator ∣ d) :
    homogeneousSparsePolynomial
      (fixedSliceSparseScale (Int.ofNat (d / (a.denominator * b.denominator))) a.numerator) *
        homogeneousSparsePolynomial b.numerator =
      C (d : ℂ) * (rationalSparsePolynomial a * rationalSparsePolynomial b) := by
  have ha := rationalSparsePolynomial_denominator_ne_zero a
  have hb := rationalSparsePolynomial_denominator_ne_zero b
  have hd : ((d / (a.denominator * b.denominator) : ℕ) : ℂ) *
      ((a.denominator : ℂ) * (b.denominator : ℂ)) = (d : ℂ) := by
    exact_mod_cast (Nat.div_mul_cancel h)
  have hc : (C (((d / (a.denominator * b.denominator) : ℕ) : ℂ)) :
      MvPolynomial (Fin 6) ℂ) =
      C (d : ℂ) * C ((a.denominator : ℂ)⁻¹) * C ((b.denominator : ℂ)⁻¹) := by
    rw [← map_mul, ← map_mul]
    apply congrArg C
    rw [← hd]
    field_simp [ha, hb]
  rw [homogeneousSparsePolynomial_scale]
  simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
  rw [hc]
  simp only [rationalSparsePolynomial]
  ring

theorem rationalSparsePolynomial_clear_sum (d : ℕ)
    (pairs : List (RationalSparsePolynomial × RationalSparsePolynomial))
    (h : ∀ pair ∈ pairs, pair.1.denominator * pair.2.denominator ∣ d) :
    homogeneousSparsePolynomial
      (fixedSliceSparseSumProducts (rationalSparseClearedTerms d pairs)) =
      C (d : ℂ) * (pairs.map fun pair =>
        rationalSparsePolynomial pair.1 * rationalSparsePolynomial pair.2).sum := by
  rw [homogeneousSparsePolynomial_sumProducts]
  simp only [rationalSparseClearedTerms, List.map_map]
  induction pairs with
  | nil => simp
  | cons pair pairs ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Function.comp_apply]
    rw [rationalSparsePolynomial_clear_pair d pair.1 pair.2 (h pair (by simp))]
    rw [ih (fun p hp => h p (by simp [hp]))]

/-- A successful finite check implies the full polynomial identity over ℂ,
not merely equality of values at a chosen point. -/
theorem rationalSparseZeroCheck.sound {d : ℕ}
    {pairs : List (RationalSparsePolynomial × RationalSparsePolynomial)}
    (h : rationalSparseZeroCheck d pairs) :
    (pairs.map fun pair =>
      rationalSparsePolynomial pair.1 * rationalSparsePolynomial pair.2).sum = 0 := by
  obtain ⟨hd, hdiv, hz⟩ := h
  have heq := congrArg homogeneousSparsePolynomial hz
  rw [homogeneousSparsePolynomial_normalize, rationalSparsePolynomial_clear_sum d pairs hdiv]
    at heq
  have hc : (C (d : ℂ) : MvPolynomial (Fin 6) ℂ) ≠ 0 := by
    apply MvPolynomial.C_ne_zero.mpr
    exact_mod_cast (Nat.ne_of_gt hd)
  exact (mul_eq_zero.mp heq).resolve_left hc

end
end Biunimodular.F11
