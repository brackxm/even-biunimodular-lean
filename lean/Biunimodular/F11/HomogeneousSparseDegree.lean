/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousSparseOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

set_option autoImplicit false
namespace Biunimodular.F11
open MvPolynomial
open scoped MonomialOrder

/-- Remove all terms with the specified leading exponent. -/
def rationalSparseLowerPart (p : RationalSparsePolynomial)
    (e : FixedSliceSparseExponent) : RationalSparsePolynomial :=
  ⟨p.denominator, p.positive, p.numerator.filter (fun t => t.exponent != e)⟩

def rationalSparseMonomial (e : FixedSliceSparseExponent) : RationalSparsePolynomial :=
  ⟨1, by decide, [⟨⟨1, 0, 0, 0, 0⟩, e⟩]⟩

def rationalSparseLeadingTerms (p : RationalSparsePolynomial)
    (e : FixedSliceSparseExponent) :=
  [(p, rationalSparseOne), (rationalSparseNeg (rationalSparseMonomial e), rationalSparseOne),
    (rationalSparseNeg (rationalSparseLowerPart p e), rationalSparseOne)]

def rationalSparseLeadingCheck (p : RationalSparsePolynomial)
    (e : FixedSliceSparseExponent) : Prop :=
  rationalSparseZeroCheck p.denominator (rationalSparseLeadingTerms p e) ∧
  ∀ t ∈ (rationalSparseLowerPart p e).numerator, homogeneousExponentLT t.exponent e

noncomputable section

variable {σ K : Type*} [Field K]

theorem monomialOrder_add_strict_bound (m : MonomialOrder σ)
    {f h : MvPolynomial σ K} {d : σ →₀ ℕ}
    (hf : f = 0 ∨ m.degree f ≺[m] d)
    (hh : h = 0 ∨ m.degree h ≺[m] d) :
    f + h = 0 ∨ m.degree (f + h) ≺[m] d := by
  obtain rfl | hf := hf
  · simpa using hh
  obtain rfl | hh := hh
  · simpa using (Or.inr hf : f = 0 ∨ m.degree f ≺[m] d)
  exact Or.inr (lt_of_le_of_lt m.degree_add_le (max_lt hf hh))

theorem homogeneousSparsePolynomial_strict_bound (p : FixedSliceSparsePolynomial)
    (e : FixedSliceSparseExponent) (h : ∀ t ∈ p, homogeneousExponentLT t.exponent e) :
    homogeneousSparsePolynomial p = 0 ∨
      homogeneousGrevlexOrder.degree (homogeneousSparsePolynomial p)
        ≺[homogeneousGrevlexOrder] homogeneousExponent e := by
  classical
  induction p with
  | nil => exact Or.inl rfl
  | cons t p ih =>
    rw [homogeneousSparsePolynomial_cons]
    apply monomialOrder_add_strict_bound
    · by_cases hz : fixedSliceAlphaEval t.coefficient = 0
      · left; simp [hz]
      right
      rw [homogeneousGrevlexOrder.degree_monomial, ite_eq_right hz]
      exact (homogeneousExponentLT_iff _ _).mp (h t (by simp))
    · exact ih (fun u hu => h u (by simp [hu]))

theorem rationalSparsePolynomial_strict_bound (p : RationalSparsePolynomial)
    (e : FixedSliceSparseExponent)
    (h : ∀ t ∈ p.numerator, homogeneousExponentLT t.exponent e) :
    rationalSparsePolynomial p = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial p)
        ≺[homogeneousGrevlexOrder] homogeneousExponent e := by
  obtain hz | hlt := homogeneousSparsePolynomial_strict_bound p.numerator e h
  · exact Or.inl (by simp [rationalSparsePolynomial, hz])
  right
  apply lt_of_le_of_lt homogeneousGrevlexOrder.degree_mul_le
  simpa [homogeneousGrevlexOrder.degree_C] using hlt

theorem homogeneousExponent_mul (a b : FixedSliceSparseExponent) :
    homogeneousExponent (fixedSliceSparseExponentMul a b) =
      homogeneousExponent a + homogeneousExponent b := by
  ext i
  fin_cases i <;> simp [homogeneousExponentFunction, fixedSliceSparseExponentMul]

/-- Bounds on the stored terms of a multiplier imply a degree bound on its
product with a polynomial of known leading degree. -/
theorem homogeneousSparsePolynomial_mul_strict_bound (p : FixedSliceSparsePolynomial)
    (g : MvPolynomial (Fin 6) ℂ) (gd e : FixedSliceSparseExponent)
    (hg : g ≠ 0) (hgd : homogeneousGrevlexOrder.degree g = homogeneousExponent gd)
    (h : ∀ t ∈ p, homogeneousExponentLT
      (fixedSliceSparseExponentMul t.exponent gd) e) :
    homogeneousSparsePolynomial p * g = 0 ∨
      homogeneousGrevlexOrder.degree (homogeneousSparsePolynomial p * g)
        ≺[homogeneousGrevlexOrder] homogeneousExponent e := by
  classical
  induction p with
  | nil => exact Or.inl (by simp [homogeneousSparsePolynomial])
  | cons t p ih =>
    rw [homogeneousSparsePolynomial_cons, add_mul]
    apply monomialOrder_add_strict_bound
    · by_cases hz : fixedSliceAlphaEval t.coefficient = 0
      · left; simp [hz]
      right
      rw [homogeneousGrevlexOrder.degree_mul
        ((monomial_eq_zero (s := homogeneousExponent t.exponent)).not.mpr hz) hg,
        homogeneousGrevlexOrder.degree_monomial, ite_eq_right hz, hgd,
        ← homogeneousExponent_mul]
      exact (homogeneousExponentLT_iff _ _).mp (h t (by simp))
    · exact ih (fun u hu => h u (by simp [hu]))

theorem rationalSparsePolynomial_mul_strict_bound (p : RationalSparsePolynomial)
    (g : MvPolynomial (Fin 6) ℂ) (gd e : FixedSliceSparseExponent)
    (hg : g ≠ 0) (hgd : homogeneousGrevlexOrder.degree g = homogeneousExponent gd)
    (h : ∀ t ∈ p.numerator, homogeneousExponentLT
      (fixedSliceSparseExponentMul t.exponent gd) e) :
    rationalSparsePolynomial p * g = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial p * g)
        ≺[homogeneousGrevlexOrder] homogeneousExponent e := by
  simp only [rationalSparsePolynomial, mul_assoc]
  obtain hz | hlt := homogeneousSparsePolynomial_mul_strict_bound p.numerator g gd e hg hgd h
  · exact Or.inl (by rw [hz, mul_zero])
  right
  apply lt_of_le_of_lt homogeneousGrevlexOrder.degree_mul_le
  simpa [homogeneousGrevlexOrder.degree_C] using hlt

@[simp] theorem rationalSparsePolynomial_monomial (e : FixedSliceSparseExponent) :
    rationalSparsePolynomial (rationalSparseMonomial e) =
      monomial (homogeneousExponent e) (1 : ℂ) := by
  simp only [rationalSparsePolynomial, rationalSparseMonomial, Nat.cast_one,
    inv_one, map_one, one_mul, homogeneousSparsePolynomial, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [homogeneousSparseTerm_monomial ⟨⟨1, 0, 0, 0, 0⟩, e⟩]
  norm_num [fixedSliceAlphaEval]

/-- A successful leading-term check proves monicity and the exact degree in
our well-founded monomial order. -/
theorem rationalSparseLeadingCheck.sound {p : RationalSparsePolynomial}
    {e : FixedSliceSparseExponent} (h : rationalSparseLeadingCheck p e) :
    homogeneousGrevlexOrder.Monic (rationalSparsePolynomial p) ∧
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial p) = homogeneousExponent e := by
  classical
  obtain ⟨hidentity, hlower⟩ := h
  have hi := hidentity.sound
  have heq : rationalSparsePolynomial p = monomial (homogeneousExponent e) (1 : ℂ) +
      rationalSparsePolynomial (rationalSparseLowerPart p e) := by
    simp only [rationalSparseLeadingTerms, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, rationalSparsePolynomial_neg, rationalSparsePolynomial_one,
      rationalSparsePolynomial_monomial, mul_one, add_zero] at hi
    linear_combination hi
  rw [heq]
  have hm : homogeneousGrevlexOrder.Monic (monomial (homogeneousExponent e) (1 : ℂ)) :=
    homogeneousGrevlexOrder.monic_monomial_one
  have hd : homogeneousGrevlexOrder.degree (monomial (homogeneousExponent e) (1 : ℂ)) =
      homogeneousExponent e := by simp [homogeneousGrevlexOrder.degree_monomial]
  obtain hz | hlt := rationalSparsePolynomial_strict_bound _ e hlower
  · simpa [hz] using And.intro hm hd
  have hdeg : homogeneousGrevlexOrder.degree (monomial (homogeneousExponent e) (1 : ℂ) +
      rationalSparsePolynomial (rationalSparseLowerPart p e)) = homogeneousExponent e := by
    rw [homogeneousGrevlexOrder.degree_add_of_lt (by simpa [hd] using hlt), hd]
  refine ⟨?_, hdeg⟩
  unfold MonomialOrder.Monic
  rw [homogeneousGrevlexOrder.leadingCoeff_add_of_lt (by simpa [hd] using hlt)]
  exact hm

end
end Biunimodular.F11
