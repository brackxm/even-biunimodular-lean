/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusGrevlexOrder
import Biunimodular.F11.RurInverseSparsePolynomial
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false
namespace Biunimodular.F11
open MvPolynomial
open scoped MonomialOrder

def torusSparseExponentFunction (e : RurInverseExponent7) : Fin 7 → ℕ :=
  ![e.z1, e.z2, e.z3, e.z4, e.z5, e.w, e.x]

def torusSparseExponentEncoding (e : RurInverseExponent7) : Fin 8 → ℕ :=
  Fin.cons (∑ j, torusSparseExponentFunction e j)
    (fun i => ∑ j ∈ Finset.univ.erase i.rev, torusSparseExponentFunction e j)

def torusSparseExponentLT (a b : RurInverseExponent7) : Prop :=
  ∃ i : Fin 8, (∀ j : Fin 8, j < i →
    torusSparseExponentEncoding a j = torusSparseExponentEncoding b j) ∧
    torusSparseExponentEncoding a i < torusSparseExponentEncoding b i

instance (a b : RurInverseExponent7) : Decidable (torusSparseExponentLT a b) :=
  inferInstanceAs (Decidable (∃ i : Fin 8, (∀ j : Fin 8, j < i →
    torusSparseExponentEncoding a j = torusSparseExponentEncoding b j) ∧
    torusSparseExponentEncoding a i < torusSparseExponentEncoding b i))

/-- The stored head has nonzero coefficient, and every remaining term is
strictly smaller in the proved order. No coefficient cancellation is assumed. -/
def torusSparseLeadingCheck (p : List RurInverseTerm7) (e : RurInverseExponent7) : Prop :=
  match p with
  | [] => False
  | t :: tail => t.exponent = e ∧ t.coefficient ≠ 0 ∧
      ∀ u ∈ tail, torusSparseExponentLT u.exponent e

instance (p : List RurInverseTerm7) (e : RurInverseExponent7) :
    Decidable (torusSparseLeadingCheck p e) := by
  cases p <;> unfold torusSparseLeadingCheck <;> infer_instance

noncomputable section

def torusSparseExponent (e : RurInverseExponent7) : Fin 7 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (torusSparseExponentFunction e)

@[simp] theorem torusSparseExponent_apply (e : RurInverseExponent7) (i : Fin 7) :
    torusSparseExponent e i = torusSparseExponentFunction e i := by
  simp [torusSparseExponent]

theorem torusSparseExponentEncoding_eq (e : RurInverseExponent7) :
    torusGrevlexEncoding (torusSparseExponent e) =
      Finsupp.equivFunOnFinite.symm (torusSparseExponentEncoding e) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [torusSparseExponentEncoding]

theorem torusSparseExponentLT_iff (a b : RurInverseExponent7) :
    torusSparseExponentLT a b ↔
      torusSparseExponent a ≺[torusGrevlexOrder] torusSparseExponent b := by
  change _ ↔ toLex (torusGrevlexEncoding (torusSparseExponent a)) <
    toLex (torusGrevlexEncoding (torusSparseExponent b))
  rw [Finsupp.Lex.lt_iff]
  simp only [torusSparseExponentEncoding_eq, ofLex_toLex]
  rfl

def torusSparsePolynomial (p : List RurInverseTerm7) : MvPolynomial (Fin 7) ℂ :=
  rurInverseSparseEval p (X 0) (X 1) (X 2) (X 3) (X 5) (X 4) (X 6)

theorem torusSparseTerm_monomial (t : RurInverseTerm7) :
    rurInverseSparseTermEval t (X 0) (X 1) (X 2) (X 3) (X 5) (X 4) (X 6) =
      monomial (torusSparseExponent t.exponent) (t.coefficient : ℂ) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero (X i)), Fin.prod_univ_seven]
  simp only [torusSparseExponent_apply]
  dsimp [rurInverseSparseTermEval, torusSparseExponentFunction]
  simp only [map_intCast]
  ring

theorem torusSparsePolynomial_cons (t : RurInverseTerm7) (p : List RurInverseTerm7) :
    torusSparsePolynomial (t :: p) =
      monomial (torusSparseExponent t.exponent) (t.coefficient : ℂ) + torusSparsePolynomial p := by
  change rurInverseSparseTermEval t _ _ _ _ _ _ _ + _ = _
  rw [torusSparseTerm_monomial]
  rfl

private theorem torusPolynomial_add_strict_bound
    {f g : MvPolynomial (Fin 7) ℂ} {d : Fin 7 →₀ ℕ}
    (hf : f = 0 ∨ torusGrevlexOrder.degree f ≺[torusGrevlexOrder] d)
    (hg : g = 0 ∨ torusGrevlexOrder.degree g ≺[torusGrevlexOrder] d) :
    f + g = 0 ∨ torusGrevlexOrder.degree (f + g) ≺[torusGrevlexOrder] d := by
  obtain rfl | hf := hf
  · simpa using hg
  obtain rfl | hg := hg
  · simpa using (Or.inr hf : f = 0 ∨ torusGrevlexOrder.degree f ≺[torusGrevlexOrder] d)
  exact Or.inr (lt_of_le_of_lt torusGrevlexOrder.degree_add_le (max_lt hf hg))

theorem torusSparsePolynomial_strict_bound (p : List RurInverseTerm7)
    (e : RurInverseExponent7) (h : ∀ t ∈ p, torusSparseExponentLT t.exponent e) :
    torusSparsePolynomial p = 0 ∨
      torusGrevlexOrder.degree (torusSparsePolynomial p)
        ≺[torusGrevlexOrder] torusSparseExponent e := by
  classical
  induction p with
  | nil => exact Or.inl rfl
  | cons t p ih =>
    rw [torusSparsePolynomial_cons]
    apply torusPolynomial_add_strict_bound
    · by_cases hz : (t.coefficient : ℂ) = 0
      · left; simp [hz]
      right
      rw [torusGrevlexOrder.degree_monomial, ite_eq_right hz]
      exact (torusSparseExponentLT_iff _ _).mp (h t (by simp))
    · exact ih (fun u hu => h u (by simp [hu]))

/-- A finite leading-term check proves both the actual degree and invertible
leading coefficient of the complex multivariate polynomial. -/
theorem torusSparseLeadingCheck.sound {p : List RurInverseTerm7}
    {e : RurInverseExponent7} (h : torusSparseLeadingCheck p e) :
    IsUnit (torusGrevlexOrder.leadingCoeff (torusSparsePolynomial p)) ∧
      torusGrevlexOrder.degree (torusSparsePolynomial p) = torusSparseExponent e := by
  cases p with
  | nil => exact h.elim
  | cons t tail =>
    obtain ⟨he, hc, hlower⟩ := h
    have hn : (t.coefficient : ℂ) ≠ 0 := by exact_mod_cast hc
    have hd : torusGrevlexOrder.degree
        (monomial (torusSparseExponent t.exponent) (t.coefficient : ℂ)) =
          torusSparseExponent e := by
      rw [torusGrevlexOrder.degree_monomial, ite_eq_right hn, he]
    rw [torusSparsePolynomial_cons]
    obtain hz | hlt := torusSparsePolynomial_strict_bound tail e hlower
    · rw [hz, add_zero]
      refine ⟨?_, hd⟩
      simpa using (isUnit_iff_ne_zero.mpr hn)
    have hlt' : torusGrevlexOrder.degree (torusSparsePolynomial tail)
        ≺[torusGrevlexOrder] torusGrevlexOrder.degree
          (monomial (torusSparseExponent t.exponent) (t.coefficient : ℂ)) := by
      simpa only [hd] using hlt
    refine ⟨?_, by rw [torusGrevlexOrder.degree_add_of_lt hlt', hd]⟩
    rw [torusGrevlexOrder.leadingCoeff_add_of_lt hlt']
    simpa using (isUnit_iff_ne_zero.mpr hn)

end
end Biunimodular.F11
