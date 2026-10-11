/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousGrevlexOrder
import Biunimodular.F11.RationalSparseOperations
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
namespace Biunimodular.F11
open MvPolynomial
open scoped MonomialOrder

def homogeneousExponentFunction (e : FixedSliceSparseExponent) : Fin 6 → ℕ :=
  ![e.trace, e.x1, e.x2, e.x3, e.x4, e.x5]

def homogeneousExponentEncoding (e : FixedSliceSparseExponent) : Fin 7 → ℕ :=
  Fin.cons (∑ j, homogeneousExponentFunction e j)
    (fun i => ∑ j ∈ Finset.univ.erase i, homogeneousExponentFunction e j)

/-- A computable comparison using precisely the proved reverse lexicographic
monomial order. The finite lexicographic test contains no polynomial oracle. -/
def homogeneousExponentLT (a b : FixedSliceSparseExponent) : Prop :=
  ∃ i : Fin 7, (∀ j : Fin 7, j < i →
    homogeneousExponentEncoding a j = homogeneousExponentEncoding b j) ∧
    homogeneousExponentEncoding a i < homogeneousExponentEncoding b i

instance (a b : FixedSliceSparseExponent) : Decidable (homogeneousExponentLT a b) :=
  inferInstanceAs (Decidable (∃ i : Fin 7, (∀ j : Fin 7, j < i →
    homogeneousExponentEncoding a j = homogeneousExponentEncoding b j) ∧
    homogeneousExponentEncoding a i < homogeneousExponentEncoding b i))

noncomputable section

def homogeneousExponent (e : FixedSliceSparseExponent) : Fin 6 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (homogeneousExponentFunction e)

@[simp] theorem homogeneousExponent_apply (e : FixedSliceSparseExponent) (i : Fin 6) :
    homogeneousExponent e i = homogeneousExponentFunction e i := by
  simp [homogeneousExponent]

theorem homogeneousExponentEncoding_eq (e : FixedSliceSparseExponent) :
    homogeneousGrevlexEncoding (homogeneousExponent e) =
      Finsupp.equivFunOnFinite.symm (homogeneousExponentEncoding e) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [homogeneousExponentEncoding]

/-- Soundness of the executable monomial comparison. -/
theorem homogeneousExponentLT_iff (a b : FixedSliceSparseExponent) :
    homogeneousExponentLT a b ↔
      homogeneousExponent a ≺[homogeneousGrevlexOrder] homogeneousExponent b := by
  change _ ↔ toLex (homogeneousGrevlexEncoding (homogeneousExponent a)) <
    toLex (homogeneousGrevlexEncoding (homogeneousExponent b))
  rw [Finsupp.Lex.lt_iff]
  simp only [homogeneousExponentEncoding_eq, ofLex_toLex]
  rfl

/-- The sparse exponent slots agree with the actual homogeneous monomials. -/
theorem homogeneousSparseTerm_monomial (t : FixedSliceSparseTerm) :
    C (fixedSliceAlphaEval t.coefficient) *
      X 5 ^ t.exponent.x5 * X 4 ^ t.exponent.x4 * X 3 ^ t.exponent.x3 *
      X 2 ^ t.exponent.x2 * X 1 ^ t.exponent.x1 * X 0 ^ t.exponent.trace =
    monomial (homogeneousExponent t.exponent) (fixedSliceAlphaEval t.coefficient) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero (X i)), Fin.prod_univ_six]
  simp only [homogeneousExponent_apply]
  dsimp [homogeneousExponentFunction]
  ring

theorem homogeneousSparsePolynomial_cons (t : FixedSliceSparseTerm)
    (p : FixedSliceSparsePolynomial) :
    homogeneousSparsePolynomial (t :: p) =
      monomial (homogeneousExponent t.exponent) (fixedSliceAlphaEval t.coefficient) +
        homogeneousSparsePolynomial p := by
  simp only [homogeneousSparsePolynomial, List.map_cons, List.sum_cons]
  congr 1
  exact homogeneousSparseTerm_monomial t

end
end Biunimodular.F11
