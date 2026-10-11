/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RationalSparseCertificate
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
namespace Biunimodular.F11

def rationalSparseNeg (p : RationalSparsePolynomial) : RationalSparsePolynomial :=
  ⟨p.denominator, p.positive, fixedSliceSparseScale (-1) p.numerator⟩

def rationalSparseOne : RationalSparsePolynomial :=
  ⟨1, by decide, [⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩]⟩

noncomputable section
open MvPolynomial

@[simp] theorem rationalSparsePolynomial_neg (p : RationalSparsePolynomial) :
    rationalSparsePolynomial (rationalSparseNeg p) = -rationalSparsePolynomial p := by
  simp only [rationalSparsePolynomial, rationalSparseNeg, homogeneousSparsePolynomial_scale,
    Int.cast_neg, Int.cast_one, map_neg, map_one]
  ring

@[simp] theorem rationalSparsePolynomial_one : rationalSparsePolynomial rationalSparseOne = 1 := by
  norm_num [rationalSparsePolynomial, rationalSparseOne, homogeneousSparsePolynomial,
    fixedSliceAlphaEval]

/-- The standard matrix-column certificate is an exact linear combination
identity after interpreting its rational sparse entries as polynomials. -/
theorem rationalSparseZeroCheck.combination {n d : ℕ}
    (a b : Fin n → RationalSparsePolynomial) (target : RationalSparsePolynomial)
    (h : rationalSparseZeroCheck d
      ((List.ofFn fun i => (a i, b i)) ++ [(rationalSparseNeg target, rationalSparseOne)])) :
    (∑ i, rationalSparsePolynomial (a i) * rationalSparsePolynomial (b i)) =
      rationalSparsePolynomial target := by
  have hs := h.sound
  simpa [List.map_append, List.map_ofFn, List.sum_ofFn, add_neg_eq_zero] using hs

end
end Biunimodular.F11
