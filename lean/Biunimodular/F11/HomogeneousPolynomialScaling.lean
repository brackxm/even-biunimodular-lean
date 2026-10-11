/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
namespace Biunimodular.F11
open scoped BigOperators

/-- Homogeneous evaluation scales by the total degree, over any commutative
target ring. -/
theorem homogeneousPolynomial_eval₂_scale {σ R S : Type*} [Fintype σ]
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (g : σ → S)
    (c : S) {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂ f (fun i => c * g i) p =
      c ^ n * MvPolynomial.eval₂ f g p := by
  classical
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdegree : (∑ i, d i) = n := by
    rw [← Finsupp.degree_eq_sum]
    simpa only [Finsupp.degree_apply] using (hp.degree_eq_sum_deg_support hd).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
  ring

end Biunimodular.F11
