/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-- A squarefree split polynomial in a coordinate kernel generates that
kernel if every one of its roots lifts to a point of the coordinate algebra.
This proves equality of ideals, without assuming the algebra is reduced. -/
theorem coordinateKernel_eq_span_of_separable_root_lifts
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : K[X] →ₐ[K] A) (p : K[X]) (hp : p.Separable)
    (hsplit : p.Splits) (hzero : f p = 0)
    (hlift : ∀ x : K, p.IsRoot x →
      ∃ g : A →ₐ[K] K, g (f X) = x) :
    RingHom.ker f = Ideal.span ({p} : Set K[X]) := by
  apply le_antisymm
  · intro q hq
    apply Ideal.mem_span_singleton.mpr
    by_cases hq0 : q = 0
    · simp [hq0]
    apply hsplit.dvd_of_roots_le_roots hp.ne_zero
    apply (Multiset.le_iff_subset (Polynomial.nodup_roots hp)).mpr
    intro x hx
    have hpx : p.IsRoot x := (Polynomial.mem_roots hp.ne_zero).mp hx
    obtain ⟨g, hg⟩ := hlift x hpx
    have hcomp : g.comp f = Polynomial.aeval x := by
      apply Polynomial.algHom_ext
      simpa using hg
    apply (Polynomial.mem_roots hq0).mpr
    change q.eval x = 0
    have h : (g.comp f) q = 0 := by
      change g (f q) = 0
      rw [RingHom.mem_ker.mp hq, map_zero]
    simpa [hcomp] using h
  · apply Ideal.span_le.mpr
    intro q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact RingHom.mem_ker.mpr hzero

/-- A Bezout identity with a denominator polynomial proves that denominator
is nonzero at every root of the eliminant. -/
theorem denominator_ne_zero_at_root_of_bezout
    {K : Type*} [Field K] (p d a b : K[X])
    (hbezout : a * p + b * d = 1) (x : K) (hx : p.IsRoot x) :
    d.eval x ≠ 0 := by
  intro hd
  have hx0 : p.eval x = 0 := hx
  have h := congrArg (Polynomial.eval x) hbezout
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    hx0, hd, mul_zero, zero_add] at h
  exact zero_ne_one h

end

end Biunimodular.F11
