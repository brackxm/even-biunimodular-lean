/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- If the images of all polynomial variables belong to a coordinate map's
range, that coordinate map generates the whole quotient algebra. -/
theorem coordinate_surjective_of_variables_in_range
    {K σ : Type*} [CommRing K]
    (I : Ideal (MvPolynomial σ K))
    (f : Polynomial K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hvars : ∀ i, Ideal.Quotient.mkₐ K I (MvPolynomial.X i) ∈ f.range) :
    Function.Surjective f := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mkₐ K I p ∈ f.range
  induction p using MvPolynomial.induction_on with
  | C c =>
    change Ideal.Quotient.mkₐ K I ((algebraMap K (MvPolynomial σ K)) c) ∈ f.range
    rw [AlgHom.commutes]
    exact f.range.algebraMap_mem c
  | add p q hp hq =>
    rw [map_add]
    exact f.range.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    exact f.range.mul_mem hp (hvars i)

/-- A reverse RUR relation expresses its coordinate as a polynomial in x.
The Bezout identity supplies the inverse of the denominator in the algebra,
so this argument also applies to nilpotent elements. -/
theorem coordinate_mem_range_of_reverse_rur
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (f : Polynomial K →ₐ[K] A) (H d B E N : Polynomial K) (a : A)
    (hH : f H = 0) (hBezout : B * H + E * d = 1)
    (hreverse : f d * a = f N) : a ∈ f.range := by
  have hinverse : f E * f d = 1 := by
    have h := congrArg f hBezout
    simpa only [map_add, map_mul, map_one, hH, mul_zero, zero_add] using h
  refine ⟨E * N, ?_⟩
  calc
    f (E * N) = f E * f N := map_mul f E N
    _ = f E * (f d * a) := by rw [hreverse]
    _ = a := by rw [← mul_assoc, hinverse, one_mul]

end
end Biunimodular.F11
