/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

/-- Leading monomials of any ideal members suffice for a spanning bound.
No assumption that this family is a complete Groebner basis is required. -/
theorem quotient_standard_monomials_span
    {K σ ι : Type*} [Field K]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (b : ι → MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (hI : ∀ i, b i ∈ I)
    (hS : ∀ e, (∀ i, ¬ m.degree (b i) ≤ e) → e ∈ S) :
    Submodule.span K (Set.range (fun e : S =>
      Ideal.Quotient.mkₐ K I (monomial e.val (1 : K)))) = ⊤ := by
  classical
  apply top_unique
  intro a _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, r, hp, _, hr⟩ := m.div hb p
  have hg : Finsupp.linearCombination (MvPolynomial σ K) b g ∈ I := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro i _
    simpa only [smul_eq_mul] using I.mul_mem_left (g i) (hI i)
  change Ideal.Quotient.mkₐ K I p ∈ _
  have hq : Ideal.Quotient.mkₐ K I
      (Finsupp.linearCombination (MvPolynomial σ K) b g) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hg
  rw [hp, map_add, hq, zero_add]
  rw [r.as_sum, map_sum]
  apply Submodule.sum_mem
  intro e he
  have hv : Ideal.Quotient.mkₐ K I (monomial e (1 : K)) ∈
      Submodule.span K (Set.range (fun e : S =>
        Ideal.Quotient.mkₐ K I (monomial e.val (1 : K)))) :=
    Submodule.subset_span ⟨⟨e, hS e (hr e he)⟩, rfl⟩
  have hmono : monomial e (r.coeff e) = r.coeff e • monomial e (1 : K) := by
    simp [smul_monomial]
  rw [hmono, map_smul]
  exact Submodule.smul_mem _ _ hv

theorem quotient_finiteDimensional_of_standard_monomials
    {K σ ι : Type*} [Field K]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (b : ι → MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (hI : ∀ i, b i ∈ I)
    (hS : ∀ e, (∀ i, ¬ m.degree (b i) ≤ e) → e ∈ S) :
    FiniteDimensional K (MvPolynomial σ K ⧸ I) := by
  classical
  let v : S → (MvPolynomial σ K ⧸ I) :=
    fun e => Ideal.Quotient.mkₐ K I (monomial e.val (1 : K))
  apply FiniteDimensional.of_surjective (Finsupp.linearCombination K v)
  apply LinearMap.range_eq_top.mp
  rw [Finsupp.range_linearCombination]
  exact quotient_standard_monomials_span m I b S hb hI hS

theorem quotient_finrank_le_standard_monomials
    {K σ ι : Type*} [Field K]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (b : ι → MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (hI : ∀ i, b i ∈ I)
    (hS : ∀ e, (∀ i, ¬ m.degree (b i) ≤ e) → e ∈ S) :
    Module.finrank K (MvPolynomial σ K ⧸ I) ≤ S.card := by
  classical
  simpa only [Fintype.card_coe] using
    finrank_le_of_span_eq_top (quotient_standard_monomials_span m I b S hb hI hS)

end
end Biunimodular.F11
