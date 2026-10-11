/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.MonicDivisorSubproduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.Polynomial.GaussLemma

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial

/-- Two equal-degree irreducible modular factors exclude a proper monic
integral divisor when neither factor has the constant of an integral unit. -/
theorem monic_irreducible_of_two_modular_constants
    (p : ℤ[X]) (hp : p.Monic) (hc : p.coeff 0 = 1)
    (n prime : ℕ) (hn : 0 < n) [Fact (Nat.Prime prime)]
    (hd : p.natDegree = 2*n) (f₁ f₂ : (ZMod prime)[X])
    (h₁ : f₁.Monic ∧ Irreducible f₁) (h₂ : f₂.Monic ∧ Irreducible f₂)
    (d₁ : f₁.natDegree = n) (d₂ : f₂.natDegree = n)
    (c₁ : f₁.coeff 0 ≠ 1 ∧ f₁.coeff 0 ≠ -1)
    (c₂ : f₂.coeff 0 ≠ 1 ∧ f₂.coeff 0 ≠ -1)
    (hfactor : p.map (Int.castRingHom (ZMod prime)) = f₁*f₂) : Irreducible p := by
  classical
  have hp1 : p ≠ 1 := by
    intro h
    have hz := congrArg Polynomial.natDegree h
    simp only [natDegree_one, hd] at hz
    omega
  apply (hp.irreducible_iff_lt_natDegree_lt hp1).mpr
  intro g hgm hdegree hdiv
  obtain ⟨hpos, hsmall⟩ := Finset.mem_Ioc.mp hdegree
  have hsmall' : g.natDegree ≤ n := by
    rw [hd] at hsmall
    omega
  obtain ⟨r, hr⟩ := hdiv
  have hprod : g.coeff 0 * r.coeff 0 = 1 := by
    rw [← mul_coeff_zero, ← hr, hc]
  have hunit : IsUnit (g.coeff 0) := IsUnit.of_mul_eq_one (r.coeff 0) hprod
  let q := g.map (Int.castRingHom (ZMod prime))
  have hqm : q.Monic := hgm.map _
  have hqd : q.natDegree = g.natDegree := hgm.natDegree_map _
  have hqc : q.coeff 0 = 1 ∨ q.coeff 0 = -1 := by
    obtain h | h := Int.isUnit_eq_one_or hunit
    · left; simp [q, Polynomial.coeff_map, h]
    · right; simp [q, Polynomial.coeff_map, h]
  have hqdiv : q ∣ f₁*f₂ := by
    rw [← hfactor]
    exact Polynomial.map_dvd (Int.castRingHom (ZMod prime)) ⟨r,hr⟩
  let s : Multiset (ZMod prime)[X] := f₁ ::ₘ f₂ ::ₘ 0
  have hs : ∀ f ∈ s, f.Monic ∧ Irreducible f := by
    intro f hf
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hf
    rcases hf with rfl | rfl
    · exact h₁
    · exact h₂
  have hqs : q ∣ s.prod := by simpa [s] using hqdiv
  obtain ⟨t, ht, he⟩ := monic_divisor_eq_subproduct s hs q hqm hqs
  have hm := Multiset.mem_powerset.mpr ht
  simp only [s, Multiset.powerset_cons, Multiset.powerset_zero,
    Multiset.map_add, Multiset.map_singleton, Multiset.mem_add,
    Multiset.mem_singleton, or_assoc] at hm
  have hdpos : 0 < q.natDegree := hqd.symm ▸ hpos
  have hdsmall : q.natDegree ≤ n := hqd.symm ▸ hsmall'
  rw [he] at hdpos hdsmall hqc
  rcases hm with hm | hm | hm | hm
  all_goals subst t
  all_goals
    simp [Multiset.prod_cons, Multiset.prod_zero, natDegree_mul,
      h₁.1.ne_zero, h₂.1.ne_zero, d₁, d₂] at hdpos hdsmall hqc
  all_goals
    first
      | omega
      | exact hqc.elim c₁.1 c₁.2
      | exact hqc.elim c₂.1 c₂.2

end Biunimodular.F11
