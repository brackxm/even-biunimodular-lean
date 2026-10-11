/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FiniteFieldFrobeniusTransport
import Biunimodular.F11.FiniteFieldRootPeriod
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-- The number of points moved by a permutation does not depend on the
decidable equality instance used to form its support finset. -/
theorem perm_support_card_decidableEq
    {α : Type*} [Fintype α] (f : Equiv.Perm α)
    (d₁ d₂ : DecidableEq α) :
    (@Equiv.Perm.support α d₁ _ f).card =
      (@Equiv.Perm.support α d₂ _ f).card := by
  have h : (@Equiv.Perm.support α d₁ _ f) =
      (@Equiv.Perm.support α d₂ _ f) := by
    ext x
    simp only [Equiv.Perm.mem_support]
  rw [h]

/-- On fewer than twice `n` roots, a nontrivial Frobenius permutation of
prime order `n` is one `n`-cycle. -/
theorem finiteFieldFrobPermIn_isCycle_of_prime_period
    {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (p : F[X]) [Fact ((p.map (algebraMap F K)).Splits)]
    [DecidableEq (p.rootSet K)]
    (n : ℕ) (hn : Nat.Prime n)
    (hcard : Fintype.card (p.rootSet K) < 2 * n)
    (hperiod : ∀ x : p.rootSet K,
      (x : K) ^ (Fintype.card F) ^ n = x)
    (hnonfix : ∃ x : p.rootSet K,
      (x : K) ^ Fintype.card F ≠ x) :
    (finiteFieldFrobPermIn p K).IsCycle ∧
      (finiteFieldFrobPermIn p K).support.card = n := by
  let g := finiteFieldFrobPermIn p K
  have hpow (x : p.rootSet K) : ((g x) : K) = (x : K) ^ Fintype.card F :=
    finiteFieldFrobPermIn_apply p K x
  have hiter (m : ℕ) (x : p.rootSet K) :
      (((g ^ m) x) : K) = (x : K) ^ (Fintype.card F) ^ m := by
    induction m generalizing x with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih, hpow]
      simp only [pow_succ, pow_mul, mul_comm]
  have hgn : g ^ n = 1 := by
    ext x
    simpa only [Equiv.Perm.one_apply] using (hiter n x).trans (hperiod x)
  have hgne : g ≠ 1 := by
    obtain ⟨x, hx⟩ := hnonfix
    intro hg
    apply hx
    have h := hpow x
    rw [hg] at h
    simpa using h.symm
  have horddvd : orderOf g ∣ n := orderOf_dvd_iff_pow_eq_one.mpr hgn
  have hord : orderOf g = n := by
    have hne : orderOf g ≠ 1 := by
      intro h
      exact hgne (orderOf_eq_one_iff.mp h)
    exact (hn.dvd_iff_eq hne).mp horddvd |>.symm
  have hcycle := Equiv.Perm.isCycle_of_prime_order' (hord ▸ hn)
    (by rw [hord]
        exact hcard)
  refine ⟨hcycle, ?_⟩
  simpa only [g, Nat.card_eq_fintype_card] using hcycle.orderOf.symm.trans hord

/-- An irreducible degree-`n` factor supplies the nonfixed root; the other
factors only need to have roots fixed by the `card(F)^n` power map. -/
theorem finiteFieldFrobPermIn_isCycle_of_irreducible_factor
    {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (p q : F[X]) [Fact ((p.map (algebraMap F K)).Splits)]
    [Fact ((q.map (algebraMap F K)).Splits)]
    [DecidableEq (p.rootSet K)]
    (hpne : p ≠ 0) (hq : Irreducible q)
    (n : ℕ) (hn : Nat.Prime n) (hqdeg : q.natDegree = n)
    (hdiv : q ∣ p)
    (hcard : Fintype.card (p.rootSet K) < 2 * n)
    (hother : ∀ x : p.rootSet K, x.1 ∉ q.rootSet K →
      (x : K) ^ (Fintype.card F) ^ n = x) :
    (finiteFieldFrobPermIn p K).IsCycle ∧
      (finiteFieldFrobPermIn p K).support.card = n := by
  have hinc (x : q.rootSet K) : x.1 ∈ p.rootSet K := by
    apply Polynomial.mem_rootSet.mpr
    refine ⟨hpne, ?_⟩
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv
      ((Polynomial.mem_rootSet.mp x.2).2)
  have hperiod (x : p.rootSet K) :
      (x : K) ^ (Fintype.card F) ^ n = x := by
    by_cases hx : x.1 ∈ q.rootSet K
    · have h := irreducible_root_pow_card_pow q hq ⟨x.1, hx⟩
      rw [← Fintype.card_eq_nat_card, hqdeg] at h
      exact h
    · exact hother x hx
  have hnonfix : ∃ x : p.rootSet K, (x : K) ^ Fintype.card F ≠ x := by
    have hqcycle := finiteFieldFrobPermIn_isCycle q K hq (by rw [hqdeg]; exact hn.two_le)
    obtain ⟨x, hx, _⟩ := hqcycle
    refine ⟨⟨x.1, hinc x⟩, ?_⟩
    intro hfixed
    apply hx
    apply Subtype.ext
    rw [finiteFieldFrobPermIn_apply q K x]
    exact hfixed
  exact finiteFieldFrobPermIn_isCycle_of_prime_period p n hn hcard hperiod hnonfix

/-- A polynomial with split linear factors and one irreducible prime-degree
factor has a single Frobenius cycle when there are fewer than two such
prime-degree blocks of roots. -/
theorem finiteFieldFrobPermIn_split_mul_irreducible
    {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (l q : F[X]) [Fact (((l * q).map (algebraMap F K)).Splits)]
    [DecidableEq ((l * q).rootSet K)]
    (hl : l.Splits) (hlne : l ≠ 0) (hq : Irreducible q)
    (n : ℕ) (hn : Nat.Prime n) (hqdeg : q.natDegree = n)
    (hcard : Fintype.card ((l * q).rootSet K) < 2 * n) :
    (finiteFieldFrobPermIn (l * q) K).IsCycle ∧
      (finiteFieldFrobPermIn (l * q) K).support.card = n := by
  have hdiv : q ∣ l * q := ⟨l, by ring⟩
  have hsplitq : (q.map (algebraMap F K)).Splits := by
    apply (Fact.out : ((l * q).map (algebraMap F K)).Splits).of_dvd
    · exact Polynomial.map_ne_zero (mul_ne_zero hlne hq.ne_zero)
    · exact Polynomial.map_dvd (algebraMap F K) hdiv
  let : Fact ((q.map (algebraMap F K)).Splits) := ⟨hsplitq⟩
  have hother (x : (l * q).rootSet K)
      (hxq : x.1 ∉ q.rootSet K) :
      (x : K) ^ (Fintype.card F) ^ n = x := by
    have hxzero : aeval x.1 (l * q) = 0 := (Polynomial.mem_rootSet.mp x.2).2
    rw [map_mul] at hxzero
    have hqne : aeval x.1 q ≠ 0 := by
      intro hzero
      exact hxq (Polynomial.mem_rootSet.mpr ⟨hq.ne_zero, hzero⟩)
    have hlzero : aeval x.1 l = 0 := (mul_eq_zero.mp hxzero).resolve_right hqne
    have hxl : x.1 ∈ l.rootSet K :=
      Polynomial.mem_rootSet.mpr ⟨hlne, hlzero⟩
    have hsplitF : (l.map (algebraMap F F)).Splits := by simpa using hl
    have himage :=
      Splits.image_rootSet_algebraMap (B := K) hsplitF
    rw [← himage] at hxl
    obtain ⟨y, _, hy⟩ := hxl
    calc
      (x : K) ^ (Fintype.card F) ^ n =
          (algebraMap F K y) ^ (Fintype.card F) ^ n := by rw [hy]
      _ = algebraMap F K (y ^ (Fintype.card F) ^ n) := by rw [map_pow]
      _ = algebraMap F K y := by rw [FiniteField.pow_card_pow]
      _ = x := hy
  exact finiteFieldFrobPermIn_isCycle_of_irreducible_factor
    (l * q) q (mul_ne_zero hlne hq.ne_zero) hq n hn hqdeg hdiv hcard hother

end Biunimodular.F11
