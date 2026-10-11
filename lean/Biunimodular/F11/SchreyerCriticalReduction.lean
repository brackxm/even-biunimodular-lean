/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.SchreyerCancellation

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial
open scoped MonomialOrder

variable {σ K : Type*} [Field K] {n : ℕ}

/-- A critical relation with the required weighted leading term reduces any
relation with a divisible matching top term. All assumptions here are leading
term bounds, rather than an assumption that arbitrary relations are generated. -/
theorem schreyer_reduce_of_matching_top (m : MonomialOrder σ)
    (g v s : Fin n → MvPolynomial σ K) (j : Fin n)
    (d l : σ →₀ ℕ) (hl : l ≤ d)
    (hvj : v j * g j ≠ 0) (hsj : s j * g j ≠ 0)
    (hvd : m.degree (v j * g j) = d) (hsd : m.degree (s j * g j) = l)
    (hvtop : schreyerDegree m g v = schreyerKey m g v j)
    (hstop : ∀ k, schreyerKey m g s k ≤ schreyerKey m g s j) :
    ∃ q : MvPolynomial σ K,
      schreyerDegree m g (v - q • s) < schreyerDegree m g v := by
  classical
  let c : K := m.leadingCoeff (v j * g j) / m.leadingCoeff (s j * g j)
  have hvc : m.leadingCoeff (v j * g j) ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hvj
  have hsc : m.leadingCoeff (s j * g j) ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hsj
  have hc : c ≠ 0 := div_ne_zero hvc hsc
  let q : MvPolynomial σ K := monomial (d - l) c
  have hq : q ≠ 0 := (monomial_eq_zero (s := d - l)).not.mpr hc
  have hqd : m.degree q = d - l := by simp [q, m.degree_monomial, hc]
  have hqj : m.degree (q * (s j * g j)) = d := by
    rw [m.degree_mul hq hsj, hqd, hsd, tsub_add_cancel_of_le hl]
  have hcoeff : (v j * g j).coeff d = (q * (s j * g j)).coeff d := by
    have hlc : m.leadingCoeff (q * (s j * g j)) = m.leadingCoeff (v j * g j) := by
      rw [m.leadingCoeff_mul]
      change m.leadingCoeff (monomial (d - l) c) * m.leadingCoeff (s j * g j) = _
      rw [m.leadingCoeff_monomial]
      exact div_mul_cancel₀ _ hsc
    simpa only [MonomialOrder.leadingCoeff, hvd, hqj] using hlc.symm
  have hvl (k : Fin n) (hk : v k * g k ≠ 0) :
      m.degree (v k * g k) ≺[m] d ∨
        m.degree (v k * g k) = d ∧ k.val ≤ j.val := by
    have hkey : schreyerKey m g v k ≤ schreyerKey m g v j := by
      rw [← hvtop]
      exact Finset.le_sup (f := schreyerKey m g v) (Finset.mem_univ k)
    simpa only [hvd] using (schreyerKey_le_iff m g v k j hk hvj).mp hkey
  have hsl (k : Fin n) (hk : s k * g k ≠ 0) :
      m.degree (s k * g k) ≺[m] l ∨
        m.degree (s k * g k) = l ∧ k.val ≤ j.val := by
    simpa only [hsd] using (schreyerKey_le_iff m g s k j hk hsj).mp (hstop k)
  have hqbound (k : Fin n) (hk : q * (s k * g k) ≠ 0) :
      m.degree (q * (s k * g k)) ≺[m] d ∨
        m.degree (q * (s k * g k)) = d ∧ k.val ≤ j.val := by
    have hsk := (mul_ne_zero_iff.mp hk).2
    rw [m.degree_mul hq hsk, hqd]
    obtain hlt | ⟨heq, hi⟩ := hsl k hsk
    · left
      have heq : m.toSyn (d - l + l) = m.toSyn d :=
        congrArg m.toSyn (tsub_add_cancel_of_le hl)
      rw [← heq, map_add, map_add]
      simpa only [add_comm] using add_lt_add_left hlt (m.toSyn (d - l))
    · exact Or.inr ⟨by rw [heq, tsub_add_cancel_of_le hl], hi⟩
  refine ⟨q, ?_⟩
  rw [hvtop]
  simp only [schreyerKey, ite_eq_right hvj, hvd]
  apply schreyerDegree_lt_bound
  intro k
  have hexp : (v - q • s) k * g k = v k * g k - q * (s k * g k) := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexp]
  by_cases hz : v k * g k - q * (s k * g k) = 0
  · exact Or.inl hz
  right
  have hvle : m.degree (v k * g k) ≼[m] d := by
    by_cases hk : v k * g k = 0
    · simp [hk]
    exact (hvl k hk).elim le_of_lt (fun h => le_of_eq (congrArg m.toSyn h.1))
  have hqle : m.degree (q * (s k * g k)) ≼[m] d := by
    by_cases hk : q * (s k * g k) = 0
    · simp [hk]
    exact (hqbound k hk).elim le_of_lt (fun h => le_of_eq (congrArg m.toSyn h.1))
  by_cases hkj : k = j
  · subst k
    exact Or.inl ((monomialOrder_sub_cancel m _ _ d hvle hqle hcoeff).resolve_left hz)
  by_cases hindex : k.val < j.val
  · have hle := m.degree_sub_le.trans (sup_le hvle hqle)
    obtain hlt | heq := lt_or_eq_of_le hle
    · exact Or.inl hlt
    · exact Or.inr ⟨m.toSyn.injective heq, hindex⟩
  have hgt : j.val < k.val := by
    have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    omega
  by_cases hvk : v k * g k = 0
  · by_cases hqk : q * (s k * g k) = 0
    · exact (hz (by rw [hvk, hqk, sub_self])).elim
    have hlt : m.degree (q * (s k * g k)) ≺[m] d := by
      obtain h | ⟨_, hi⟩ := hqbound k hqk
      · exact h
      · omega
    simp only [hvk, zero_sub, m.degree_neg]
    exact Or.inl hlt
  by_cases hqk : q * (s k * g k) = 0
  · have hlt : m.degree (v k * g k) ≺[m] d := by
      obtain h | ⟨_, hi⟩ := hvl k hvk
      · exact h
      · omega
    simp only [hqk, sub_zero]
    exact Or.inl hlt
  have hvlt : m.degree (v k * g k) ≺[m] d := by
    obtain h | ⟨_, hi⟩ := hvl k hvk
    · exact h
    · omega
  have hqlt : m.degree (q * (s k * g k)) ≺[m] d := by
    obtain h | ⟨_, hi⟩ := hqbound k hqk
    · exact h
    · omega
  exact Or.inl (lt_of_le_of_lt m.degree_sub_le (max_lt hvlt hqlt))

/-- The finite critical-pair obligations imply completeness for arbitrary
polynomial relations. The least-common-multiple degree is forced by the two
top components of a relation; no finite-degree cutoff is used. -/
theorem schreyer_relations_generate_of_critical_pairs {ι : Type*}
    (m : MonomialOrder σ) (g : Fin n → MvPolynomial σ K)
    (s : ι → Fin n → MvPolynomial σ K)
    (hg : ∀ k, g k ≠ 0)
    (hs : ∀ r, (∑ k, s r k * g k) = 0)
    (hcover : ∀ i j : Fin n, i < j → ∃ r,
      s r j * g j ≠ 0 ∧
      m.degree (s r j * g j) = m.degree (g i) ⊔ m.degree (g j) ∧
      ∀ k, schreyerKey m g (s r) k ≤ schreyerKey m g (s r) j) :
    LinearMap.ker (polynomialRelationMap g) =
      Submodule.span (MvPolynomial σ K) (Set.range s) := by
  apply schreyer_relations_generate_of_descent m g s hs
  intro v hv hrelation
  obtain ⟨i, j, hij, hvi, hvj, hdeg, htop⟩ :=
    schreyer_relation_top_pair m g v hg hv hrelation
  obtain ⟨r, hsj, hsd, hstop⟩ := hcover i j hij
  have hli : m.degree (g i) ≤ m.degree (v j * g j) := by
    rw [← hdeg, m.degree_mul hvi (hg i)]
    exact le_add_self
  have hlj : m.degree (g j) ≤ m.degree (v j * g j) := by
    rw [m.degree_mul hvj (hg j)]
    exact le_add_self
  obtain ⟨q, hq⟩ := schreyer_reduce_of_matching_top m g v (s r) j
    (m.degree (v j * g j)) (m.degree (g i) ⊔ m.degree (g j))
    (sup_le hli hlj) (mul_ne_zero hvj (hg j)) hsj rfl hsd htop hstop
  exact ⟨r, q, hq⟩

end
end Biunimodular.F11
