/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial
open scoped MonomialOrder

variable {σ K : Type*} [Field K] {n : ℕ}

/-- The weighted leading key of one coefficient of a polynomial relation.
Ties in the monomial order are broken by the generator's index. -/
def schreyerKey (m : MonomialOrder σ) (g v : Fin n → MvPolynomial σ K)
    (i : Fin n) : WithBot (m.syn ×ₗ ℕ) := by
  classical
  exact if v i * g i = 0 then ⊥ else
    ↑(toLex (m.toSyn (m.degree (v i * g i)), i.val))

def schreyerDegree (m : MonomialOrder σ) (g v : Fin n → MvPolynomial σ K) :
    WithBot (m.syn ×ₗ ℕ) :=
  Finset.univ.sup (schreyerKey m g v)

theorem schreyerKey_le_iff (m : MonomialOrder σ)
    (g v : Fin n → MvPolynomial σ K) (i j : Fin n)
    (hi : v i * g i ≠ 0) (hj : v j * g j ≠ 0) :
    schreyerKey m g v i ≤ schreyerKey m g v j ↔
      m.degree (v i * g i) ≺[m] m.degree (v j * g j) ∨
      m.degree (v i * g i) = m.degree (v j * g j) ∧ i.val ≤ j.val := by
  classical
  simp only [schreyerKey, ite_eq_right hi, ite_eq_right hj, WithBot.coe_le_coe,
    Prod.Lex.toLex_le_toLex, EmbeddingLike.apply_eq_iff_eq]

/-- The largest weighted term in a nonzero polynomial relation has another
term with the same monomial degree and a smaller generator index. This is
the universal cancellation fact behind the finite critical-pair check. -/
theorem schreyer_relation_top_pair (m : MonomialOrder σ)
    (g v : Fin n → MvPolynomial σ K) (hg : ∀ i, g i ≠ 0)
    (hv : v ≠ 0) (hrelation : (∑ i, v i * g i) = 0) :
    ∃ i j : Fin n, i < j ∧ v i ≠ 0 ∧ v j ≠ 0 ∧
      m.degree (v i * g i) = m.degree (v j * g j) ∧
      schreyerDegree m g v = schreyerKey m g v j := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := ⟨k, Finset.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ hnonempty (schreyerKey m g v)
  have htop : (⊥ : WithBot (m.syn ×ₗ ℕ)) < schreyerDegree m g v := by
    have hp : v k * g k ≠ 0 := mul_ne_zero hk (hg k)
    have hkey : ⊥ < schreyerKey m g v k := by
      simp only [schreyerKey, ite_eq_right hp]
      exact WithBot.bot_lt_coe _
    exact lt_of_lt_of_le hkey (Finset.le_sup (f := schreyerKey m g v) (Finset.mem_univ k))
  have hjp : v j * g j ≠ 0 := by
    intro hz
    have hb : schreyerKey m g v j = ⊥ := by simp [schreyerKey, hz]
    change (⊥ : WithBot (m.syn ×ₗ ℕ)) < Finset.univ.sup (schreyerKey m g v) at htop
    rw [hj, hb] at htop
    exact (lt_irrefl _) htop
  have hbound (i : Fin n) : schreyerKey m g v i ≤ schreyerKey m g v j := by
    rw [← hj]
    exact Finset.le_sup (f := schreyerKey m g v) (Finset.mem_univ i)
  have hex : ∃ i : Fin n, i ≠ j ∧ v i * g i ≠ 0 ∧
      m.degree (v i * g i) = m.degree (v j * g j) := by
    by_contra hn
    have hcoeff (i : Fin n) (hij : i ≠ j) :
        (v i * g i).coeff (m.degree (v j * g j)) = 0 := by
      by_cases hp : v i * g i = 0
      · simp [hp]
      have hne : m.degree (v i * g i) ≠ m.degree (v j * g j) := by
        intro h
        exact hn ⟨i, hij, hp, h⟩
      obtain hlt | ⟨heq, _⟩ := (schreyerKey_le_iff m g v i j hp hjp).mp (hbound i)
      · exact m.coeff_eq_zero_of_lt hlt
      · exact (hne heq).elim
    have hz : (∑ i, (v i * g i).coeff (m.degree (v j * g j))) = 0 := by
      simpa [coeff_sum] using
        congrArg (fun p : MvPolynomial σ K => p.coeff (m.degree (v j * g j))) hrelation
    rw [Finset.sum_eq_single j (by intro i _ hi; exact hcoeff i hi) (by simp)] at hz
    exact (m.coeff_degree_ne_zero_iff.mpr hjp) hz
  obtain ⟨i, hij, hip, hdegree⟩ := hex
  have hindex : i.val ≤ j.val := by
    obtain hlt | ⟨_, hi⟩ := (schreyerKey_le_iff m g v i j hip hjp).mp (hbound i)
    · simp only [hdegree] at hlt
      exact (lt_irrefl _ hlt).elim
    · exact hi
  exact ⟨i, j, lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr hindex) hij,
    (mul_ne_zero_iff.mp hip).1, (mul_ne_zero_iff.mp hjp).1, hdegree, hj⟩

end
end Biunimodular.F11
