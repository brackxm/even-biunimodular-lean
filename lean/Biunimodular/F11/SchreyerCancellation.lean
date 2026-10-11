/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.SchreyerDescent

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial
open scoped MonomialOrder

variable {σ K : Type*} [Field K] {n : ℕ}

/-- Cancelling the coefficient at an upper degree bound either gives zero
or strictly decreases the degree. This includes the constant-degree case. -/
theorem monomialOrder_sub_cancel (m : MonomialOrder σ)
    (f h : MvPolynomial σ K) (d : σ →₀ ℕ)
    (hf : m.degree f ≼[m] d) (hh : m.degree h ≼[m] d)
    (hc : f.coeff d = h.coeff d) :
    f - h = 0 ∨ m.degree (f - h) ≺[m] d := by
  by_cases hz : f - h = 0
  · exact Or.inl hz
  right
  have hle : m.degree (f - h) ≼[m] d :=
    m.degree_sub_le.trans (sup_le hf hh)
  apply lt_of_le_of_ne hle
  intro heq
  have he : m.degree (f - h) = d := m.toSyn.injective heq
  have hn := m.coeff_degree_ne_zero_iff.mpr hz
  rw [he, coeff_sub, hc, sub_self] at hn
  exact hn rfl

/-- Executable critical-pair bounds can be used through this exact
characterization of the weighted leading key. -/
theorem schreyerKey_lt_bound (m : MonomialOrder σ)
    (g v : Fin n → MvPolynomial σ K) (k : Fin n)
    (d : σ →₀ ℕ) (j : ℕ) :
    schreyerKey m g v k < (↑(toLex (m.toSyn d, j)) : WithBot (m.syn ×ₗ ℕ)) ↔
      v k * g k = 0 ∨ m.degree (v k * g k) ≺[m] d ∨
        m.degree (v k * g k) = d ∧ k.val < j := by
  classical
  by_cases hz : v k * g k = 0
  · simp [schreyerKey, hz]
  simp only [schreyerKey, hz, ite_false, WithBot.coe_lt_coe,
    Prod.Lex.toLex_lt_toLex, EmbeddingLike.apply_eq_iff_eq, false_or]

theorem schreyerDegree_lt_bound (m : MonomialOrder σ)
    (g v : Fin n → MvPolynomial σ K) (d : σ →₀ ℕ) (j : ℕ)
    (h : ∀ k, v k * g k = 0 ∨ m.degree (v k * g k) ≺[m] d ∨
      m.degree (v k * g k) = d ∧ k.val < j) :
    schreyerDegree m g v < (↑(toLex (m.toSyn d, j)) : WithBot (m.syn ×ₗ ℕ)) := by
  classical
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro k _
  exact (schreyerKey_lt_bound m g v k d j).mpr (h k)

end
end Biunimodular.F11
