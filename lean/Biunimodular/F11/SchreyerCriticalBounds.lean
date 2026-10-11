/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.SchreyerCriticalReduction
import Biunimodular.F11.CriticalRelationVector

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial
open scoped MonomialOrder

variable {σ K : Type*} [Field K] {n : ℕ}

/-- The degree bounds of an S-polynomial reduction imply the leading-term
conditions required by the universal Schreyer completeness theorem. -/
theorem criticalRelationVector_top (m : MonomialOrder σ)
    (g d : Fin n → MvPolynomial σ K) (i j : Fin n) (hij : i < j)
    (hg : ∀ k, g k ≠ 0)
    (hD : ∀ k, d k * g k = 0 ∨
      m.degree (d k * g k) ≺[m] m.degree (g i) ⊔ m.degree (g j)) :
    let l := m.degree (g i) ⊔ m.degree (g j)
    let u : MvPolynomial σ K := monomial (l - m.degree (g i)) 1
    let v : MvPolynomial σ K := monomial (l - m.degree (g j)) 1
    let s := criticalRelationVector i j u v d
    s j * g j ≠ 0 ∧ m.degree (s j * g j) = l ∧
      ∀ k, schreyerKey m g s k ≤ schreyerKey m g s j := by
  classical
  intro l u v s
  have hne : i ≠ j := ne_of_lt hij
  have hui : u * g i ≠ 0 :=
    mul_ne_zero ((monomial_eq_zero (s := l - m.degree (g i))).not.mpr one_ne_zero) (hg i)
  have hvj : v * g j ≠ 0 :=
    mul_ne_zero ((monomial_eq_zero (s := l - m.degree (g j))).not.mpr one_ne_zero) (hg j)
  have hud : m.degree (u * g i) = l := by
    rw [m.degree_mul (mul_ne_zero_iff.mp hui).1 (hg i)]
    simp only [u, m.degree_monomial, ite_eq_right one_ne_zero]
    exact tsub_add_cancel_of_le le_sup_left
  have hvd : m.degree (v * g j) = l := by
    rw [m.degree_mul (mul_ne_zero_iff.mp hvj).1 (hg j)]
    simp only [v, m.degree_monomial, ite_eq_right one_ne_zero]
    exact tsub_add_cancel_of_le le_sup_right
  have hei : s i * g i = u * g i - d i * g i := by
    simp [s, criticalRelationVector, hne, sub_mul]
  have hej : s j * g j = -(v * g j) - d j * g j := by
    simp [s, criticalRelationVector, hne.symm, sub_mul, neg_mul]
  have hpj : s j * g j ≠ 0 ∧ m.degree (s j * g j) = l := by
    rw [hej]
    obtain hz | hlt := hD j
    · simpa [hz, hvd] using And.intro (neg_ne_zero.mpr hvj) hvd
    have hd : m.degree (-(v * g j) - d j * g j) = l := by
      rw [m.degree_sub_of_lt (by simpa [m.degree_neg, hvd] using hlt), m.degree_neg, hvd]
    refine ⟨?_, hd⟩
    intro hz
    have hc := m.leadingCoeff_sub_of_lt (f := -(v * g j))
      (g := d j * g j) (by simpa [m.degree_neg, hvd] using hlt)
    rw [hz, m.leadingCoeff_zero, m.leadingCoeff_neg] at hc
    exact (m.leadingCoeff_ne_zero_iff.mpr hvj) (neg_eq_zero.mp hc.symm)
  refine ⟨hpj.1, hpj.2, ?_⟩
  intro k
  by_cases hkj : k = j
  · subst k; exact le_rfl
  by_cases hki : k = i
  · subst k
    have hdi : m.degree (s i * g i) = l := by
      rw [hei]
      obtain hz | hlt := hD i
      · simp [hz, hud]
      · rw [m.degree_sub_of_lt (by simpa [hud] using hlt), hud]
    by_cases hz : s i * g i = 0
    · simp [schreyerKey, hz]
    exact (schreyerKey_le_iff m g s i j hz hpj.1).mpr
      (Or.inr ⟨hdi.trans hpj.2.symm, le_of_lt hij⟩)
  have hek : s k * g k = -(d k * g k) := by
    simp [s, criticalRelationVector, hki, hkj, neg_mul]
  obtain hz | hlt := hD k
  · have hs0 : s k * g k = 0 := by rw [hek, hz, neg_zero]
    simp [schreyerKey, hs0]
  by_cases hz : s k * g k = 0
  · simp [schreyerKey, hz]
  apply (schreyerKey_le_iff m g s k j hz hpj.1).mpr
  left
  rw [hek, m.degree_neg, hpj.2]
  exact hlt

end
end Biunimodular.F11
