/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs27Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs27OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair14_15S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 13 14
    (rationalSparsePolynomial homogeneousCompletion4Pair14_15U) (rationalSparsePolynomial homogeneousCompletion4Pair14_15V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair14_15D k))

theorem homogeneousCompletion4Pair14_15_relation : (∑ k, homogeneousCompletion4Pair14_15S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair14_15S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair14_15U homogeneousCompletion4Pair14_15V
    (homogeneousCompletion4G 13) (homogeneousCompletion4G 14) homogeneousCompletion4Pair14_15D homogeneousCompletion4G homogeneousCompletion4Pair14_15_sp_check

theorem homogeneousCompletion4Pair14_15_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair14_15S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair14_15S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair14_15U homogeneousCompletion4Pair14_15V
    (homogeneousCompletion4M (Fin.last 3) 13) (homogeneousCompletion4M (Fin.last 3) 14)
    homogeneousCompletion4Pair14_15D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair14_15W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair14_15_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair14_15D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair14_15_top :
    homogeneousCompletion4Pair14_15S 14 * homogeneousCompletion4GPoly 14 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair14_15S 14 * homogeneousCompletion4GPoly 14) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair14_15S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair14_15S 14 := by
  have hL0 : homogeneousCompletion4Pair14_15L = homogeneousExponentSup (homogeneousCompletion4Leading 13) (homogeneousCompletion4Leading 14) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair14_15L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 3, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair14_15L (homogeneousCompletion4Leading 13) := by native_decide
  have hV0 : (⟨0, 0, 3, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair14_15L (homogeneousCompletion4Leading 14) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair14_15U =
      monomial (homogeneousExponent homogeneousCompletion4Pair14_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair14_15_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair14_15V =
      monomial (homogeneousExponent homogeneousCompletion4Pair14_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair14_15_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair14_15D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair14_15D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair14_15L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair14_15D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair14_15L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair14_15_degree_bounds_check k)
  unfold homogeneousCompletion4Pair14_15S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair14_15D k)) 13 14 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
