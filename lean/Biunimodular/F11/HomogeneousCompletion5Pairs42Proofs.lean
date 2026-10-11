/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs42Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs42OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair8_12S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 11
    (rationalSparsePolynomial homogeneousCompletion5Pair8_12U) (rationalSparsePolynomial homogeneousCompletion5Pair8_12V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_12D k))

theorem homogeneousCompletion5Pair8_12_relation : (∑ k, homogeneousCompletion5Pair8_12S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair8_12S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair8_12U homogeneousCompletion5Pair8_12V
    (homogeneousCompletion5G 7) (homogeneousCompletion5G 11) homogeneousCompletion5Pair8_12D homogeneousCompletion5G homogeneousCompletion5Pair8_12_sp_check

theorem homogeneousCompletion5Pair8_12_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair8_12S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair8_12S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair8_12U homogeneousCompletion5Pair8_12V
    (homogeneousCompletion5M (Fin.last 4) 7) (homogeneousCompletion5M (Fin.last 4) 11)
    homogeneousCompletion5Pair8_12D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair8_12W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair8_12_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair8_12D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair8_12_top :
    homogeneousCompletion5Pair8_12S 11 * homogeneousCompletion5GPoly 11 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair8_12S 11 * homogeneousCompletion5GPoly 11) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_12S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_12S 11 := by
  have hL0 : homogeneousCompletion5Pair8_12L = homogeneousExponentSup (homogeneousCompletion5Leading 7) (homogeneousCompletion5Leading 11) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair8_12L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_12L (homogeneousCompletion5Leading 7) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_12L (homogeneousCompletion5Leading 11) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair8_12U =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_12_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair8_12V =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_12_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair8_12D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair8_12D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair8_12L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair8_12D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair8_12L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair8_12_degree_bounds_check k)
  unfold homogeneousCompletion5Pair8_12S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_12D k)) 7 11 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair8_13S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 12
    (rationalSparsePolynomial homogeneousCompletion5Pair8_13U) (rationalSparsePolynomial homogeneousCompletion5Pair8_13V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_13D k))

theorem homogeneousCompletion5Pair8_13_relation : (∑ k, homogeneousCompletion5Pair8_13S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair8_13S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair8_13U homogeneousCompletion5Pair8_13V
    (homogeneousCompletion5G 7) (homogeneousCompletion5G 12) homogeneousCompletion5Pair8_13D homogeneousCompletion5G homogeneousCompletion5Pair8_13_sp_check

theorem homogeneousCompletion5Pair8_13_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair8_13S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair8_13S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair8_13U homogeneousCompletion5Pair8_13V
    (homogeneousCompletion5M (Fin.last 4) 7) (homogeneousCompletion5M (Fin.last 4) 12)
    homogeneousCompletion5Pair8_13D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair8_13W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair8_13_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair8_13D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair8_13_top :
    homogeneousCompletion5Pair8_13S 12 * homogeneousCompletion5GPoly 12 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair8_13S 12 * homogeneousCompletion5GPoly 12) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_13S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_13S 12 := by
  have hL0 : homogeneousCompletion5Pair8_13L = homogeneousExponentSup (homogeneousCompletion5Leading 7) (homogeneousCompletion5Leading 12) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair8_13L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_13L (homogeneousCompletion5Leading 7) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_13L (homogeneousCompletion5Leading 12) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair8_13U =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_13_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair8_13V =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_13_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair8_13D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair8_13D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair8_13L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair8_13D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair8_13L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair8_13_degree_bounds_check k)
  unfold homogeneousCompletion5Pair8_13S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_13D k)) 7 12 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair8_14S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 13
    (rationalSparsePolynomial homogeneousCompletion5Pair8_14U) (rationalSparsePolynomial homogeneousCompletion5Pair8_14V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_14D k))

theorem homogeneousCompletion5Pair8_14_relation : (∑ k, homogeneousCompletion5Pair8_14S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair8_14S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair8_14U homogeneousCompletion5Pair8_14V
    (homogeneousCompletion5G 7) (homogeneousCompletion5G 13) homogeneousCompletion5Pair8_14D homogeneousCompletion5G homogeneousCompletion5Pair8_14_sp_check

theorem homogeneousCompletion5Pair8_14_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair8_14S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair8_14S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair8_14U homogeneousCompletion5Pair8_14V
    (homogeneousCompletion5M (Fin.last 4) 7) (homogeneousCompletion5M (Fin.last 4) 13)
    homogeneousCompletion5Pair8_14D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair8_14W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair8_14_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair8_14D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair8_14_top :
    homogeneousCompletion5Pair8_14S 13 * homogeneousCompletion5GPoly 13 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair8_14S 13 * homogeneousCompletion5GPoly 13) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_14S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_14S 13 := by
  have hL0 : homogeneousCompletion5Pair8_14L = homogeneousExponentSup (homogeneousCompletion5Leading 7) (homogeneousCompletion5Leading 13) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair8_14L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_14L (homogeneousCompletion5Leading 7) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_14L (homogeneousCompletion5Leading 13) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair8_14U =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_14_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair8_14V =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_14_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair8_14D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair8_14D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair8_14L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair8_14D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair8_14L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair8_14_degree_bounds_check k)
  unfold homogeneousCompletion5Pair8_14S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_14D k)) 7 13 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair8_15S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 14
    (rationalSparsePolynomial homogeneousCompletion5Pair8_15U) (rationalSparsePolynomial homogeneousCompletion5Pair8_15V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_15D k))

theorem homogeneousCompletion5Pair8_15_relation : (∑ k, homogeneousCompletion5Pair8_15S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair8_15S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair8_15U homogeneousCompletion5Pair8_15V
    (homogeneousCompletion5G 7) (homogeneousCompletion5G 14) homogeneousCompletion5Pair8_15D homogeneousCompletion5G homogeneousCompletion5Pair8_15_sp_check

theorem homogeneousCompletion5Pair8_15_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair8_15S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair8_15S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair8_15U homogeneousCompletion5Pair8_15V
    (homogeneousCompletion5M (Fin.last 4) 7) (homogeneousCompletion5M (Fin.last 4) 14)
    homogeneousCompletion5Pair8_15D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair8_15W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair8_15_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair8_15D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair8_15_top :
    homogeneousCompletion5Pair8_15S 14 * homogeneousCompletion5GPoly 14 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair8_15S 14 * homogeneousCompletion5GPoly 14) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 14) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_15S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_15S 14 := by
  have hL0 : homogeneousCompletion5Pair8_15L = homogeneousExponentSup (homogeneousCompletion5Leading 7) (homogeneousCompletion5Leading 14) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair8_15L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 14) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_15L (homogeneousCompletion5Leading 7) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_15L (homogeneousCompletion5Leading 14) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair8_15U =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_15_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair8_15V =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 14)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_15_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair8_15D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair8_15D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair8_15L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair8_15D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair8_15L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair8_15_degree_bounds_check k)
  unfold homogeneousCompletion5Pair8_15S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_15D k)) 7 14 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
