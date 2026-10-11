/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs25Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs25OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair11_13S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 12
    (rationalSparsePolynomial homogeneousCompletion4Pair11_13U) (rationalSparsePolynomial homogeneousCompletion4Pair11_13V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair11_13D k))

theorem homogeneousCompletion4Pair11_13_relation : (∑ k, homogeneousCompletion4Pair11_13S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair11_13S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair11_13U homogeneousCompletion4Pair11_13V
    (homogeneousCompletion4G 10) (homogeneousCompletion4G 12) homogeneousCompletion4Pair11_13D homogeneousCompletion4G homogeneousCompletion4Pair11_13_sp_check

theorem homogeneousCompletion4Pair11_13_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair11_13S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair11_13S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair11_13U homogeneousCompletion4Pair11_13V
    (homogeneousCompletion4M (Fin.last 3) 10) (homogeneousCompletion4M (Fin.last 3) 12)
    homogeneousCompletion4Pair11_13D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair11_13W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair11_13_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair11_13D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair11_13_top :
    homogeneousCompletion4Pair11_13S 12 * homogeneousCompletion4GPoly 12 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair11_13S 12 * homogeneousCompletion4GPoly 12) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair11_13S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair11_13S 12 := by
  have hL0 : homogeneousCompletion4Pair11_13L = homogeneousExponentSup (homogeneousCompletion4Leading 10) (homogeneousCompletion4Leading 12) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair11_13L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair11_13L (homogeneousCompletion4Leading 10) := by native_decide
  have hV0 : (⟨0, 0, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair11_13L (homogeneousCompletion4Leading 12) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair11_13U =
      monomial (homogeneousExponent homogeneousCompletion4Pair11_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair11_13_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair11_13V =
      monomial (homogeneousExponent homogeneousCompletion4Pair11_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair11_13_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair11_13D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair11_13D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair11_13L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair11_13D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair11_13L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair11_13_degree_bounds_check k)
  unfold homogeneousCompletion4Pair11_13S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair11_13D k)) 10 12 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair11_14S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 13
    (rationalSparsePolynomial homogeneousCompletion4Pair11_14U) (rationalSparsePolynomial homogeneousCompletion4Pair11_14V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair11_14D k))

theorem homogeneousCompletion4Pair11_14_relation : (∑ k, homogeneousCompletion4Pair11_14S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair11_14S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair11_14U homogeneousCompletion4Pair11_14V
    (homogeneousCompletion4G 10) (homogeneousCompletion4G 13) homogeneousCompletion4Pair11_14D homogeneousCompletion4G homogeneousCompletion4Pair11_14_sp_check

theorem homogeneousCompletion4Pair11_14_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair11_14S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair11_14S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair11_14U homogeneousCompletion4Pair11_14V
    (homogeneousCompletion4M (Fin.last 3) 10) (homogeneousCompletion4M (Fin.last 3) 13)
    homogeneousCompletion4Pair11_14D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair11_14W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair11_14_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair11_14D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair11_14_top :
    homogeneousCompletion4Pair11_14S 13 * homogeneousCompletion4GPoly 13 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair11_14S 13 * homogeneousCompletion4GPoly 13) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair11_14S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair11_14S 13 := by
  have hL0 : homogeneousCompletion4Pair11_14L = homogeneousExponentSup (homogeneousCompletion4Leading 10) (homogeneousCompletion4Leading 13) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair11_14L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair11_14L (homogeneousCompletion4Leading 10) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair11_14L (homogeneousCompletion4Leading 13) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair11_14U =
      monomial (homogeneousExponent homogeneousCompletion4Pair11_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair11_14_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair11_14V =
      monomial (homogeneousExponent homogeneousCompletion4Pair11_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair11_14_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair11_14D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair11_14D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair11_14L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair11_14D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair11_14L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair11_14_degree_bounds_check k)
  unfold homogeneousCompletion4Pair11_14S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair11_14D k)) 10 13 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair11_15S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 14
    (rationalSparsePolynomial homogeneousCompletion4Pair11_15U) (rationalSparsePolynomial homogeneousCompletion4Pair11_15V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair11_15D k))

theorem homogeneousCompletion4Pair11_15_relation : (∑ k, homogeneousCompletion4Pair11_15S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair11_15S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair11_15U homogeneousCompletion4Pair11_15V
    (homogeneousCompletion4G 10) (homogeneousCompletion4G 14) homogeneousCompletion4Pair11_15D homogeneousCompletion4G homogeneousCompletion4Pair11_15_sp_check

theorem homogeneousCompletion4Pair11_15_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair11_15S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair11_15S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair11_15U homogeneousCompletion4Pair11_15V
    (homogeneousCompletion4M (Fin.last 3) 10) (homogeneousCompletion4M (Fin.last 3) 14)
    homogeneousCompletion4Pair11_15D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair11_15W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair11_15_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair11_15D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair11_15_top :
    homogeneousCompletion4Pair11_15S 14 * homogeneousCompletion4GPoly 14 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair11_15S 14 * homogeneousCompletion4GPoly 14) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair11_15S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair11_15S 14 := by
  have hL0 : homogeneousCompletion4Pair11_15L = homogeneousExponentSup (homogeneousCompletion4Leading 10) (homogeneousCompletion4Leading 14) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair11_15L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair11_15L (homogeneousCompletion4Leading 10) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair11_15L (homogeneousCompletion4Leading 14) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair11_15U =
      monomial (homogeneousExponent homogeneousCompletion4Pair11_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair11_15_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair11_15V =
      monomial (homogeneousExponent homogeneousCompletion4Pair11_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair11_15_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair11_15D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair11_15D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair11_15L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair11_15D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair11_15L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair11_15_degree_bounds_check k)
  unfold homogeneousCompletion4Pair11_15S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair11_15D k)) 10 14 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair12_13S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 11 12
    (rationalSparsePolynomial homogeneousCompletion4Pair12_13U) (rationalSparsePolynomial homogeneousCompletion4Pair12_13V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair12_13D k))

theorem homogeneousCompletion4Pair12_13_relation : (∑ k, homogeneousCompletion4Pair12_13S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair12_13S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair12_13U homogeneousCompletion4Pair12_13V
    (homogeneousCompletion4G 11) (homogeneousCompletion4G 12) homogeneousCompletion4Pair12_13D homogeneousCompletion4G homogeneousCompletion4Pair12_13_sp_check

theorem homogeneousCompletion4Pair12_13_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair12_13S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair12_13S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair12_13U homogeneousCompletion4Pair12_13V
    (homogeneousCompletion4M (Fin.last 3) 11) (homogeneousCompletion4M (Fin.last 3) 12)
    homogeneousCompletion4Pair12_13D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair12_13W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair12_13_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair12_13D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair12_13_top :
    homogeneousCompletion4Pair12_13S 12 * homogeneousCompletion4GPoly 12 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair12_13S 12 * homogeneousCompletion4GPoly 12) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair12_13S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair12_13S 12 := by
  have hL0 : homogeneousCompletion4Pair12_13L = homogeneousExponentSup (homogeneousCompletion4Leading 11) (homogeneousCompletion4Leading 12) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair12_13L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair12_13L (homogeneousCompletion4Leading 11) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair12_13L (homogeneousCompletion4Leading 12) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair12_13U =
      monomial (homogeneousExponent homogeneousCompletion4Pair12_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair12_13_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair12_13V =
      monomial (homogeneousExponent homogeneousCompletion4Pair12_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair12_13_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair12_13D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair12_13D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair12_13L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair12_13D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair12_13L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair12_13_degree_bounds_check k)
  unfold homogeneousCompletion4Pair12_13S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair12_13D k)) 11 12 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
