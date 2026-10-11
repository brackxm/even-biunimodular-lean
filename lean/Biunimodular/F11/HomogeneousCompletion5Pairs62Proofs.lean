/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs62Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs62OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair12_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 11 25
    (rationalSparsePolynomial homogeneousCompletion5Pair12_26U) (rationalSparsePolynomial homogeneousCompletion5Pair12_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair12_26D k))

theorem homogeneousCompletion5Pair12_26_relation : (∑ k, homogeneousCompletion5Pair12_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair12_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair12_26U homogeneousCompletion5Pair12_26V
    (homogeneousCompletion5G 11) (homogeneousCompletion5G 25) homogeneousCompletion5Pair12_26D homogeneousCompletion5G homogeneousCompletion5Pair12_26_sp_check

theorem homogeneousCompletion5Pair12_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair12_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair12_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair12_26U homogeneousCompletion5Pair12_26V
    (homogeneousCompletion5M (Fin.last 4) 11) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair12_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair12_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair12_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair12_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair12_26_top :
    homogeneousCompletion5Pair12_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair12_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair12_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair12_26S 25 := by
  have hL0 : homogeneousCompletion5Pair12_26L = homogeneousExponentSup (homogeneousCompletion5Leading 11) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair12_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 4, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair12_26L (homogeneousCompletion5Leading 11) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair12_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair12_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair12_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair12_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair12_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair12_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair12_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair12_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair12_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair12_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair12_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair12_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair12_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair12_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair12_26D k)) 11 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair12_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 11 26
    (rationalSparsePolynomial homogeneousCompletion5Pair12_27U) (rationalSparsePolynomial homogeneousCompletion5Pair12_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair12_27D k))

theorem homogeneousCompletion5Pair12_27_relation : (∑ k, homogeneousCompletion5Pair12_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair12_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair12_27U homogeneousCompletion5Pair12_27V
    (homogeneousCompletion5G 11) (homogeneousCompletion5G 26) homogeneousCompletion5Pair12_27D homogeneousCompletion5G homogeneousCompletion5Pair12_27_sp_check

theorem homogeneousCompletion5Pair12_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair12_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair12_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair12_27U homogeneousCompletion5Pair12_27V
    (homogeneousCompletion5M (Fin.last 4) 11) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair12_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair12_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair12_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair12_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair12_27_top :
    homogeneousCompletion5Pair12_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair12_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair12_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair12_27S 26 := by
  have hL0 : homogeneousCompletion5Pair12_27L = homogeneousExponentSup (homogeneousCompletion5Leading 11) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair12_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 6, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair12_27L (homogeneousCompletion5Leading 11) := by native_decide
  have hV0 : (⟨0, 2, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair12_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair12_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair12_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair12_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair12_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair12_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair12_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair12_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair12_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair12_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair12_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair12_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair12_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair12_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair12_27D k)) 11 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair13_14S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 12 13
    (rationalSparsePolynomial homogeneousCompletion5Pair13_14U) (rationalSparsePolynomial homogeneousCompletion5Pair13_14V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair13_14D k))

theorem homogeneousCompletion5Pair13_14_relation : (∑ k, homogeneousCompletion5Pair13_14S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair13_14S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair13_14U homogeneousCompletion5Pair13_14V
    (homogeneousCompletion5G 12) (homogeneousCompletion5G 13) homogeneousCompletion5Pair13_14D homogeneousCompletion5G homogeneousCompletion5Pair13_14_sp_check

theorem homogeneousCompletion5Pair13_14_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair13_14S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair13_14S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair13_14U homogeneousCompletion5Pair13_14V
    (homogeneousCompletion5M (Fin.last 4) 12) (homogeneousCompletion5M (Fin.last 4) 13)
    homogeneousCompletion5Pair13_14D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair13_14W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair13_14_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair13_14D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair13_14_top :
    homogeneousCompletion5Pair13_14S 13 * homogeneousCompletion5GPoly 13 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair13_14S 13 * homogeneousCompletion5GPoly 13) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair13_14S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair13_14S 13 := by
  have hL0 : homogeneousCompletion5Pair13_14L = homogeneousExponentSup (homogeneousCompletion5Leading 12) (homogeneousCompletion5Leading 13) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair13_14L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair13_14L (homogeneousCompletion5Leading 12) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair13_14L (homogeneousCompletion5Leading 13) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair13_14U =
      monomial (homogeneousExponent homogeneousCompletion5Pair13_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair13_14_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair13_14V =
      monomial (homogeneousExponent homogeneousCompletion5Pair13_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair13_14_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair13_14D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair13_14D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair13_14L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair13_14D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair13_14L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair13_14_degree_bounds_check k)
  unfold homogeneousCompletion5Pair13_14S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair13_14D k)) 12 13 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair13_15S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 12 14
    (rationalSparsePolynomial homogeneousCompletion5Pair13_15U) (rationalSparsePolynomial homogeneousCompletion5Pair13_15V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair13_15D k))

theorem homogeneousCompletion5Pair13_15_relation : (∑ k, homogeneousCompletion5Pair13_15S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair13_15S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair13_15U homogeneousCompletion5Pair13_15V
    (homogeneousCompletion5G 12) (homogeneousCompletion5G 14) homogeneousCompletion5Pair13_15D homogeneousCompletion5G homogeneousCompletion5Pair13_15_sp_check

theorem homogeneousCompletion5Pair13_15_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair13_15S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair13_15S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair13_15U homogeneousCompletion5Pair13_15V
    (homogeneousCompletion5M (Fin.last 4) 12) (homogeneousCompletion5M (Fin.last 4) 14)
    homogeneousCompletion5Pair13_15D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair13_15W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair13_15_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair13_15D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair13_15_top :
    homogeneousCompletion5Pair13_15S 14 * homogeneousCompletion5GPoly 14 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair13_15S 14 * homogeneousCompletion5GPoly 14) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 14) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair13_15S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair13_15S 14 := by
  have hL0 : homogeneousCompletion5Pair13_15L = homogeneousExponentSup (homogeneousCompletion5Leading 12) (homogeneousCompletion5Leading 14) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair13_15L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 14) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair13_15L (homogeneousCompletion5Leading 12) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair13_15L (homogeneousCompletion5Leading 14) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair13_15U =
      monomial (homogeneousExponent homogeneousCompletion5Pair13_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair13_15_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair13_15V =
      monomial (homogeneousExponent homogeneousCompletion5Pair13_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 14)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair13_15_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair13_15D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair13_15D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair13_15L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair13_15D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair13_15L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair13_15_degree_bounds_check k)
  unfold homogeneousCompletion5Pair13_15S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair13_15D k)) 12 14 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
