/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs58Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs58OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair11_25S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 24
    (rationalSparsePolynomial homogeneousCompletion5Pair11_25U) (rationalSparsePolynomial homogeneousCompletion5Pair11_25V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_25D k))

theorem homogeneousCompletion5Pair11_25_relation : (∑ k, homogeneousCompletion5Pair11_25S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair11_25S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair11_25U homogeneousCompletion5Pair11_25V
    (homogeneousCompletion5G 10) (homogeneousCompletion5G 24) homogeneousCompletion5Pair11_25D homogeneousCompletion5G homogeneousCompletion5Pair11_25_sp_check

theorem homogeneousCompletion5Pair11_25_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair11_25S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair11_25S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair11_25U homogeneousCompletion5Pair11_25V
    (homogeneousCompletion5M (Fin.last 4) 10) (homogeneousCompletion5M (Fin.last 4) 24)
    homogeneousCompletion5Pair11_25D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair11_25W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair11_25_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair11_25D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair11_25_top :
    homogeneousCompletion5Pair11_25S 24 * homogeneousCompletion5GPoly 24 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair11_25S 24 * homogeneousCompletion5GPoly 24) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_25S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_25S 24 := by
  have hL0 : homogeneousCompletion5Pair11_25L = homogeneousExponentSup (homogeneousCompletion5Leading 10) (homogeneousCompletion5Leading 24) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair11_25L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_25L (homogeneousCompletion5Leading 10) := by native_decide
  have hV0 : (⟨0, 0, 1, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_25L (homogeneousCompletion5Leading 24) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair11_25U =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_25_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair11_25V =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_25_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair11_25D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair11_25D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair11_25L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair11_25D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair11_25L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair11_25_degree_bounds_check k)
  unfold homogeneousCompletion5Pair11_25S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_25D k)) 10 24 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair11_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 25
    (rationalSparsePolynomial homogeneousCompletion5Pair11_26U) (rationalSparsePolynomial homogeneousCompletion5Pair11_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_26D k))

theorem homogeneousCompletion5Pair11_26_relation : (∑ k, homogeneousCompletion5Pair11_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair11_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair11_26U homogeneousCompletion5Pair11_26V
    (homogeneousCompletion5G 10) (homogeneousCompletion5G 25) homogeneousCompletion5Pair11_26D homogeneousCompletion5G homogeneousCompletion5Pair11_26_sp_check

theorem homogeneousCompletion5Pair11_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair11_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair11_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair11_26U homogeneousCompletion5Pair11_26V
    (homogeneousCompletion5M (Fin.last 4) 10) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair11_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair11_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair11_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair11_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair11_26_top :
    homogeneousCompletion5Pair11_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair11_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_26S 25 := by
  have hL0 : homogeneousCompletion5Pair11_26L = homogeneousExponentSup (homogeneousCompletion5Leading 10) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair11_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 4, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_26L (homogeneousCompletion5Leading 10) := by native_decide
  have hV0 : (⟨0, 1, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair11_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair11_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair11_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair11_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair11_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair11_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair11_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair11_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair11_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_26D k)) 10 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair11_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 26
    (rationalSparsePolynomial homogeneousCompletion5Pair11_27U) (rationalSparsePolynomial homogeneousCompletion5Pair11_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_27D k))

theorem homogeneousCompletion5Pair11_27_relation : (∑ k, homogeneousCompletion5Pair11_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair11_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair11_27U homogeneousCompletion5Pair11_27V
    (homogeneousCompletion5G 10) (homogeneousCompletion5G 26) homogeneousCompletion5Pair11_27D homogeneousCompletion5G homogeneousCompletion5Pair11_27_sp_check

theorem homogeneousCompletion5Pair11_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair11_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair11_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair11_27U homogeneousCompletion5Pair11_27V
    (homogeneousCompletion5M (Fin.last 4) 10) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair11_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair11_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair11_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair11_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair11_27_top :
    homogeneousCompletion5Pair11_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair11_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_27S 26 := by
  have hL0 : homogeneousCompletion5Pair11_27L = homogeneousExponentSup (homogeneousCompletion5Leading 10) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair11_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 6, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_27L (homogeneousCompletion5Leading 10) := by native_decide
  have hV0 : (⟨0, 1, 1, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair11_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair11_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair11_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair11_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair11_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair11_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair11_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair11_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair11_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_27D k)) 10 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair12_13S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 11 12
    (rationalSparsePolynomial homogeneousCompletion5Pair12_13U) (rationalSparsePolynomial homogeneousCompletion5Pair12_13V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair12_13D k))

theorem homogeneousCompletion5Pair12_13_relation : (∑ k, homogeneousCompletion5Pair12_13S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair12_13S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair12_13U homogeneousCompletion5Pair12_13V
    (homogeneousCompletion5G 11) (homogeneousCompletion5G 12) homogeneousCompletion5Pair12_13D homogeneousCompletion5G homogeneousCompletion5Pair12_13_sp_check

theorem homogeneousCompletion5Pair12_13_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair12_13S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair12_13S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair12_13U homogeneousCompletion5Pair12_13V
    (homogeneousCompletion5M (Fin.last 4) 11) (homogeneousCompletion5M (Fin.last 4) 12)
    homogeneousCompletion5Pair12_13D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair12_13W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair12_13_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair12_13D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair12_13_top :
    homogeneousCompletion5Pair12_13S 12 * homogeneousCompletion5GPoly 12 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair12_13S 12 * homogeneousCompletion5GPoly 12) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair12_13S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair12_13S 12 := by
  have hL0 : homogeneousCompletion5Pair12_13L = homogeneousExponentSup (homogeneousCompletion5Leading 11) (homogeneousCompletion5Leading 12) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair12_13L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair12_13L (homogeneousCompletion5Leading 11) := by native_decide
  have hV0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair12_13L (homogeneousCompletion5Leading 12) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair12_13U =
      monomial (homogeneousExponent homogeneousCompletion5Pair12_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair12_13_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair12_13V =
      monomial (homogeneousExponent homogeneousCompletion5Pair12_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair12_13_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair12_13D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair12_13D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair12_13L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair12_13D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair12_13L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair12_13_degree_bounds_check k)
  unfold homogeneousCompletion5Pair12_13S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair12_13D k)) 11 12 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
