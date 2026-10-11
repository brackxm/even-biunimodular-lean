/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs54Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs54OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair10_25S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 24
    (rationalSparsePolynomial homogeneousCompletion5Pair10_25U) (rationalSparsePolynomial homogeneousCompletion5Pair10_25V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_25D k))

theorem homogeneousCompletion5Pair10_25_relation : (∑ k, homogeneousCompletion5Pair10_25S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_25S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_25U homogeneousCompletion5Pair10_25V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 24) homogeneousCompletion5Pair10_25D homogeneousCompletion5G homogeneousCompletion5Pair10_25_sp_check

theorem homogeneousCompletion5Pair10_25_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_25S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_25S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_25U homogeneousCompletion5Pair10_25V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 24)
    homogeneousCompletion5Pair10_25D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_25W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_25_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_25D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_25_top :
    homogeneousCompletion5Pair10_25S 24 * homogeneousCompletion5GPoly 24 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_25S 24 * homogeneousCompletion5GPoly 24) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_25S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_25S 24 := by
  have hL0 : homogeneousCompletion5Pair10_25L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 24) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_25L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_25L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 2, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_25L (homogeneousCompletion5Leading 24) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_25U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_25_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_25V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_25_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_25D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_25D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_25L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_25D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_25L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_25_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_25S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_25D k)) 9 24 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair10_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 25
    (rationalSparsePolynomial homogeneousCompletion5Pair10_26U) (rationalSparsePolynomial homogeneousCompletion5Pair10_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_26D k))

theorem homogeneousCompletion5Pair10_26_relation : (∑ k, homogeneousCompletion5Pair10_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_26U homogeneousCompletion5Pair10_26V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 25) homogeneousCompletion5Pair10_26D homogeneousCompletion5G homogeneousCompletion5Pair10_26_sp_check

theorem homogeneousCompletion5Pair10_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_26U homogeneousCompletion5Pair10_26V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair10_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_26_top :
    homogeneousCompletion5Pair10_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_26S 25 := by
  have hL0 : homogeneousCompletion5Pair10_26L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 4, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_26L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_26D k)) 9 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair10_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 26
    (rationalSparsePolynomial homogeneousCompletion5Pair10_27U) (rationalSparsePolynomial homogeneousCompletion5Pair10_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_27D k))

theorem homogeneousCompletion5Pair10_27_relation : (∑ k, homogeneousCompletion5Pair10_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_27U homogeneousCompletion5Pair10_27V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 26) homogeneousCompletion5Pair10_27D homogeneousCompletion5G homogeneousCompletion5Pair10_27_sp_check

theorem homogeneousCompletion5Pair10_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_27U homogeneousCompletion5Pair10_27V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair10_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_27_top :
    homogeneousCompletion5Pair10_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_27S 26 := by
  have hL0 : homogeneousCompletion5Pair10_27L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 6, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_27L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 2, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_27D k)) 9 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair11_12S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 11
    (rationalSparsePolynomial homogeneousCompletion5Pair11_12U) (rationalSparsePolynomial homogeneousCompletion5Pair11_12V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_12D k))

theorem homogeneousCompletion5Pair11_12_relation : (∑ k, homogeneousCompletion5Pair11_12S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair11_12S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair11_12U homogeneousCompletion5Pair11_12V
    (homogeneousCompletion5G 10) (homogeneousCompletion5G 11) homogeneousCompletion5Pair11_12D homogeneousCompletion5G homogeneousCompletion5Pair11_12_sp_check

theorem homogeneousCompletion5Pair11_12_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair11_12S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair11_12S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair11_12U homogeneousCompletion5Pair11_12V
    (homogeneousCompletion5M (Fin.last 4) 10) (homogeneousCompletion5M (Fin.last 4) 11)
    homogeneousCompletion5Pair11_12D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair11_12W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair11_12_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair11_12D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair11_12_top :
    homogeneousCompletion5Pair11_12S 11 * homogeneousCompletion5GPoly 11 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair11_12S 11 * homogeneousCompletion5GPoly 11) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_12S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_12S 11 := by
  have hL0 : homogeneousCompletion5Pair11_12L = homogeneousExponentSup (homogeneousCompletion5Leading 10) (homogeneousCompletion5Leading 11) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair11_12L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_12L (homogeneousCompletion5Leading 10) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_12L (homogeneousCompletion5Leading 11) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair11_12U =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_12_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair11_12V =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_12_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair11_12D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair11_12D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair11_12L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair11_12D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair11_12L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair11_12_degree_bounds_check k)
  unfold homogeneousCompletion5Pair11_12S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_12D k)) 10 11 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
