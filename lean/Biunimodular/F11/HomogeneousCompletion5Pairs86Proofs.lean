/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs86Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs86OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair22_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 21 26
    (rationalSparsePolynomial homogeneousCompletion5Pair22_27U) (rationalSparsePolynomial homogeneousCompletion5Pair22_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair22_27D k))

theorem homogeneousCompletion5Pair22_27_relation : (∑ k, homogeneousCompletion5Pair22_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair22_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair22_27U homogeneousCompletion5Pair22_27V
    (homogeneousCompletion5G 21) (homogeneousCompletion5G 26) homogeneousCompletion5Pair22_27D homogeneousCompletion5G homogeneousCompletion5Pair22_27_sp_check

theorem homogeneousCompletion5Pair22_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair22_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair22_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair22_27U homogeneousCompletion5Pair22_27V
    (homogeneousCompletion5M (Fin.last 4) 21) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair22_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair22_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair22_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair22_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair22_27_top :
    homogeneousCompletion5Pair22_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair22_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair22_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair22_27S 26 := by
  have hL0 : homogeneousCompletion5Pair22_27L = homogeneousExponentSup (homogeneousCompletion5Leading 21) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair22_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 6, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair22_27L (homogeneousCompletion5Leading 21) := by native_decide
  have hV0 : (⟨0, 0, 4, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair22_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair22_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair22_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair22_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair22_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair22_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair22_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair22_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair22_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair22_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair22_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair22_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair22_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair22_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair22_27D k)) 21 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair23_24S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 22 23
    (rationalSparsePolynomial homogeneousCompletion5Pair23_24U) (rationalSparsePolynomial homogeneousCompletion5Pair23_24V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair23_24D k))

theorem homogeneousCompletion5Pair23_24_relation : (∑ k, homogeneousCompletion5Pair23_24S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair23_24S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair23_24U homogeneousCompletion5Pair23_24V
    (homogeneousCompletion5G 22) (homogeneousCompletion5G 23) homogeneousCompletion5Pair23_24D homogeneousCompletion5G homogeneousCompletion5Pair23_24_sp_check

theorem homogeneousCompletion5Pair23_24_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair23_24S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair23_24S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair23_24U homogeneousCompletion5Pair23_24V
    (homogeneousCompletion5M (Fin.last 4) 22) (homogeneousCompletion5M (Fin.last 4) 23)
    homogeneousCompletion5Pair23_24D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair23_24W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair23_24_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair23_24D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair23_24_top :
    homogeneousCompletion5Pair23_24S 23 * homogeneousCompletion5GPoly 23 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair23_24S 23 * homogeneousCompletion5GPoly 23) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair23_24S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair23_24S 23 := by
  have hL0 : homogeneousCompletion5Pair23_24L = homogeneousExponentSup (homogeneousCompletion5Leading 22) (homogeneousCompletion5Leading 23) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair23_24L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair23_24L (homogeneousCompletion5Leading 22) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair23_24L (homogeneousCompletion5Leading 23) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair23_24U =
      monomial (homogeneousExponent homogeneousCompletion5Pair23_24L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair23_24_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair23_24V =
      monomial (homogeneousExponent homogeneousCompletion5Pair23_24L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair23_24_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair23_24D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair23_24D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair23_24L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair23_24D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair23_24L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair23_24_degree_bounds_check k)
  unfold homogeneousCompletion5Pair23_24S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair23_24D k)) 22 23 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair23_25S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 22 24
    (rationalSparsePolynomial homogeneousCompletion5Pair23_25U) (rationalSparsePolynomial homogeneousCompletion5Pair23_25V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair23_25D k))

theorem homogeneousCompletion5Pair23_25_relation : (∑ k, homogeneousCompletion5Pair23_25S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair23_25S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair23_25U homogeneousCompletion5Pair23_25V
    (homogeneousCompletion5G 22) (homogeneousCompletion5G 24) homogeneousCompletion5Pair23_25D homogeneousCompletion5G homogeneousCompletion5Pair23_25_sp_check

theorem homogeneousCompletion5Pair23_25_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair23_25S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair23_25S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair23_25U homogeneousCompletion5Pair23_25V
    (homogeneousCompletion5M (Fin.last 4) 22) (homogeneousCompletion5M (Fin.last 4) 24)
    homogeneousCompletion5Pair23_25D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair23_25W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair23_25_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair23_25D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair23_25_top :
    homogeneousCompletion5Pair23_25S 24 * homogeneousCompletion5GPoly 24 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair23_25S 24 * homogeneousCompletion5GPoly 24) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair23_25S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair23_25S 24 := by
  have hL0 : homogeneousCompletion5Pair23_25L = homogeneousExponentSup (homogeneousCompletion5Leading 22) (homogeneousCompletion5Leading 24) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair23_25L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair23_25L (homogeneousCompletion5Leading 22) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair23_25L (homogeneousCompletion5Leading 24) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair23_25U =
      monomial (homogeneousExponent homogeneousCompletion5Pair23_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair23_25_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair23_25V =
      monomial (homogeneousExponent homogeneousCompletion5Pair23_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair23_25_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair23_25D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair23_25D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair23_25L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair23_25D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair23_25L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair23_25_degree_bounds_check k)
  unfold homogeneousCompletion5Pair23_25S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair23_25D k)) 22 24 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair23_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 22 25
    (rationalSparsePolynomial homogeneousCompletion5Pair23_26U) (rationalSparsePolynomial homogeneousCompletion5Pair23_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair23_26D k))

theorem homogeneousCompletion5Pair23_26_relation : (∑ k, homogeneousCompletion5Pair23_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair23_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair23_26U homogeneousCompletion5Pair23_26V
    (homogeneousCompletion5G 22) (homogeneousCompletion5G 25) homogeneousCompletion5Pair23_26D homogeneousCompletion5G homogeneousCompletion5Pair23_26_sp_check

theorem homogeneousCompletion5Pair23_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair23_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair23_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair23_26U homogeneousCompletion5Pair23_26V
    (homogeneousCompletion5M (Fin.last 4) 22) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair23_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair23_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair23_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair23_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair23_26_top :
    homogeneousCompletion5Pair23_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair23_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair23_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair23_26S 25 := by
  have hL0 : homogeneousCompletion5Pair23_26L = homogeneousExponentSup (homogeneousCompletion5Leading 22) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair23_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 4, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair23_26L (homogeneousCompletion5Leading 22) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair23_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair23_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair23_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair23_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair23_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair23_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair23_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair23_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair23_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair23_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair23_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair23_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair23_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair23_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair23_26D k)) 22 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
