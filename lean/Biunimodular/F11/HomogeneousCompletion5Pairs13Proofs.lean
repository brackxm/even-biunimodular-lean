/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs13Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs13OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair2_25S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 24
    (rationalSparsePolynomial homogeneousCompletion5Pair2_25U) (rationalSparsePolynomial homogeneousCompletion5Pair2_25V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_25D k))

theorem homogeneousCompletion5Pair2_25_relation : (∑ k, homogeneousCompletion5Pair2_25S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair2_25S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair2_25U homogeneousCompletion5Pair2_25V
    (homogeneousCompletion5G 1) (homogeneousCompletion5G 24) homogeneousCompletion5Pair2_25D homogeneousCompletion5G homogeneousCompletion5Pair2_25_sp_check

theorem homogeneousCompletion5Pair2_25_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair2_25S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair2_25S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair2_25U homogeneousCompletion5Pair2_25V
    (homogeneousCompletion5M (Fin.last 4) 1) (homogeneousCompletion5M (Fin.last 4) 24)
    homogeneousCompletion5Pair2_25D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair2_25W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair2_25_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair2_25D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair2_25_top :
    homogeneousCompletion5Pair2_25S 24 * homogeneousCompletion5GPoly 24 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair2_25S 24 * homogeneousCompletion5GPoly 24) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_25S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_25S 24 := by
  have hL0 : homogeneousCompletion5Pair2_25L = homogeneousExponentSup (homogeneousCompletion5Leading 1) (homogeneousCompletion5Leading 24) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair2_25L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_25L (homogeneousCompletion5Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_25L (homogeneousCompletion5Leading 24) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair2_25U =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_25_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair2_25V =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_25_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair2_25D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair2_25D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair2_25L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair2_25D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair2_25L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair2_25_degree_bounds_check k)
  unfold homogeneousCompletion5Pair2_25S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_25D k)) 1 24 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair2_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 25
    (rationalSparsePolynomial homogeneousCompletion5Pair2_26U) (rationalSparsePolynomial homogeneousCompletion5Pair2_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_26D k))

theorem homogeneousCompletion5Pair2_26_relation : (∑ k, homogeneousCompletion5Pair2_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair2_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair2_26U homogeneousCompletion5Pair2_26V
    (homogeneousCompletion5G 1) (homogeneousCompletion5G 25) homogeneousCompletion5Pair2_26D homogeneousCompletion5G homogeneousCompletion5Pair2_26_sp_check

theorem homogeneousCompletion5Pair2_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair2_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair2_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair2_26U homogeneousCompletion5Pair2_26V
    (homogeneousCompletion5M (Fin.last 4) 1) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair2_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair2_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair2_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair2_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair2_26_top :
    homogeneousCompletion5Pair2_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair2_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_26S 25 := by
  have hL0 : homogeneousCompletion5Pair2_26L = homogeneousExponentSup (homogeneousCompletion5Leading 1) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair2_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 4, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_26L (homogeneousCompletion5Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair2_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair2_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair2_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair2_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair2_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair2_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair2_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair2_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair2_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_26D k)) 1 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair2_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 26
    (rationalSparsePolynomial homogeneousCompletion5Pair2_27U) (rationalSparsePolynomial homogeneousCompletion5Pair2_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_27D k))

theorem homogeneousCompletion5Pair2_27_relation : (∑ k, homogeneousCompletion5Pair2_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair2_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair2_27U homogeneousCompletion5Pair2_27V
    (homogeneousCompletion5G 1) (homogeneousCompletion5G 26) homogeneousCompletion5Pair2_27D homogeneousCompletion5G homogeneousCompletion5Pair2_27_sp_check

theorem homogeneousCompletion5Pair2_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair2_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair2_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair2_27U homogeneousCompletion5Pair2_27V
    (homogeneousCompletion5M (Fin.last 4) 1) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair2_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair2_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair2_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair2_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair2_27_top :
    homogeneousCompletion5Pair2_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair2_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_27S 26 := by
  have hL0 : homogeneousCompletion5Pair2_27L = homogeneousExponentSup (homogeneousCompletion5Leading 1) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair2_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 6, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_27L (homogeneousCompletion5Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair2_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair2_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair2_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair2_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair2_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair2_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair2_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair2_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair2_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_27D k)) 1 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair3_4S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 3
    (rationalSparsePolynomial homogeneousCompletion5Pair3_4U) (rationalSparsePolynomial homogeneousCompletion5Pair3_4V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_4D k))

theorem homogeneousCompletion5Pair3_4_relation : (∑ k, homogeneousCompletion5Pair3_4S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair3_4S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair3_4U homogeneousCompletion5Pair3_4V
    (homogeneousCompletion5G 2) (homogeneousCompletion5G 3) homogeneousCompletion5Pair3_4D homogeneousCompletion5G homogeneousCompletion5Pair3_4_sp_check

theorem homogeneousCompletion5Pair3_4_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair3_4S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair3_4S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair3_4U homogeneousCompletion5Pair3_4V
    (homogeneousCompletion5M (Fin.last 4) 2) (homogeneousCompletion5M (Fin.last 4) 3)
    homogeneousCompletion5Pair3_4D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair3_4W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair3_4_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair3_4D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair3_4_top :
    homogeneousCompletion5Pair3_4S 3 * homogeneousCompletion5GPoly 3 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair3_4S 3 * homogeneousCompletion5GPoly 3) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_4S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_4S 3 := by
  have hL0 : homogeneousCompletion5Pair3_4L = homogeneousExponentSup (homogeneousCompletion5Leading 2) (homogeneousCompletion5Leading 3) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair3_4L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_4L (homogeneousCompletion5Leading 2) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_4L (homogeneousCompletion5Leading 3) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair3_4U =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_4_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair3_4V =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_4_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair3_4D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair3_4D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair3_4L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair3_4D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair3_4L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair3_4_degree_bounds_check k)
  unfold homogeneousCompletion5Pair3_4S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_4D k)) 2 3 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
