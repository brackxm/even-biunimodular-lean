/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs19Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs19OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair3_25S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 24
    (rationalSparsePolynomial homogeneousCompletion5Pair3_25U) (rationalSparsePolynomial homogeneousCompletion5Pair3_25V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_25D k))

theorem homogeneousCompletion5Pair3_25_relation : (∑ k, homogeneousCompletion5Pair3_25S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair3_25S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair3_25U homogeneousCompletion5Pair3_25V
    (homogeneousCompletion5G 2) (homogeneousCompletion5G 24) homogeneousCompletion5Pair3_25D homogeneousCompletion5G homogeneousCompletion5Pair3_25_sp_check

theorem homogeneousCompletion5Pair3_25_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair3_25S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair3_25S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair3_25U homogeneousCompletion5Pair3_25V
    (homogeneousCompletion5M (Fin.last 4) 2) (homogeneousCompletion5M (Fin.last 4) 24)
    homogeneousCompletion5Pair3_25D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair3_25W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair3_25_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair3_25D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair3_25_top :
    homogeneousCompletion5Pair3_25S 24 * homogeneousCompletion5GPoly 24 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair3_25S 24 * homogeneousCompletion5GPoly 24) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_25S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_25S 24 := by
  have hL0 : homogeneousCompletion5Pair3_25L = homogeneousExponentSup (homogeneousCompletion5Leading 2) (homogeneousCompletion5Leading 24) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair3_25L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_25L (homogeneousCompletion5Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_25L (homogeneousCompletion5Leading 24) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair3_25U =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_25_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair3_25V =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_25_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair3_25D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair3_25D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair3_25L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair3_25D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair3_25L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair3_25_degree_bounds_check k)
  unfold homogeneousCompletion5Pair3_25S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_25D k)) 2 24 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair3_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 25
    (rationalSparsePolynomial homogeneousCompletion5Pair3_26U) (rationalSparsePolynomial homogeneousCompletion5Pair3_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_26D k))

theorem homogeneousCompletion5Pair3_26_relation : (∑ k, homogeneousCompletion5Pair3_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair3_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair3_26U homogeneousCompletion5Pair3_26V
    (homogeneousCompletion5G 2) (homogeneousCompletion5G 25) homogeneousCompletion5Pair3_26D homogeneousCompletion5G homogeneousCompletion5Pair3_26_sp_check

theorem homogeneousCompletion5Pair3_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair3_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair3_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair3_26U homogeneousCompletion5Pair3_26V
    (homogeneousCompletion5M (Fin.last 4) 2) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair3_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair3_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair3_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair3_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair3_26_top :
    homogeneousCompletion5Pair3_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair3_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_26S 25 := by
  have hL0 : homogeneousCompletion5Pair3_26L = homogeneousExponentSup (homogeneousCompletion5Leading 2) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair3_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 5, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_26L (homogeneousCompletion5Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair3_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair3_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair3_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair3_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair3_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair3_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair3_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair3_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair3_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_26D k)) 2 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair3_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 26
    (rationalSparsePolynomial homogeneousCompletion5Pair3_27U) (rationalSparsePolynomial homogeneousCompletion5Pair3_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_27D k))

theorem homogeneousCompletion5Pair3_27_relation : (∑ k, homogeneousCompletion5Pair3_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair3_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair3_27U homogeneousCompletion5Pair3_27V
    (homogeneousCompletion5G 2) (homogeneousCompletion5G 26) homogeneousCompletion5Pair3_27D homogeneousCompletion5G homogeneousCompletion5Pair3_27_sp_check

theorem homogeneousCompletion5Pair3_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair3_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair3_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair3_27U homogeneousCompletion5Pair3_27V
    (homogeneousCompletion5M (Fin.last 4) 2) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair3_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair3_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair3_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair3_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair3_27_top :
    homogeneousCompletion5Pair3_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair3_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_27S 26 := by
  have hL0 : homogeneousCompletion5Pair3_27L = homogeneousExponentSup (homogeneousCompletion5Leading 2) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair3_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 6, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_27L (homogeneousCompletion5Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair3_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair3_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair3_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair3_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair3_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair3_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair3_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair3_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair3_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_27D k)) 2 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair4_5S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 4
    (rationalSparsePolynomial homogeneousCompletion5Pair4_5U) (rationalSparsePolynomial homogeneousCompletion5Pair4_5V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_5D k))

theorem homogeneousCompletion5Pair4_5_relation : (∑ k, homogeneousCompletion5Pair4_5S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair4_5S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair4_5U homogeneousCompletion5Pair4_5V
    (homogeneousCompletion5G 3) (homogeneousCompletion5G 4) homogeneousCompletion5Pair4_5D homogeneousCompletion5G homogeneousCompletion5Pair4_5_sp_check

theorem homogeneousCompletion5Pair4_5_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair4_5S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair4_5S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair4_5U homogeneousCompletion5Pair4_5V
    (homogeneousCompletion5M (Fin.last 4) 3) (homogeneousCompletion5M (Fin.last 4) 4)
    homogeneousCompletion5Pair4_5D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair4_5W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair4_5_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair4_5D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair4_5_top :
    homogeneousCompletion5Pair4_5S 4 * homogeneousCompletion5GPoly 4 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair4_5S 4 * homogeneousCompletion5GPoly 4) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_5S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_5S 4 := by
  have hL0 : homogeneousCompletion5Pair4_5L = homogeneousExponentSup (homogeneousCompletion5Leading 3) (homogeneousCompletion5Leading 4) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair4_5L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_5L (homogeneousCompletion5Leading 3) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_5L (homogeneousCompletion5Leading 4) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair4_5U =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_5_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair4_5V =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_5_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair4_5D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair4_5D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair4_5L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair4_5D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair4_5L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair4_5_degree_bounds_check k)
  unfold homogeneousCompletion5Pair4_5S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_5D k)) 3 4 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
