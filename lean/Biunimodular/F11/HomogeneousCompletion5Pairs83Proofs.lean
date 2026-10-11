/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs83Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs83OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair20_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 19 25
    (rationalSparsePolynomial homogeneousCompletion5Pair20_26U) (rationalSparsePolynomial homogeneousCompletion5Pair20_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair20_26D k))

theorem homogeneousCompletion5Pair20_26_relation : (∑ k, homogeneousCompletion5Pair20_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair20_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair20_26U homogeneousCompletion5Pair20_26V
    (homogeneousCompletion5G 19) (homogeneousCompletion5G 25) homogeneousCompletion5Pair20_26D homogeneousCompletion5G homogeneousCompletion5Pair20_26_sp_check

theorem homogeneousCompletion5Pair20_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair20_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair20_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair20_26U homogeneousCompletion5Pair20_26V
    (homogeneousCompletion5M (Fin.last 4) 19) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair20_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair20_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair20_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair20_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair20_26_top :
    homogeneousCompletion5Pair20_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair20_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair20_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair20_26S 25 := by
  have hL0 : homogeneousCompletion5Pair20_26L = homogeneousExponentSup (homogeneousCompletion5Leading 19) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair20_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair20_26L (homogeneousCompletion5Leading 19) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair20_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair20_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair20_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair20_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair20_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair20_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair20_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair20_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair20_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair20_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair20_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair20_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair20_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair20_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair20_26D k)) 19 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair20_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 19 26
    (rationalSparsePolynomial homogeneousCompletion5Pair20_27U) (rationalSparsePolynomial homogeneousCompletion5Pair20_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair20_27D k))

theorem homogeneousCompletion5Pair20_27_relation : (∑ k, homogeneousCompletion5Pair20_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair20_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair20_27U homogeneousCompletion5Pair20_27V
    (homogeneousCompletion5G 19) (homogeneousCompletion5G 26) homogeneousCompletion5Pair20_27D homogeneousCompletion5G homogeneousCompletion5Pair20_27_sp_check

theorem homogeneousCompletion5Pair20_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair20_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair20_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair20_27U homogeneousCompletion5Pair20_27V
    (homogeneousCompletion5M (Fin.last 4) 19) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair20_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair20_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair20_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair20_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair20_27_top :
    homogeneousCompletion5Pair20_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair20_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair20_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair20_27S 26 := by
  have hL0 : homogeneousCompletion5Pair20_27L = homogeneousExponentSup (homogeneousCompletion5Leading 19) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair20_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 6, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair20_27L (homogeneousCompletion5Leading 19) := by native_decide
  have hV0 : (⟨0, 0, 1, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair20_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair20_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair20_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair20_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair20_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair20_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair20_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair20_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair20_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair20_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair20_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair20_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair20_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair20_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair20_27D k)) 19 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair21_22S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 20 21
    (rationalSparsePolynomial homogeneousCompletion5Pair21_22U) (rationalSparsePolynomial homogeneousCompletion5Pair21_22V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair21_22D k))

theorem homogeneousCompletion5Pair21_22_relation : (∑ k, homogeneousCompletion5Pair21_22S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair21_22S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair21_22U homogeneousCompletion5Pair21_22V
    (homogeneousCompletion5G 20) (homogeneousCompletion5G 21) homogeneousCompletion5Pair21_22D homogeneousCompletion5G homogeneousCompletion5Pair21_22_sp_check

theorem homogeneousCompletion5Pair21_22_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair21_22S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair21_22S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair21_22U homogeneousCompletion5Pair21_22V
    (homogeneousCompletion5M (Fin.last 4) 20) (homogeneousCompletion5M (Fin.last 4) 21)
    homogeneousCompletion5Pair21_22D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair21_22W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair21_22_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair21_22D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair21_22_top :
    homogeneousCompletion5Pair21_22S 21 * homogeneousCompletion5GPoly 21 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair21_22S 21 * homogeneousCompletion5GPoly 21) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair21_22S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair21_22S 21 := by
  have hL0 : homogeneousCompletion5Pair21_22L = homogeneousExponentSup (homogeneousCompletion5Leading 20) (homogeneousCompletion5Leading 21) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair21_22L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 4, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair21_22L (homogeneousCompletion5Leading 20) := by native_decide
  have hV0 : (⟨0, 1, 0, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair21_22L (homogeneousCompletion5Leading 21) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair21_22U =
      monomial (homogeneousExponent homogeneousCompletion5Pair21_22L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair21_22_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair21_22V =
      monomial (homogeneousExponent homogeneousCompletion5Pair21_22L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair21_22_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair21_22D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair21_22D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair21_22L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair21_22D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair21_22L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair21_22_degree_bounds_check k)
  unfold homogeneousCompletion5Pair21_22S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair21_22D k)) 20 21 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair21_23S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 20 22
    (rationalSparsePolynomial homogeneousCompletion5Pair21_23U) (rationalSparsePolynomial homogeneousCompletion5Pair21_23V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair21_23D k))

theorem homogeneousCompletion5Pair21_23_relation : (∑ k, homogeneousCompletion5Pair21_23S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair21_23S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair21_23U homogeneousCompletion5Pair21_23V
    (homogeneousCompletion5G 20) (homogeneousCompletion5G 22) homogeneousCompletion5Pair21_23D homogeneousCompletion5G homogeneousCompletion5Pair21_23_sp_check

theorem homogeneousCompletion5Pair21_23_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair21_23S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair21_23S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair21_23U homogeneousCompletion5Pair21_23V
    (homogeneousCompletion5M (Fin.last 4) 20) (homogeneousCompletion5M (Fin.last 4) 22)
    homogeneousCompletion5Pair21_23D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair21_23W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair21_23_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair21_23D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair21_23_top :
    homogeneousCompletion5Pair21_23S 22 * homogeneousCompletion5GPoly 22 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair21_23S 22 * homogeneousCompletion5GPoly 22) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair21_23S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair21_23S 22 := by
  have hL0 : homogeneousCompletion5Pair21_23L = homogeneousExponentSup (homogeneousCompletion5Leading 20) (homogeneousCompletion5Leading 22) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair21_23L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair21_23L (homogeneousCompletion5Leading 20) := by native_decide
  have hV0 : (⟨0, 1, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair21_23L (homogeneousCompletion5Leading 22) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair21_23U =
      monomial (homogeneousExponent homogeneousCompletion5Pair21_23L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair21_23_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair21_23V =
      monomial (homogeneousExponent homogeneousCompletion5Pair21_23L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair21_23_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair21_23D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair21_23D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair21_23L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair21_23D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair21_23L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair21_23_degree_bounds_check k)
  unfold homogeneousCompletion5Pair21_23S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair21_23D k)) 20 22 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
