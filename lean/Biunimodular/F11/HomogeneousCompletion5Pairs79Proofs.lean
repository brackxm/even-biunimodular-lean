/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs79Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs79OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair18_25S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 17 24
    (rationalSparsePolynomial homogeneousCompletion5Pair18_25U) (rationalSparsePolynomial homogeneousCompletion5Pair18_25V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair18_25D k))

theorem homogeneousCompletion5Pair18_25_relation : (∑ k, homogeneousCompletion5Pair18_25S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair18_25S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair18_25U homogeneousCompletion5Pair18_25V
    (homogeneousCompletion5G 17) (homogeneousCompletion5G 24) homogeneousCompletion5Pair18_25D homogeneousCompletion5G homogeneousCompletion5Pair18_25_sp_check

theorem homogeneousCompletion5Pair18_25_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair18_25S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair18_25S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair18_25U homogeneousCompletion5Pair18_25V
    (homogeneousCompletion5M (Fin.last 4) 17) (homogeneousCompletion5M (Fin.last 4) 24)
    homogeneousCompletion5Pair18_25D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair18_25W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair18_25_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair18_25D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair18_25_top :
    homogeneousCompletion5Pair18_25S 24 * homogeneousCompletion5GPoly 24 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair18_25S 24 * homogeneousCompletion5GPoly 24) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair18_25S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair18_25S 24 := by
  have hL0 : homogeneousCompletion5Pair18_25L = homogeneousExponentSup (homogeneousCompletion5Leading 17) (homogeneousCompletion5Leading 24) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair18_25L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 3, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair18_25L (homogeneousCompletion5Leading 17) := by native_decide
  have hV0 : (⟨0, 0, 0, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair18_25L (homogeneousCompletion5Leading 24) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair18_25U =
      monomial (homogeneousExponent homogeneousCompletion5Pair18_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair18_25_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair18_25V =
      monomial (homogeneousExponent homogeneousCompletion5Pair18_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair18_25_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair18_25D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair18_25D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair18_25L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair18_25D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair18_25L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair18_25_degree_bounds_check k)
  unfold homogeneousCompletion5Pair18_25S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair18_25D k)) 17 24 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair18_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 17 25
    (rationalSparsePolynomial homogeneousCompletion5Pair18_26U) (rationalSparsePolynomial homogeneousCompletion5Pair18_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair18_26D k))

theorem homogeneousCompletion5Pair18_26_relation : (∑ k, homogeneousCompletion5Pair18_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair18_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair18_26U homogeneousCompletion5Pair18_26V
    (homogeneousCompletion5G 17) (homogeneousCompletion5G 25) homogeneousCompletion5Pair18_26D homogeneousCompletion5G homogeneousCompletion5Pair18_26_sp_check

theorem homogeneousCompletion5Pair18_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair18_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair18_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair18_26U homogeneousCompletion5Pair18_26V
    (homogeneousCompletion5M (Fin.last 4) 17) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair18_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair18_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair18_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair18_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair18_26_top :
    homogeneousCompletion5Pair18_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair18_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair18_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair18_26S 25 := by
  have hL0 : homogeneousCompletion5Pair18_26L = homogeneousExponentSup (homogeneousCompletion5Leading 17) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair18_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair18_26L (homogeneousCompletion5Leading 17) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair18_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair18_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair18_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair18_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair18_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair18_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair18_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair18_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair18_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair18_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair18_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair18_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair18_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair18_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair18_26D k)) 17 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair18_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 17 26
    (rationalSparsePolynomial homogeneousCompletion5Pair18_27U) (rationalSparsePolynomial homogeneousCompletion5Pair18_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair18_27D k))

theorem homogeneousCompletion5Pair18_27_relation : (∑ k, homogeneousCompletion5Pair18_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair18_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair18_27U homogeneousCompletion5Pair18_27V
    (homogeneousCompletion5G 17) (homogeneousCompletion5G 26) homogeneousCompletion5Pair18_27D homogeneousCompletion5G homogeneousCompletion5Pair18_27_sp_check

theorem homogeneousCompletion5Pair18_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair18_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair18_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair18_27U homogeneousCompletion5Pair18_27V
    (homogeneousCompletion5M (Fin.last 4) 17) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair18_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair18_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair18_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair18_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair18_27_top :
    homogeneousCompletion5Pair18_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair18_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair18_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair18_27S 26 := by
  have hL0 : homogeneousCompletion5Pair18_27L = homogeneousExponentSup (homogeneousCompletion5Leading 17) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair18_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 5, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair18_27L (homogeneousCompletion5Leading 17) := by native_decide
  have hV0 : (⟨0, 0, 0, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair18_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair18_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair18_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair18_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair18_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair18_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair18_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair18_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair18_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair18_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair18_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair18_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair18_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair18_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair18_27D k)) 17 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair19_20S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 18 19
    (rationalSparsePolynomial homogeneousCompletion5Pair19_20U) (rationalSparsePolynomial homogeneousCompletion5Pair19_20V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair19_20D k))

theorem homogeneousCompletion5Pair19_20_relation : (∑ k, homogeneousCompletion5Pair19_20S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair19_20S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair19_20U homogeneousCompletion5Pair19_20V
    (homogeneousCompletion5G 18) (homogeneousCompletion5G 19) homogeneousCompletion5Pair19_20D homogeneousCompletion5G homogeneousCompletion5Pair19_20_sp_check

theorem homogeneousCompletion5Pair19_20_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair19_20S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair19_20S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair19_20U homogeneousCompletion5Pair19_20V
    (homogeneousCompletion5M (Fin.last 4) 18) (homogeneousCompletion5M (Fin.last 4) 19)
    homogeneousCompletion5Pair19_20D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair19_20W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair19_20_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair19_20D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair19_20_top :
    homogeneousCompletion5Pair19_20S 19 * homogeneousCompletion5GPoly 19 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair19_20S 19 * homogeneousCompletion5GPoly 19) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair19_20S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair19_20S 19 := by
  have hL0 : homogeneousCompletion5Pair19_20L = homogeneousExponentSup (homogeneousCompletion5Leading 18) (homogeneousCompletion5Leading 19) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair19_20L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair19_20L (homogeneousCompletion5Leading 18) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair19_20L (homogeneousCompletion5Leading 19) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair19_20U =
      monomial (homogeneousExponent homogeneousCompletion5Pair19_20L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair19_20_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair19_20V =
      monomial (homogeneousExponent homogeneousCompletion5Pair19_20L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair19_20_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair19_20D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair19_20D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair19_20L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair19_20D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair19_20L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair19_20_degree_bounds_check k)
  unfold homogeneousCompletion5Pair19_20S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair19_20D k)) 18 19 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
