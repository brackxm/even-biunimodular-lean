/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs36Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs36OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair6_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 26
    (rationalSparsePolynomial homogeneousCompletion5Pair6_27U) (rationalSparsePolynomial homogeneousCompletion5Pair6_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_27D k))

theorem homogeneousCompletion5Pair6_27_relation : (∑ k, homogeneousCompletion5Pair6_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_27U homogeneousCompletion5Pair6_27V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 26) homogeneousCompletion5Pair6_27D homogeneousCompletion5G homogeneousCompletion5Pair6_27_sp_check

theorem homogeneousCompletion5Pair6_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_27U homogeneousCompletion5Pair6_27V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair6_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_27_top :
    homogeneousCompletion5Pair6_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_27S 26 := by
  have hL0 : homogeneousCompletion5Pair6_27L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 5, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_27L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_27D k)) 5 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_8S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 7
    (rationalSparsePolynomial homogeneousCompletion5Pair7_8U) (rationalSparsePolynomial homogeneousCompletion5Pair7_8V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_8D k))

theorem homogeneousCompletion5Pair7_8_relation : (∑ k, homogeneousCompletion5Pair7_8S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_8S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_8U homogeneousCompletion5Pair7_8V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 7) homogeneousCompletion5Pair7_8D homogeneousCompletion5G homogeneousCompletion5Pair7_8_sp_check

theorem homogeneousCompletion5Pair7_8_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_8S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_8S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_8U homogeneousCompletion5Pair7_8V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 7)
    homogeneousCompletion5Pair7_8D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_8W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_8_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_8D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_8_top :
    homogeneousCompletion5Pair7_8S 7 * homogeneousCompletion5GPoly 7 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_8S 7 * homogeneousCompletion5GPoly 7) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_8S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_8S 7 := by
  have hL0 : homogeneousCompletion5Pair7_8L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 7) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_8L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_8L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_8L (homogeneousCompletion5Leading 7) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_8U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_8_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_8V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_8_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_8D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_8D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_8L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_8D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_8L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_8_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_8S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_8D k)) 6 7 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_9S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 8
    (rationalSparsePolynomial homogeneousCompletion5Pair7_9U) (rationalSparsePolynomial homogeneousCompletion5Pair7_9V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_9D k))

theorem homogeneousCompletion5Pair7_9_relation : (∑ k, homogeneousCompletion5Pair7_9S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_9S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_9U homogeneousCompletion5Pair7_9V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 8) homogeneousCompletion5Pair7_9D homogeneousCompletion5G homogeneousCompletion5Pair7_9_sp_check

theorem homogeneousCompletion5Pair7_9_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_9S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_9S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_9U homogeneousCompletion5Pair7_9V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 8)
    homogeneousCompletion5Pair7_9D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_9W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_9_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_9D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_9_top :
    homogeneousCompletion5Pair7_9S 8 * homogeneousCompletion5GPoly 8 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_9S 8 * homogeneousCompletion5GPoly 8) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_9S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_9S 8 := by
  have hL0 : homogeneousCompletion5Pair7_9L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 8) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_9L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_9L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_9L (homogeneousCompletion5Leading 8) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_9U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_9_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_9V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_9_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_9D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_9D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_9L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_9D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_9L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_9_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_9S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_9D k)) 6 8 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_10S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 9
    (rationalSparsePolynomial homogeneousCompletion5Pair7_10U) (rationalSparsePolynomial homogeneousCompletion5Pair7_10V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_10D k))

theorem homogeneousCompletion5Pair7_10_relation : (∑ k, homogeneousCompletion5Pair7_10S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_10S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_10U homogeneousCompletion5Pair7_10V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 9) homogeneousCompletion5Pair7_10D homogeneousCompletion5G homogeneousCompletion5Pair7_10_sp_check

theorem homogeneousCompletion5Pair7_10_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_10S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_10S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_10U homogeneousCompletion5Pair7_10V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 9)
    homogeneousCompletion5Pair7_10D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_10W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_10_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_10D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_10_top :
    homogeneousCompletion5Pair7_10S 9 * homogeneousCompletion5GPoly 9 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_10S 9 * homogeneousCompletion5GPoly 9) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_10S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_10S 9 := by
  have hL0 : homogeneousCompletion5Pair7_10L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 9) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_10L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_10L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_10L (homogeneousCompletion5Leading 9) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_10U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_10_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_10V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_10_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_10D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_10D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_10L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_10D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_10L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_10_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_10S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_10D k)) 6 9 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
