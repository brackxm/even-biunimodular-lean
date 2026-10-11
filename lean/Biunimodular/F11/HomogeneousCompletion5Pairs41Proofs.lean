/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs41Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs41OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair7_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 26
    (rationalSparsePolynomial homogeneousCompletion5Pair7_27U) (rationalSparsePolynomial homogeneousCompletion5Pair7_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_27D k))

theorem homogeneousCompletion5Pair7_27_relation : (∑ k, homogeneousCompletion5Pair7_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_27U homogeneousCompletion5Pair7_27V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 26) homogeneousCompletion5Pair7_27D homogeneousCompletion5G homogeneousCompletion5Pair7_27_sp_check

theorem homogeneousCompletion5Pair7_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_27U homogeneousCompletion5Pair7_27V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair7_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_27_top :
    homogeneousCompletion5Pair7_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_27S 26 := by
  have hL0 : homogeneousCompletion5Pair7_27L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 5, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_27L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_27D k)) 6 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair8_9S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 8
    (rationalSparsePolynomial homogeneousCompletion5Pair8_9U) (rationalSparsePolynomial homogeneousCompletion5Pair8_9V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_9D k))

theorem homogeneousCompletion5Pair8_9_relation : (∑ k, homogeneousCompletion5Pair8_9S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair8_9S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair8_9U homogeneousCompletion5Pair8_9V
    (homogeneousCompletion5G 7) (homogeneousCompletion5G 8) homogeneousCompletion5Pair8_9D homogeneousCompletion5G homogeneousCompletion5Pair8_9_sp_check

theorem homogeneousCompletion5Pair8_9_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair8_9S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair8_9S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair8_9U homogeneousCompletion5Pair8_9V
    (homogeneousCompletion5M (Fin.last 4) 7) (homogeneousCompletion5M (Fin.last 4) 8)
    homogeneousCompletion5Pair8_9D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair8_9W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair8_9_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair8_9D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair8_9_top :
    homogeneousCompletion5Pair8_9S 8 * homogeneousCompletion5GPoly 8 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair8_9S 8 * homogeneousCompletion5GPoly 8) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_9S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_9S 8 := by
  have hL0 : homogeneousCompletion5Pair8_9L = homogeneousExponentSup (homogeneousCompletion5Leading 7) (homogeneousCompletion5Leading 8) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair8_9L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_9L (homogeneousCompletion5Leading 7) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_9L (homogeneousCompletion5Leading 8) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair8_9U =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_9_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair8_9V =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_9_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair8_9D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair8_9D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair8_9L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair8_9D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair8_9L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair8_9_degree_bounds_check k)
  unfold homogeneousCompletion5Pair8_9S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_9D k)) 7 8 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair8_10S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 9
    (rationalSparsePolynomial homogeneousCompletion5Pair8_10U) (rationalSparsePolynomial homogeneousCompletion5Pair8_10V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_10D k))

theorem homogeneousCompletion5Pair8_10_relation : (∑ k, homogeneousCompletion5Pair8_10S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair8_10S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair8_10U homogeneousCompletion5Pair8_10V
    (homogeneousCompletion5G 7) (homogeneousCompletion5G 9) homogeneousCompletion5Pair8_10D homogeneousCompletion5G homogeneousCompletion5Pair8_10_sp_check

theorem homogeneousCompletion5Pair8_10_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair8_10S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair8_10S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair8_10U homogeneousCompletion5Pair8_10V
    (homogeneousCompletion5M (Fin.last 4) 7) (homogeneousCompletion5M (Fin.last 4) 9)
    homogeneousCompletion5Pair8_10D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair8_10W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair8_10_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair8_10D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair8_10_top :
    homogeneousCompletion5Pair8_10S 9 * homogeneousCompletion5GPoly 9 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair8_10S 9 * homogeneousCompletion5GPoly 9) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_10S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_10S 9 := by
  have hL0 : homogeneousCompletion5Pair8_10L = homogeneousExponentSup (homogeneousCompletion5Leading 7) (homogeneousCompletion5Leading 9) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair8_10L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_10L (homogeneousCompletion5Leading 7) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_10L (homogeneousCompletion5Leading 9) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair8_10U =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_10_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair8_10V =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_10_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair8_10D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair8_10D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair8_10L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair8_10D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair8_10L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair8_10_degree_bounds_check k)
  unfold homogeneousCompletion5Pair8_10S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_10D k)) 7 9 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair8_11S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 10
    (rationalSparsePolynomial homogeneousCompletion5Pair8_11U) (rationalSparsePolynomial homogeneousCompletion5Pair8_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_11D k))

theorem homogeneousCompletion5Pair8_11_relation : (∑ k, homogeneousCompletion5Pair8_11S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair8_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair8_11U homogeneousCompletion5Pair8_11V
    (homogeneousCompletion5G 7) (homogeneousCompletion5G 10) homogeneousCompletion5Pair8_11D homogeneousCompletion5G homogeneousCompletion5Pair8_11_sp_check

theorem homogeneousCompletion5Pair8_11_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair8_11S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair8_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair8_11U homogeneousCompletion5Pair8_11V
    (homogeneousCompletion5M (Fin.last 4) 7) (homogeneousCompletion5M (Fin.last 4) 10)
    homogeneousCompletion5Pair8_11D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair8_11W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair8_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair8_11D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair8_11_top :
    homogeneousCompletion5Pair8_11S 10 * homogeneousCompletion5GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair8_11S 10 * homogeneousCompletion5GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair8_11S 10 := by
  have hL0 : homogeneousCompletion5Pair8_11L = homogeneousExponentSup (homogeneousCompletion5Leading 7) (homogeneousCompletion5Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair8_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_11L (homogeneousCompletion5Leading 7) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair8_11L (homogeneousCompletion5Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair8_11U =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair8_11V =
      monomial (homogeneousExponent homogeneousCompletion5Pair8_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair8_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair8_11D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair8_11D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair8_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair8_11D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair8_11L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair8_11_degree_bounds_check k)
  unfold homogeneousCompletion5Pair8_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair8_11D k)) 7 10 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
