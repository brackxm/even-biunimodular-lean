/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs20Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs20OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair7_15S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 14
    (rationalSparsePolynomial homogeneousCompletion4Pair7_15U) (rationalSparsePolynomial homogeneousCompletion4Pair7_15V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair7_15D k))

theorem homogeneousCompletion4Pair7_15_relation : (∑ k, homogeneousCompletion4Pair7_15S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair7_15S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair7_15U homogeneousCompletion4Pair7_15V
    (homogeneousCompletion4G 6) (homogeneousCompletion4G 14) homogeneousCompletion4Pair7_15D homogeneousCompletion4G homogeneousCompletion4Pair7_15_sp_check

theorem homogeneousCompletion4Pair7_15_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair7_15S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair7_15S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair7_15U homogeneousCompletion4Pair7_15V
    (homogeneousCompletion4M (Fin.last 3) 6) (homogeneousCompletion4M (Fin.last 3) 14)
    homogeneousCompletion4Pair7_15D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair7_15W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair7_15_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair7_15D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair7_15_top :
    homogeneousCompletion4Pair7_15S 14 * homogeneousCompletion4GPoly 14 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair7_15S 14 * homogeneousCompletion4GPoly 14) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair7_15S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair7_15S 14 := by
  have hL0 : homogeneousCompletion4Pair7_15L = homogeneousExponentSup (homogeneousCompletion4Leading 6) (homogeneousCompletion4Leading 14) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair7_15L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 4, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair7_15L (homogeneousCompletion4Leading 6) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair7_15L (homogeneousCompletion4Leading 14) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair7_15U =
      monomial (homogeneousExponent homogeneousCompletion4Pair7_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair7_15_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair7_15V =
      monomial (homogeneousExponent homogeneousCompletion4Pair7_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair7_15_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair7_15D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair7_15D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair7_15L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair7_15D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair7_15L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair7_15_degree_bounds_check k)
  unfold homogeneousCompletion4Pair7_15S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair7_15D k)) 6 14 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair8_9S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 8
    (rationalSparsePolynomial homogeneousCompletion4Pair8_9U) (rationalSparsePolynomial homogeneousCompletion4Pair8_9V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair8_9D k))

theorem homogeneousCompletion4Pair8_9_relation : (∑ k, homogeneousCompletion4Pair8_9S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair8_9S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair8_9U homogeneousCompletion4Pair8_9V
    (homogeneousCompletion4G 7) (homogeneousCompletion4G 8) homogeneousCompletion4Pair8_9D homogeneousCompletion4G homogeneousCompletion4Pair8_9_sp_check

theorem homogeneousCompletion4Pair8_9_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair8_9S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair8_9S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair8_9U homogeneousCompletion4Pair8_9V
    (homogeneousCompletion4M (Fin.last 3) 7) (homogeneousCompletion4M (Fin.last 3) 8)
    homogeneousCompletion4Pair8_9D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair8_9W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair8_9_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair8_9D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair8_9_top :
    homogeneousCompletion4Pair8_9S 8 * homogeneousCompletion4GPoly 8 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair8_9S 8 * homogeneousCompletion4GPoly 8) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair8_9S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair8_9S 8 := by
  have hL0 : homogeneousCompletion4Pair8_9L = homogeneousExponentSup (homogeneousCompletion4Leading 7) (homogeneousCompletion4Leading 8) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair8_9L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair8_9L (homogeneousCompletion4Leading 7) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair8_9L (homogeneousCompletion4Leading 8) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair8_9U =
      monomial (homogeneousExponent homogeneousCompletion4Pair8_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair8_9_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair8_9V =
      monomial (homogeneousExponent homogeneousCompletion4Pair8_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair8_9_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair8_9D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair8_9D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair8_9L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair8_9D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair8_9L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair8_9_degree_bounds_check k)
  unfold homogeneousCompletion4Pair8_9S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair8_9D k)) 7 8 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair8_10S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 9
    (rationalSparsePolynomial homogeneousCompletion4Pair8_10U) (rationalSparsePolynomial homogeneousCompletion4Pair8_10V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair8_10D k))

theorem homogeneousCompletion4Pair8_10_relation : (∑ k, homogeneousCompletion4Pair8_10S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair8_10S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair8_10U homogeneousCompletion4Pair8_10V
    (homogeneousCompletion4G 7) (homogeneousCompletion4G 9) homogeneousCompletion4Pair8_10D homogeneousCompletion4G homogeneousCompletion4Pair8_10_sp_check

theorem homogeneousCompletion4Pair8_10_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair8_10S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair8_10S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair8_10U homogeneousCompletion4Pair8_10V
    (homogeneousCompletion4M (Fin.last 3) 7) (homogeneousCompletion4M (Fin.last 3) 9)
    homogeneousCompletion4Pair8_10D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair8_10W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair8_10_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair8_10D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair8_10_top :
    homogeneousCompletion4Pair8_10S 9 * homogeneousCompletion4GPoly 9 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair8_10S 9 * homogeneousCompletion4GPoly 9) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair8_10S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair8_10S 9 := by
  have hL0 : homogeneousCompletion4Pair8_10L = homogeneousExponentSup (homogeneousCompletion4Leading 7) (homogeneousCompletion4Leading 9) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair8_10L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair8_10L (homogeneousCompletion4Leading 7) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair8_10L (homogeneousCompletion4Leading 9) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair8_10U =
      monomial (homogeneousExponent homogeneousCompletion4Pair8_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair8_10_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair8_10V =
      monomial (homogeneousExponent homogeneousCompletion4Pair8_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair8_10_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair8_10D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair8_10D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair8_10L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair8_10D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair8_10L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair8_10_degree_bounds_check k)
  unfold homogeneousCompletion4Pair8_10S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair8_10D k)) 7 9 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair8_11S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 7 10
    (rationalSparsePolynomial homogeneousCompletion4Pair8_11U) (rationalSparsePolynomial homogeneousCompletion4Pair8_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair8_11D k))

theorem homogeneousCompletion4Pair8_11_relation : (∑ k, homogeneousCompletion4Pair8_11S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair8_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair8_11U homogeneousCompletion4Pair8_11V
    (homogeneousCompletion4G 7) (homogeneousCompletion4G 10) homogeneousCompletion4Pair8_11D homogeneousCompletion4G homogeneousCompletion4Pair8_11_sp_check

theorem homogeneousCompletion4Pair8_11_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair8_11S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair8_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair8_11U homogeneousCompletion4Pair8_11V
    (homogeneousCompletion4M (Fin.last 3) 7) (homogeneousCompletion4M (Fin.last 3) 10)
    homogeneousCompletion4Pair8_11D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair8_11W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair8_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair8_11D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair8_11_top :
    homogeneousCompletion4Pair8_11S 10 * homogeneousCompletion4GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair8_11S 10 * homogeneousCompletion4GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair8_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair8_11S 10 := by
  have hL0 : homogeneousCompletion4Pair8_11L = homogeneousExponentSup (homogeneousCompletion4Leading 7) (homogeneousCompletion4Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair8_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair8_11L (homogeneousCompletion4Leading 7) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair8_11L (homogeneousCompletion4Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair8_11U =
      monomial (homogeneousExponent homogeneousCompletion4Pair8_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair8_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair8_11V =
      monomial (homogeneousExponent homogeneousCompletion4Pair8_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair8_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair8_11D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair8_11D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair8_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair8_11D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair8_11L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair8_11_degree_bounds_check k)
  unfold homogeneousCompletion4Pair8_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair8_11D k)) 7 10 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
