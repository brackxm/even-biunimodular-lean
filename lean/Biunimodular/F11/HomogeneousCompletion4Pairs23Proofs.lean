/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs23Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs23OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair9_14S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 8 13
    (rationalSparsePolynomial homogeneousCompletion4Pair9_14U) (rationalSparsePolynomial homogeneousCompletion4Pair9_14V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair9_14D k))

theorem homogeneousCompletion4Pair9_14_relation : (∑ k, homogeneousCompletion4Pair9_14S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair9_14S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair9_14U homogeneousCompletion4Pair9_14V
    (homogeneousCompletion4G 8) (homogeneousCompletion4G 13) homogeneousCompletion4Pair9_14D homogeneousCompletion4G homogeneousCompletion4Pair9_14_sp_check

theorem homogeneousCompletion4Pair9_14_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair9_14S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair9_14S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair9_14U homogeneousCompletion4Pair9_14V
    (homogeneousCompletion4M (Fin.last 3) 8) (homogeneousCompletion4M (Fin.last 3) 13)
    homogeneousCompletion4Pair9_14D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair9_14W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair9_14_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair9_14D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair9_14_top :
    homogeneousCompletion4Pair9_14S 13 * homogeneousCompletion4GPoly 13 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair9_14S 13 * homogeneousCompletion4GPoly 13) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair9_14S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair9_14S 13 := by
  have hL0 : homogeneousCompletion4Pair9_14L = homogeneousExponentSup (homogeneousCompletion4Leading 8) (homogeneousCompletion4Leading 13) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair9_14L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 3, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair9_14L (homogeneousCompletion4Leading 8) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair9_14L (homogeneousCompletion4Leading 13) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair9_14U =
      monomial (homogeneousExponent homogeneousCompletion4Pair9_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair9_14_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair9_14V =
      monomial (homogeneousExponent homogeneousCompletion4Pair9_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair9_14_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair9_14D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair9_14D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair9_14L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair9_14D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair9_14L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair9_14_degree_bounds_check k)
  unfold homogeneousCompletion4Pair9_14S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair9_14D k)) 8 13 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair9_15S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 8 14
    (rationalSparsePolynomial homogeneousCompletion4Pair9_15U) (rationalSparsePolynomial homogeneousCompletion4Pair9_15V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair9_15D k))

theorem homogeneousCompletion4Pair9_15_relation : (∑ k, homogeneousCompletion4Pair9_15S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair9_15S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair9_15U homogeneousCompletion4Pair9_15V
    (homogeneousCompletion4G 8) (homogeneousCompletion4G 14) homogeneousCompletion4Pair9_15D homogeneousCompletion4G homogeneousCompletion4Pair9_15_sp_check

theorem homogeneousCompletion4Pair9_15_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair9_15S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair9_15S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair9_15U homogeneousCompletion4Pair9_15V
    (homogeneousCompletion4M (Fin.last 3) 8) (homogeneousCompletion4M (Fin.last 3) 14)
    homogeneousCompletion4Pair9_15D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair9_15W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair9_15_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair9_15D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair9_15_top :
    homogeneousCompletion4Pair9_15S 14 * homogeneousCompletion4GPoly 14 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair9_15S 14 * homogeneousCompletion4GPoly 14) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair9_15S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair9_15S 14 := by
  have hL0 : homogeneousCompletion4Pair9_15L = homogeneousExponentSup (homogeneousCompletion4Leading 8) (homogeneousCompletion4Leading 14) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair9_15L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 3, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair9_15L (homogeneousCompletion4Leading 8) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair9_15L (homogeneousCompletion4Leading 14) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair9_15U =
      monomial (homogeneousExponent homogeneousCompletion4Pair9_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair9_15_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair9_15V =
      monomial (homogeneousExponent homogeneousCompletion4Pair9_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair9_15_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair9_15D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair9_15D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair9_15L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair9_15D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair9_15L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair9_15_degree_bounds_check k)
  unfold homogeneousCompletion4Pair9_15S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair9_15D k)) 8 14 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair10_11S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 10
    (rationalSparsePolynomial homogeneousCompletion4Pair10_11U) (rationalSparsePolynomial homogeneousCompletion4Pair10_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair10_11D k))

theorem homogeneousCompletion4Pair10_11_relation : (∑ k, homogeneousCompletion4Pair10_11S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair10_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair10_11U homogeneousCompletion4Pair10_11V
    (homogeneousCompletion4G 9) (homogeneousCompletion4G 10) homogeneousCompletion4Pair10_11D homogeneousCompletion4G homogeneousCompletion4Pair10_11_sp_check

theorem homogeneousCompletion4Pair10_11_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair10_11S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair10_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair10_11U homogeneousCompletion4Pair10_11V
    (homogeneousCompletion4M (Fin.last 3) 9) (homogeneousCompletion4M (Fin.last 3) 10)
    homogeneousCompletion4Pair10_11D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair10_11W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair10_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair10_11D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair10_11_top :
    homogeneousCompletion4Pair10_11S 10 * homogeneousCompletion4GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair10_11S 10 * homogeneousCompletion4GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair10_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair10_11S 10 := by
  have hL0 : homogeneousCompletion4Pair10_11L = homogeneousExponentSup (homogeneousCompletion4Leading 9) (homogeneousCompletion4Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair10_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair10_11L (homogeneousCompletion4Leading 9) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair10_11L (homogeneousCompletion4Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair10_11U =
      monomial (homogeneousExponent homogeneousCompletion4Pair10_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair10_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair10_11V =
      monomial (homogeneousExponent homogeneousCompletion4Pair10_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair10_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair10_11D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair10_11D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair10_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair10_11D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair10_11L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair10_11_degree_bounds_check k)
  unfold homogeneousCompletion4Pair10_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair10_11D k)) 9 10 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair10_12S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 11
    (rationalSparsePolynomial homogeneousCompletion4Pair10_12U) (rationalSparsePolynomial homogeneousCompletion4Pair10_12V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair10_12D k))

theorem homogeneousCompletion4Pair10_12_relation : (∑ k, homogeneousCompletion4Pair10_12S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair10_12S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair10_12U homogeneousCompletion4Pair10_12V
    (homogeneousCompletion4G 9) (homogeneousCompletion4G 11) homogeneousCompletion4Pair10_12D homogeneousCompletion4G homogeneousCompletion4Pair10_12_sp_check

theorem homogeneousCompletion4Pair10_12_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair10_12S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair10_12S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair10_12U homogeneousCompletion4Pair10_12V
    (homogeneousCompletion4M (Fin.last 3) 9) (homogeneousCompletion4M (Fin.last 3) 11)
    homogeneousCompletion4Pair10_12D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair10_12W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair10_12_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair10_12D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair10_12_top :
    homogeneousCompletion4Pair10_12S 11 * homogeneousCompletion4GPoly 11 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair10_12S 11 * homogeneousCompletion4GPoly 11) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair10_12S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair10_12S 11 := by
  have hL0 : homogeneousCompletion4Pair10_12L = homogeneousExponentSup (homogeneousCompletion4Leading 9) (homogeneousCompletion4Leading 11) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair10_12L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 1, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair10_12L (homogeneousCompletion4Leading 9) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair10_12L (homogeneousCompletion4Leading 11) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair10_12U =
      monomial (homogeneousExponent homogeneousCompletion4Pair10_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair10_12_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair10_12V =
      monomial (homogeneousExponent homogeneousCompletion4Pair10_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair10_12_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair10_12D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair10_12D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair10_12L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair10_12D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair10_12L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair10_12_degree_bounds_check k)
  unfold homogeneousCompletion4Pair10_12S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair10_12D k)) 9 11 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
