/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs13Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs13OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair4_14S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 13
    (rationalSparsePolynomial homogeneousCompletion4Pair4_14U) (rationalSparsePolynomial homogeneousCompletion4Pair4_14V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair4_14D k))

theorem homogeneousCompletion4Pair4_14_relation : (∑ k, homogeneousCompletion4Pair4_14S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair4_14S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair4_14U homogeneousCompletion4Pair4_14V
    (homogeneousCompletion4G 3) (homogeneousCompletion4G 13) homogeneousCompletion4Pair4_14D homogeneousCompletion4G homogeneousCompletion4Pair4_14_sp_check

theorem homogeneousCompletion4Pair4_14_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair4_14S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair4_14S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair4_14U homogeneousCompletion4Pair4_14V
    (homogeneousCompletion4M (Fin.last 3) 3) (homogeneousCompletion4M (Fin.last 3) 13)
    homogeneousCompletion4Pair4_14D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair4_14W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair4_14_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair4_14D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair4_14_top :
    homogeneousCompletion4Pair4_14S 13 * homogeneousCompletion4GPoly 13 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair4_14S 13 * homogeneousCompletion4GPoly 13) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair4_14S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair4_14S 13 := by
  have hL0 : homogeneousCompletion4Pair4_14L = homogeneousExponentSup (homogeneousCompletion4Leading 3) (homogeneousCompletion4Leading 13) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair4_14L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 3, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair4_14L (homogeneousCompletion4Leading 3) := by native_decide
  have hV0 : (⟨1, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair4_14L (homogeneousCompletion4Leading 13) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair4_14U =
      monomial (homogeneousExponent homogeneousCompletion4Pair4_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair4_14_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair4_14V =
      monomial (homogeneousExponent homogeneousCompletion4Pair4_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair4_14_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair4_14D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair4_14D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair4_14L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair4_14D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair4_14L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair4_14_degree_bounds_check k)
  unfold homogeneousCompletion4Pair4_14S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair4_14D k)) 3 13 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair4_15S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 14
    (rationalSparsePolynomial homogeneousCompletion4Pair4_15U) (rationalSparsePolynomial homogeneousCompletion4Pair4_15V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair4_15D k))

theorem homogeneousCompletion4Pair4_15_relation : (∑ k, homogeneousCompletion4Pair4_15S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair4_15S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair4_15U homogeneousCompletion4Pair4_15V
    (homogeneousCompletion4G 3) (homogeneousCompletion4G 14) homogeneousCompletion4Pair4_15D homogeneousCompletion4G homogeneousCompletion4Pair4_15_sp_check

theorem homogeneousCompletion4Pair4_15_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair4_15S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair4_15S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair4_15U homogeneousCompletion4Pair4_15V
    (homogeneousCompletion4M (Fin.last 3) 3) (homogeneousCompletion4M (Fin.last 3) 14)
    homogeneousCompletion4Pair4_15D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair4_15W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair4_15_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair4_15D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair4_15_top :
    homogeneousCompletion4Pair4_15S 14 * homogeneousCompletion4GPoly 14 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair4_15S 14 * homogeneousCompletion4GPoly 14) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair4_15S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair4_15S 14 := by
  have hL0 : homogeneousCompletion4Pair4_15L = homogeneousExponentSup (homogeneousCompletion4Leading 3) (homogeneousCompletion4Leading 14) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair4_15L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 4, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair4_15L (homogeneousCompletion4Leading 3) := by native_decide
  have hV0 : (⟨1, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair4_15L (homogeneousCompletion4Leading 14) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair4_15U =
      monomial (homogeneousExponent homogeneousCompletion4Pair4_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair4_15_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair4_15V =
      monomial (homogeneousExponent homogeneousCompletion4Pair4_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair4_15_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair4_15D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair4_15D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair4_15L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair4_15D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair4_15L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair4_15_degree_bounds_check k)
  unfold homogeneousCompletion4Pair4_15S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair4_15D k)) 3 14 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair5_6S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 5
    (rationalSparsePolynomial homogeneousCompletion4Pair5_6U) (rationalSparsePolynomial homogeneousCompletion4Pair5_6V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair5_6D k))

theorem homogeneousCompletion4Pair5_6_relation : (∑ k, homogeneousCompletion4Pair5_6S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair5_6S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair5_6U homogeneousCompletion4Pair5_6V
    (homogeneousCompletion4G 4) (homogeneousCompletion4G 5) homogeneousCompletion4Pair5_6D homogeneousCompletion4G homogeneousCompletion4Pair5_6_sp_check

theorem homogeneousCompletion4Pair5_6_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair5_6S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair5_6S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair5_6U homogeneousCompletion4Pair5_6V
    (homogeneousCompletion4M (Fin.last 3) 4) (homogeneousCompletion4M (Fin.last 3) 5)
    homogeneousCompletion4Pair5_6D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair5_6W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair5_6_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair5_6D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair5_6_top :
    homogeneousCompletion4Pair5_6S 5 * homogeneousCompletion4GPoly 5 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair5_6S 5 * homogeneousCompletion4GPoly 5) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair5_6S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair5_6S 5 := by
  have hL0 : homogeneousCompletion4Pair5_6L = homogeneousExponentSup (homogeneousCompletion4Leading 4) (homogeneousCompletion4Leading 5) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair5_6L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair5_6L (homogeneousCompletion4Leading 4) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair5_6L (homogeneousCompletion4Leading 5) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair5_6U =
      monomial (homogeneousExponent homogeneousCompletion4Pair5_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair5_6_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair5_6V =
      monomial (homogeneousExponent homogeneousCompletion4Pair5_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair5_6_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair5_6D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair5_6D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair5_6L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair5_6D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair5_6L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair5_6_degree_bounds_check k)
  unfold homogeneousCompletion4Pair5_6S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair5_6D k)) 4 5 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair5_7S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 6
    (rationalSparsePolynomial homogeneousCompletion4Pair5_7U) (rationalSparsePolynomial homogeneousCompletion4Pair5_7V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair5_7D k))

theorem homogeneousCompletion4Pair5_7_relation : (∑ k, homogeneousCompletion4Pair5_7S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair5_7S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair5_7U homogeneousCompletion4Pair5_7V
    (homogeneousCompletion4G 4) (homogeneousCompletion4G 6) homogeneousCompletion4Pair5_7D homogeneousCompletion4G homogeneousCompletion4Pair5_7_sp_check

theorem homogeneousCompletion4Pair5_7_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair5_7S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair5_7S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair5_7U homogeneousCompletion4Pair5_7V
    (homogeneousCompletion4M (Fin.last 3) 4) (homogeneousCompletion4M (Fin.last 3) 6)
    homogeneousCompletion4Pair5_7D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair5_7W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair5_7_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair5_7D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair5_7_top :
    homogeneousCompletion4Pair5_7S 6 * homogeneousCompletion4GPoly 6 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair5_7S 6 * homogeneousCompletion4GPoly 6) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair5_7S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair5_7S 6 := by
  have hL0 : homogeneousCompletion4Pair5_7L = homogeneousExponentSup (homogeneousCompletion4Leading 4) (homogeneousCompletion4Leading 6) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair5_7L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair5_7L (homogeneousCompletion4Leading 4) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair5_7L (homogeneousCompletion4Leading 6) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair5_7U =
      monomial (homogeneousExponent homogeneousCompletion4Pair5_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair5_7_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair5_7V =
      monomial (homogeneousExponent homogeneousCompletion4Pair5_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair5_7_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair5_7D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair5_7D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair5_7L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair5_7D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair5_7L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair5_7_degree_bounds_check k)
  unfold homogeneousCompletion4Pair5_7S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair5_7D k)) 4 6 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
