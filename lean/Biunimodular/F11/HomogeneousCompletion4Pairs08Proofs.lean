/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs08Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs08OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair3_5S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 4
    (rationalSparsePolynomial homogeneousCompletion4Pair3_5U) (rationalSparsePolynomial homogeneousCompletion4Pair3_5V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair3_5D k))

theorem homogeneousCompletion4Pair3_5_relation : (∑ k, homogeneousCompletion4Pair3_5S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair3_5S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair3_5U homogeneousCompletion4Pair3_5V
    (homogeneousCompletion4G 2) (homogeneousCompletion4G 4) homogeneousCompletion4Pair3_5D homogeneousCompletion4G homogeneousCompletion4Pair3_5_sp_check

theorem homogeneousCompletion4Pair3_5_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair3_5S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair3_5S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair3_5U homogeneousCompletion4Pair3_5V
    (homogeneousCompletion4M (Fin.last 3) 2) (homogeneousCompletion4M (Fin.last 3) 4)
    homogeneousCompletion4Pair3_5D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair3_5W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair3_5_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair3_5D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair3_5_top :
    homogeneousCompletion4Pair3_5S 4 * homogeneousCompletion4GPoly 4 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair3_5S 4 * homogeneousCompletion4GPoly 4) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair3_5S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair3_5S 4 := by
  have hL0 : homogeneousCompletion4Pair3_5L = homogeneousExponentSup (homogeneousCompletion4Leading 2) (homogeneousCompletion4Leading 4) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair3_5L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair3_5L (homogeneousCompletion4Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair3_5L (homogeneousCompletion4Leading 4) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair3_5U =
      monomial (homogeneousExponent homogeneousCompletion4Pair3_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair3_5_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair3_5V =
      monomial (homogeneousExponent homogeneousCompletion4Pair3_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair3_5_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair3_5D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair3_5D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair3_5L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair3_5D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair3_5L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair3_5_degree_bounds_check k)
  unfold homogeneousCompletion4Pair3_5S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair3_5D k)) 2 4 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair3_6S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 5
    (rationalSparsePolynomial homogeneousCompletion4Pair3_6U) (rationalSparsePolynomial homogeneousCompletion4Pair3_6V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair3_6D k))

theorem homogeneousCompletion4Pair3_6_relation : (∑ k, homogeneousCompletion4Pair3_6S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair3_6S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair3_6U homogeneousCompletion4Pair3_6V
    (homogeneousCompletion4G 2) (homogeneousCompletion4G 5) homogeneousCompletion4Pair3_6D homogeneousCompletion4G homogeneousCompletion4Pair3_6_sp_check

theorem homogeneousCompletion4Pair3_6_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair3_6S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair3_6S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair3_6U homogeneousCompletion4Pair3_6V
    (homogeneousCompletion4M (Fin.last 3) 2) (homogeneousCompletion4M (Fin.last 3) 5)
    homogeneousCompletion4Pair3_6D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair3_6W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair3_6_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair3_6D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair3_6_top :
    homogeneousCompletion4Pair3_6S 5 * homogeneousCompletion4GPoly 5 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair3_6S 5 * homogeneousCompletion4GPoly 5) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair3_6S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair3_6S 5 := by
  have hL0 : homogeneousCompletion4Pair3_6L = homogeneousExponentSup (homogeneousCompletion4Leading 2) (homogeneousCompletion4Leading 5) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair3_6L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair3_6L (homogeneousCompletion4Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair3_6L (homogeneousCompletion4Leading 5) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair3_6U =
      monomial (homogeneousExponent homogeneousCompletion4Pair3_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair3_6_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair3_6V =
      monomial (homogeneousExponent homogeneousCompletion4Pair3_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair3_6_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair3_6D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair3_6D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair3_6L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair3_6D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair3_6L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair3_6_degree_bounds_check k)
  unfold homogeneousCompletion4Pair3_6S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair3_6D k)) 2 5 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair3_7S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 6
    (rationalSparsePolynomial homogeneousCompletion4Pair3_7U) (rationalSparsePolynomial homogeneousCompletion4Pair3_7V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair3_7D k))

theorem homogeneousCompletion4Pair3_7_relation : (∑ k, homogeneousCompletion4Pair3_7S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair3_7S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair3_7U homogeneousCompletion4Pair3_7V
    (homogeneousCompletion4G 2) (homogeneousCompletion4G 6) homogeneousCompletion4Pair3_7D homogeneousCompletion4G homogeneousCompletion4Pair3_7_sp_check

theorem homogeneousCompletion4Pair3_7_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair3_7S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair3_7S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair3_7U homogeneousCompletion4Pair3_7V
    (homogeneousCompletion4M (Fin.last 3) 2) (homogeneousCompletion4M (Fin.last 3) 6)
    homogeneousCompletion4Pair3_7D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair3_7W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair3_7_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair3_7D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair3_7_top :
    homogeneousCompletion4Pair3_7S 6 * homogeneousCompletion4GPoly 6 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair3_7S 6 * homogeneousCompletion4GPoly 6) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair3_7S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair3_7S 6 := by
  have hL0 : homogeneousCompletion4Pair3_7L = homogeneousExponentSup (homogeneousCompletion4Leading 2) (homogeneousCompletion4Leading 6) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair3_7L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 2, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair3_7L (homogeneousCompletion4Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair3_7L (homogeneousCompletion4Leading 6) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair3_7U =
      monomial (homogeneousExponent homogeneousCompletion4Pair3_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair3_7_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair3_7V =
      monomial (homogeneousExponent homogeneousCompletion4Pair3_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair3_7_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair3_7D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair3_7D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair3_7L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair3_7D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair3_7L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair3_7_degree_bounds_check k)
  unfold homogeneousCompletion4Pair3_7S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair3_7D k)) 2 6 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair3_8S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 7
    (rationalSparsePolynomial homogeneousCompletion4Pair3_8U) (rationalSparsePolynomial homogeneousCompletion4Pair3_8V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair3_8D k))

theorem homogeneousCompletion4Pair3_8_relation : (∑ k, homogeneousCompletion4Pair3_8S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair3_8S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair3_8U homogeneousCompletion4Pair3_8V
    (homogeneousCompletion4G 2) (homogeneousCompletion4G 7) homogeneousCompletion4Pair3_8D homogeneousCompletion4G homogeneousCompletion4Pair3_8_sp_check

theorem homogeneousCompletion4Pair3_8_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair3_8S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair3_8S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair3_8U homogeneousCompletion4Pair3_8V
    (homogeneousCompletion4M (Fin.last 3) 2) (homogeneousCompletion4M (Fin.last 3) 7)
    homogeneousCompletion4Pair3_8D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair3_8W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair3_8_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair3_8D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair3_8_top :
    homogeneousCompletion4Pair3_8S 7 * homogeneousCompletion4GPoly 7 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair3_8S 7 * homogeneousCompletion4GPoly 7) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair3_8S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair3_8S 7 := by
  have hL0 : homogeneousCompletion4Pair3_8L = homogeneousExponentSup (homogeneousCompletion4Leading 2) (homogeneousCompletion4Leading 7) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair3_8L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair3_8L (homogeneousCompletion4Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair3_8L (homogeneousCompletion4Leading 7) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair3_8U =
      monomial (homogeneousExponent homogeneousCompletion4Pair3_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair3_8_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair3_8V =
      monomial (homogeneousExponent homogeneousCompletion4Pair3_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair3_8_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair3_8D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair3_8D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair3_8L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair3_8D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair3_8L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair3_8_degree_bounds_check k)
  unfold homogeneousCompletion4Pair3_8S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair3_8D k)) 2 7 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
