/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs16Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs16OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair6_7S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 6
    (rationalSparsePolynomial homogeneousCompletion4Pair6_7U) (rationalSparsePolynomial homogeneousCompletion4Pair6_7V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_7D k))

theorem homogeneousCompletion4Pair6_7_relation : (∑ k, homogeneousCompletion4Pair6_7S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair6_7S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair6_7U homogeneousCompletion4Pair6_7V
    (homogeneousCompletion4G 5) (homogeneousCompletion4G 6) homogeneousCompletion4Pair6_7D homogeneousCompletion4G homogeneousCompletion4Pair6_7_sp_check

theorem homogeneousCompletion4Pair6_7_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair6_7S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair6_7S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair6_7U homogeneousCompletion4Pair6_7V
    (homogeneousCompletion4M (Fin.last 3) 5) (homogeneousCompletion4M (Fin.last 3) 6)
    homogeneousCompletion4Pair6_7D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair6_7W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair6_7_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair6_7D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair6_7_top :
    homogeneousCompletion4Pair6_7S 6 * homogeneousCompletion4GPoly 6 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair6_7S 6 * homogeneousCompletion4GPoly 6) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_7S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_7S 6 := by
  have hL0 : homogeneousCompletion4Pair6_7L = homogeneousExponentSup (homogeneousCompletion4Leading 5) (homogeneousCompletion4Leading 6) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair6_7L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_7L (homogeneousCompletion4Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_7L (homogeneousCompletion4Leading 6) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair6_7U =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_7_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair6_7V =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_7_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair6_7D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair6_7D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair6_7L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair6_7D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair6_7L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair6_7_degree_bounds_check k)
  unfold homogeneousCompletion4Pair6_7S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_7D k)) 5 6 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair6_8S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 7
    (rationalSparsePolynomial homogeneousCompletion4Pair6_8U) (rationalSparsePolynomial homogeneousCompletion4Pair6_8V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_8D k))

theorem homogeneousCompletion4Pair6_8_relation : (∑ k, homogeneousCompletion4Pair6_8S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair6_8S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair6_8U homogeneousCompletion4Pair6_8V
    (homogeneousCompletion4G 5) (homogeneousCompletion4G 7) homogeneousCompletion4Pair6_8D homogeneousCompletion4G homogeneousCompletion4Pair6_8_sp_check

theorem homogeneousCompletion4Pair6_8_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair6_8S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair6_8S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair6_8U homogeneousCompletion4Pair6_8V
    (homogeneousCompletion4M (Fin.last 3) 5) (homogeneousCompletion4M (Fin.last 3) 7)
    homogeneousCompletion4Pair6_8D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair6_8W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair6_8_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair6_8D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair6_8_top :
    homogeneousCompletion4Pair6_8S 7 * homogeneousCompletion4GPoly 7 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair6_8S 7 * homogeneousCompletion4GPoly 7) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_8S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_8S 7 := by
  have hL0 : homogeneousCompletion4Pair6_8L = homogeneousExponentSup (homogeneousCompletion4Leading 5) (homogeneousCompletion4Leading 7) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair6_8L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_8L (homogeneousCompletion4Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_8L (homogeneousCompletion4Leading 7) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair6_8U =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_8_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair6_8V =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_8_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair6_8D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair6_8D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair6_8L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair6_8D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair6_8L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair6_8_degree_bounds_check k)
  unfold homogeneousCompletion4Pair6_8S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_8D k)) 5 7 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair6_9S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 8
    (rationalSparsePolynomial homogeneousCompletion4Pair6_9U) (rationalSparsePolynomial homogeneousCompletion4Pair6_9V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_9D k))

theorem homogeneousCompletion4Pair6_9_relation : (∑ k, homogeneousCompletion4Pair6_9S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair6_9S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair6_9U homogeneousCompletion4Pair6_9V
    (homogeneousCompletion4G 5) (homogeneousCompletion4G 8) homogeneousCompletion4Pair6_9D homogeneousCompletion4G homogeneousCompletion4Pair6_9_sp_check

theorem homogeneousCompletion4Pair6_9_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair6_9S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair6_9S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair6_9U homogeneousCompletion4Pair6_9V
    (homogeneousCompletion4M (Fin.last 3) 5) (homogeneousCompletion4M (Fin.last 3) 8)
    homogeneousCompletion4Pair6_9D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair6_9W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair6_9_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair6_9D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair6_9_top :
    homogeneousCompletion4Pair6_9S 8 * homogeneousCompletion4GPoly 8 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair6_9S 8 * homogeneousCompletion4GPoly 8) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_9S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_9S 8 := by
  have hL0 : homogeneousCompletion4Pair6_9L = homogeneousExponentSup (homogeneousCompletion4Leading 5) (homogeneousCompletion4Leading 8) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair6_9L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_9L (homogeneousCompletion4Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_9L (homogeneousCompletion4Leading 8) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair6_9U =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_9_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair6_9V =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_9_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair6_9D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair6_9D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair6_9L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair6_9D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair6_9L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair6_9_degree_bounds_check k)
  unfold homogeneousCompletion4Pair6_9S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_9D k)) 5 8 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair6_10S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 9
    (rationalSparsePolynomial homogeneousCompletion4Pair6_10U) (rationalSparsePolynomial homogeneousCompletion4Pair6_10V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_10D k))

theorem homogeneousCompletion4Pair6_10_relation : (∑ k, homogeneousCompletion4Pair6_10S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair6_10S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair6_10U homogeneousCompletion4Pair6_10V
    (homogeneousCompletion4G 5) (homogeneousCompletion4G 9) homogeneousCompletion4Pair6_10D homogeneousCompletion4G homogeneousCompletion4Pair6_10_sp_check

theorem homogeneousCompletion4Pair6_10_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair6_10S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair6_10S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair6_10U homogeneousCompletion4Pair6_10V
    (homogeneousCompletion4M (Fin.last 3) 5) (homogeneousCompletion4M (Fin.last 3) 9)
    homogeneousCompletion4Pair6_10D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair6_10W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair6_10_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair6_10D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair6_10_top :
    homogeneousCompletion4Pair6_10S 9 * homogeneousCompletion4GPoly 9 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair6_10S 9 * homogeneousCompletion4GPoly 9) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_10S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_10S 9 := by
  have hL0 : homogeneousCompletion4Pair6_10L = homogeneousExponentSup (homogeneousCompletion4Leading 5) (homogeneousCompletion4Leading 9) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair6_10L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_10L (homogeneousCompletion4Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_10L (homogeneousCompletion4Leading 9) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair6_10U =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_10_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair6_10V =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_10_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair6_10D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair6_10D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair6_10L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair6_10D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair6_10L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair6_10_degree_bounds_check k)
  unfold homogeneousCompletion4Pair6_10S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_10D k)) 5 9 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
