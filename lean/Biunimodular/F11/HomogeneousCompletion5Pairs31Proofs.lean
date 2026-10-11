/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs31Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs31OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair6_7S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 6
    (rationalSparsePolynomial homogeneousCompletion5Pair6_7U) (rationalSparsePolynomial homogeneousCompletion5Pair6_7V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_7D k))

theorem homogeneousCompletion5Pair6_7_relation : (∑ k, homogeneousCompletion5Pair6_7S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_7S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_7U homogeneousCompletion5Pair6_7V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 6) homogeneousCompletion5Pair6_7D homogeneousCompletion5G homogeneousCompletion5Pair6_7_sp_check

theorem homogeneousCompletion5Pair6_7_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_7S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_7S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_7U homogeneousCompletion5Pair6_7V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 6)
    homogeneousCompletion5Pair6_7D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_7W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_7_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_7D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_7_top :
    homogeneousCompletion5Pair6_7S 6 * homogeneousCompletion5GPoly 6 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_7S 6 * homogeneousCompletion5GPoly 6) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_7S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_7S 6 := by
  have hL0 : homogeneousCompletion5Pair6_7L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 6) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_7L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_7L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_7L (homogeneousCompletion5Leading 6) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_7U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_7_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_7V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_7_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_7D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_7D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_7L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_7D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_7L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_7_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_7S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_7D k)) 5 6 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair6_8S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 7
    (rationalSparsePolynomial homogeneousCompletion5Pair6_8U) (rationalSparsePolynomial homogeneousCompletion5Pair6_8V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_8D k))

theorem homogeneousCompletion5Pair6_8_relation : (∑ k, homogeneousCompletion5Pair6_8S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_8S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_8U homogeneousCompletion5Pair6_8V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 7) homogeneousCompletion5Pair6_8D homogeneousCompletion5G homogeneousCompletion5Pair6_8_sp_check

theorem homogeneousCompletion5Pair6_8_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_8S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_8S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_8U homogeneousCompletion5Pair6_8V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 7)
    homogeneousCompletion5Pair6_8D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_8W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_8_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_8D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_8_top :
    homogeneousCompletion5Pair6_8S 7 * homogeneousCompletion5GPoly 7 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_8S 7 * homogeneousCompletion5GPoly 7) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_8S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_8S 7 := by
  have hL0 : homogeneousCompletion5Pair6_8L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 7) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_8L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_8L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_8L (homogeneousCompletion5Leading 7) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_8U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_8_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_8V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_8_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_8D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_8D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_8L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_8D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_8L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_8_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_8S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_8D k)) 5 7 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair6_9S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 8
    (rationalSparsePolynomial homogeneousCompletion5Pair6_9U) (rationalSparsePolynomial homogeneousCompletion5Pair6_9V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_9D k))

theorem homogeneousCompletion5Pair6_9_relation : (∑ k, homogeneousCompletion5Pair6_9S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_9S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_9U homogeneousCompletion5Pair6_9V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 8) homogeneousCompletion5Pair6_9D homogeneousCompletion5G homogeneousCompletion5Pair6_9_sp_check

theorem homogeneousCompletion5Pair6_9_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_9S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_9S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_9U homogeneousCompletion5Pair6_9V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 8)
    homogeneousCompletion5Pair6_9D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_9W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_9_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_9D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_9_top :
    homogeneousCompletion5Pair6_9S 8 * homogeneousCompletion5GPoly 8 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_9S 8 * homogeneousCompletion5GPoly 8) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_9S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_9S 8 := by
  have hL0 : homogeneousCompletion5Pair6_9L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 8) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_9L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_9L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_9L (homogeneousCompletion5Leading 8) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_9U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_9_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_9V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_9_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_9D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_9D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_9L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_9D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_9L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_9_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_9S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_9D k)) 5 8 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair6_10S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 9
    (rationalSparsePolynomial homogeneousCompletion5Pair6_10U) (rationalSparsePolynomial homogeneousCompletion5Pair6_10V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_10D k))

theorem homogeneousCompletion5Pair6_10_relation : (∑ k, homogeneousCompletion5Pair6_10S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_10S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_10U homogeneousCompletion5Pair6_10V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 9) homogeneousCompletion5Pair6_10D homogeneousCompletion5G homogeneousCompletion5Pair6_10_sp_check

theorem homogeneousCompletion5Pair6_10_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_10S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_10S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_10U homogeneousCompletion5Pair6_10V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 9)
    homogeneousCompletion5Pair6_10D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_10W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_10_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_10D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_10_top :
    homogeneousCompletion5Pair6_10S 9 * homogeneousCompletion5GPoly 9 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_10S 9 * homogeneousCompletion5GPoly 9) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_10S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_10S 9 := by
  have hL0 : homogeneousCompletion5Pair6_10L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 9) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_10L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_10L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_10L (homogeneousCompletion5Leading 9) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_10U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_10_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_10V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_10_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_10D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_10D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_10L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_10D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_10L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_10_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_10S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_10D k)) 5 9 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
