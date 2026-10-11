/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs02Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs02OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair1_6S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 5
    (rationalSparsePolynomial homogeneousCompletion5Pair1_6U) (rationalSparsePolynomial homogeneousCompletion5Pair1_6V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_6D k))

theorem homogeneousCompletion5Pair1_6_relation : (∑ k, homogeneousCompletion5Pair1_6S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_6S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_6U homogeneousCompletion5Pair1_6V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 5) homogeneousCompletion5Pair1_6D homogeneousCompletion5G homogeneousCompletion5Pair1_6_sp_check

theorem homogeneousCompletion5Pair1_6_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_6S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_6S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_6U homogeneousCompletion5Pair1_6V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 5)
    homogeneousCompletion5Pair1_6D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_6W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_6_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_6D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_6_top :
    homogeneousCompletion5Pair1_6S 5 * homogeneousCompletion5GPoly 5 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_6S 5 * homogeneousCompletion5GPoly 5) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_6S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_6S 5 := by
  have hL0 : homogeneousCompletion5Pair1_6L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 5) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_6L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_6L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_6L (homogeneousCompletion5Leading 5) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_6U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_6_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_6V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_6_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_6D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_6D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_6L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_6D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_6L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_6_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_6S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_6D k)) 0 5 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair1_7S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 6
    (rationalSparsePolynomial homogeneousCompletion5Pair1_7U) (rationalSparsePolynomial homogeneousCompletion5Pair1_7V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_7D k))

theorem homogeneousCompletion5Pair1_7_relation : (∑ k, homogeneousCompletion5Pair1_7S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_7S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_7U homogeneousCompletion5Pair1_7V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 6) homogeneousCompletion5Pair1_7D homogeneousCompletion5G homogeneousCompletion5Pair1_7_sp_check

theorem homogeneousCompletion5Pair1_7_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_7S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_7S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_7U homogeneousCompletion5Pair1_7V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 6)
    homogeneousCompletion5Pair1_7D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_7W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_7_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_7D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_7_top :
    homogeneousCompletion5Pair1_7S 6 * homogeneousCompletion5GPoly 6 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_7S 6 * homogeneousCompletion5GPoly 6) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_7S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_7S 6 := by
  have hL0 : homogeneousCompletion5Pair1_7L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 6) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_7L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_7L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_7L (homogeneousCompletion5Leading 6) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_7U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_7_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_7V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_7_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_7D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_7D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_7L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_7D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_7L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_7_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_7S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_7D k)) 0 6 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair1_8S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 7
    (rationalSparsePolynomial homogeneousCompletion5Pair1_8U) (rationalSparsePolynomial homogeneousCompletion5Pair1_8V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_8D k))

theorem homogeneousCompletion5Pair1_8_relation : (∑ k, homogeneousCompletion5Pair1_8S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_8S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_8U homogeneousCompletion5Pair1_8V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 7) homogeneousCompletion5Pair1_8D homogeneousCompletion5G homogeneousCompletion5Pair1_8_sp_check

theorem homogeneousCompletion5Pair1_8_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_8S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_8S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_8U homogeneousCompletion5Pair1_8V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 7)
    homogeneousCompletion5Pair1_8D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_8W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_8_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_8D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_8_top :
    homogeneousCompletion5Pair1_8S 7 * homogeneousCompletion5GPoly 7 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_8S 7 * homogeneousCompletion5GPoly 7) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_8S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_8S 7 := by
  have hL0 : homogeneousCompletion5Pair1_8L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 7) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_8L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_8L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_8L (homogeneousCompletion5Leading 7) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_8U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_8_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_8V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_8_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_8D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_8D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_8L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_8D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_8L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_8_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_8S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_8D k)) 0 7 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair1_9S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 8
    (rationalSparsePolynomial homogeneousCompletion5Pair1_9U) (rationalSparsePolynomial homogeneousCompletion5Pair1_9V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_9D k))

theorem homogeneousCompletion5Pair1_9_relation : (∑ k, homogeneousCompletion5Pair1_9S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_9S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_9U homogeneousCompletion5Pair1_9V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 8) homogeneousCompletion5Pair1_9D homogeneousCompletion5G homogeneousCompletion5Pair1_9_sp_check

theorem homogeneousCompletion5Pair1_9_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_9S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_9S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_9U homogeneousCompletion5Pair1_9V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 8)
    homogeneousCompletion5Pair1_9D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_9W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_9_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_9D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_9_top :
    homogeneousCompletion5Pair1_9S 8 * homogeneousCompletion5GPoly 8 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_9S 8 * homogeneousCompletion5GPoly 8) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_9S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_9S 8 := by
  have hL0 : homogeneousCompletion5Pair1_9L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 8) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_9L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_9L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_9L (homogeneousCompletion5Leading 8) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_9U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_9_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_9V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_9_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_9D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_9D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_9L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_9D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_9L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_9_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_9S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_9D k)) 0 8 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
