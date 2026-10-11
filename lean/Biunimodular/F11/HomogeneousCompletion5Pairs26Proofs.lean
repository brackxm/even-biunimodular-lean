/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs26Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs26OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair5_8S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 7
    (rationalSparsePolynomial homogeneousCompletion5Pair5_8U) (rationalSparsePolynomial homogeneousCompletion5Pair5_8V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_8D k))

theorem homogeneousCompletion5Pair5_8_relation : (∑ k, homogeneousCompletion5Pair5_8S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_8S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_8U homogeneousCompletion5Pair5_8V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 7) homogeneousCompletion5Pair5_8D homogeneousCompletion5G homogeneousCompletion5Pair5_8_sp_check

theorem homogeneousCompletion5Pair5_8_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_8S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_8S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_8U homogeneousCompletion5Pair5_8V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 7)
    homogeneousCompletion5Pair5_8D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_8W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_8_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_8D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_8_top :
    homogeneousCompletion5Pair5_8S 7 * homogeneousCompletion5GPoly 7 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_8S 7 * homogeneousCompletion5GPoly 7) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_8S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_8S 7 := by
  have hL0 : homogeneousCompletion5Pair5_8L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 7) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_8L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 1, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_8L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_8L (homogeneousCompletion5Leading 7) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_8U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_8_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_8V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_8L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 7)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_8_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_8D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_8D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_8L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_8D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_8L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_8_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_8S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_8D k)) 4 7 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair5_9S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 8
    (rationalSparsePolynomial homogeneousCompletion5Pair5_9U) (rationalSparsePolynomial homogeneousCompletion5Pair5_9V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_9D k))

theorem homogeneousCompletion5Pair5_9_relation : (∑ k, homogeneousCompletion5Pair5_9S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_9S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_9U homogeneousCompletion5Pair5_9V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 8) homogeneousCompletion5Pair5_9D homogeneousCompletion5G homogeneousCompletion5Pair5_9_sp_check

theorem homogeneousCompletion5Pair5_9_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_9S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_9S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_9U homogeneousCompletion5Pair5_9V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 8)
    homogeneousCompletion5Pair5_9D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_9W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_9_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_9D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_9_top :
    homogeneousCompletion5Pair5_9S 8 * homogeneousCompletion5GPoly 8 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_9S 8 * homogeneousCompletion5GPoly 8) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_9S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_9S 8 := by
  have hL0 : homogeneousCompletion5Pair5_9L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 8) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_9L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 2, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_9L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_9L (homogeneousCompletion5Leading 8) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_9U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_9_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_9V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_9_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_9D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_9D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_9L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_9D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_9L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_9_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_9S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_9D k)) 4 8 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair5_10S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 9
    (rationalSparsePolynomial homogeneousCompletion5Pair5_10U) (rationalSparsePolynomial homogeneousCompletion5Pair5_10V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_10D k))

theorem homogeneousCompletion5Pair5_10_relation : (∑ k, homogeneousCompletion5Pair5_10S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_10S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_10U homogeneousCompletion5Pair5_10V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 9) homogeneousCompletion5Pair5_10D homogeneousCompletion5G homogeneousCompletion5Pair5_10_sp_check

theorem homogeneousCompletion5Pair5_10_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_10S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_10S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_10U homogeneousCompletion5Pair5_10V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 9)
    homogeneousCompletion5Pair5_10D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_10W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_10_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_10D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_10_top :
    homogeneousCompletion5Pair5_10S 9 * homogeneousCompletion5GPoly 9 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_10S 9 * homogeneousCompletion5GPoly 9) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_10S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_10S 9 := by
  have hL0 : homogeneousCompletion5Pair5_10L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 9) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_10L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_10L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_10L (homogeneousCompletion5Leading 9) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_10U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_10_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_10V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_10_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_10D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_10D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_10L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_10D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_10L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_10_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_10S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_10D k)) 4 9 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair5_11S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 10
    (rationalSparsePolynomial homogeneousCompletion5Pair5_11U) (rationalSparsePolynomial homogeneousCompletion5Pair5_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_11D k))

theorem homogeneousCompletion5Pair5_11_relation : (∑ k, homogeneousCompletion5Pair5_11S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_11U homogeneousCompletion5Pair5_11V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 10) homogeneousCompletion5Pair5_11D homogeneousCompletion5G homogeneousCompletion5Pair5_11_sp_check

theorem homogeneousCompletion5Pair5_11_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_11S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_11U homogeneousCompletion5Pair5_11V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 10)
    homogeneousCompletion5Pair5_11D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_11W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_11D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_11_top :
    homogeneousCompletion5Pair5_11S 10 * homogeneousCompletion5GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_11S 10 * homogeneousCompletion5GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_11S 10 := by
  have hL0 : homogeneousCompletion5Pair5_11L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 1, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_11L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_11L (homogeneousCompletion5Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_11U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_11V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_11D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_11D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_11D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_11L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_11_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_11D k)) 4 10 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
