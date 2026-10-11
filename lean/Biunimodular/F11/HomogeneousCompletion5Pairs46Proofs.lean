/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs46Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs46OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair9_10S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 8 9
    (rationalSparsePolynomial homogeneousCompletion5Pair9_10U) (rationalSparsePolynomial homogeneousCompletion5Pair9_10V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_10D k))

theorem homogeneousCompletion5Pair9_10_relation : (∑ k, homogeneousCompletion5Pair9_10S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair9_10S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair9_10U homogeneousCompletion5Pair9_10V
    (homogeneousCompletion5G 8) (homogeneousCompletion5G 9) homogeneousCompletion5Pair9_10D homogeneousCompletion5G homogeneousCompletion5Pair9_10_sp_check

theorem homogeneousCompletion5Pair9_10_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair9_10S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair9_10S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair9_10U homogeneousCompletion5Pair9_10V
    (homogeneousCompletion5M (Fin.last 4) 8) (homogeneousCompletion5M (Fin.last 4) 9)
    homogeneousCompletion5Pair9_10D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair9_10W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair9_10_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair9_10D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair9_10_top :
    homogeneousCompletion5Pair9_10S 9 * homogeneousCompletion5GPoly 9 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair9_10S 9 * homogeneousCompletion5GPoly 9) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_10S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_10S 9 := by
  have hL0 : homogeneousCompletion5Pair9_10L = homogeneousExponentSup (homogeneousCompletion5Leading 8) (homogeneousCompletion5Leading 9) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair9_10L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_10L (homogeneousCompletion5Leading 8) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_10L (homogeneousCompletion5Leading 9) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair9_10U =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_10_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair9_10V =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_10_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair9_10D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair9_10D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair9_10L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair9_10D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair9_10L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair9_10_degree_bounds_check k)
  unfold homogeneousCompletion5Pair9_10S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_10D k)) 8 9 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair9_11S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 8 10
    (rationalSparsePolynomial homogeneousCompletion5Pair9_11U) (rationalSparsePolynomial homogeneousCompletion5Pair9_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_11D k))

theorem homogeneousCompletion5Pair9_11_relation : (∑ k, homogeneousCompletion5Pair9_11S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair9_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair9_11U homogeneousCompletion5Pair9_11V
    (homogeneousCompletion5G 8) (homogeneousCompletion5G 10) homogeneousCompletion5Pair9_11D homogeneousCompletion5G homogeneousCompletion5Pair9_11_sp_check

theorem homogeneousCompletion5Pair9_11_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair9_11S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair9_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair9_11U homogeneousCompletion5Pair9_11V
    (homogeneousCompletion5M (Fin.last 4) 8) (homogeneousCompletion5M (Fin.last 4) 10)
    homogeneousCompletion5Pair9_11D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair9_11W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair9_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair9_11D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair9_11_top :
    homogeneousCompletion5Pair9_11S 10 * homogeneousCompletion5GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair9_11S 10 * homogeneousCompletion5GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_11S 10 := by
  have hL0 : homogeneousCompletion5Pair9_11L = homogeneousExponentSup (homogeneousCompletion5Leading 8) (homogeneousCompletion5Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair9_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_11L (homogeneousCompletion5Leading 8) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_11L (homogeneousCompletion5Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair9_11U =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair9_11V =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair9_11D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair9_11D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair9_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair9_11D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair9_11L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair9_11_degree_bounds_check k)
  unfold homogeneousCompletion5Pair9_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_11D k)) 8 10 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair9_12S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 8 11
    (rationalSparsePolynomial homogeneousCompletion5Pair9_12U) (rationalSparsePolynomial homogeneousCompletion5Pair9_12V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_12D k))

theorem homogeneousCompletion5Pair9_12_relation : (∑ k, homogeneousCompletion5Pair9_12S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair9_12S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair9_12U homogeneousCompletion5Pair9_12V
    (homogeneousCompletion5G 8) (homogeneousCompletion5G 11) homogeneousCompletion5Pair9_12D homogeneousCompletion5G homogeneousCompletion5Pair9_12_sp_check

theorem homogeneousCompletion5Pair9_12_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair9_12S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair9_12S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair9_12U homogeneousCompletion5Pair9_12V
    (homogeneousCompletion5M (Fin.last 4) 8) (homogeneousCompletion5M (Fin.last 4) 11)
    homogeneousCompletion5Pair9_12D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair9_12W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair9_12_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair9_12D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair9_12_top :
    homogeneousCompletion5Pair9_12S 11 * homogeneousCompletion5GPoly 11 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair9_12S 11 * homogeneousCompletion5GPoly 11) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_12S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_12S 11 := by
  have hL0 : homogeneousCompletion5Pair9_12L = homogeneousExponentSup (homogeneousCompletion5Leading 8) (homogeneousCompletion5Leading 11) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair9_12L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_12L (homogeneousCompletion5Leading 8) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_12L (homogeneousCompletion5Leading 11) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair9_12U =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_12_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair9_12V =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_12_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair9_12D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair9_12D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair9_12L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair9_12D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair9_12L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair9_12_degree_bounds_check k)
  unfold homogeneousCompletion5Pair9_12S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_12D k)) 8 11 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair9_13S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 8 12
    (rationalSparsePolynomial homogeneousCompletion5Pair9_13U) (rationalSparsePolynomial homogeneousCompletion5Pair9_13V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_13D k))

theorem homogeneousCompletion5Pair9_13_relation : (∑ k, homogeneousCompletion5Pair9_13S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair9_13S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair9_13U homogeneousCompletion5Pair9_13V
    (homogeneousCompletion5G 8) (homogeneousCompletion5G 12) homogeneousCompletion5Pair9_13D homogeneousCompletion5G homogeneousCompletion5Pair9_13_sp_check

theorem homogeneousCompletion5Pair9_13_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair9_13S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair9_13S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair9_13U homogeneousCompletion5Pair9_13V
    (homogeneousCompletion5M (Fin.last 4) 8) (homogeneousCompletion5M (Fin.last 4) 12)
    homogeneousCompletion5Pair9_13D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair9_13W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair9_13_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair9_13D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair9_13_top :
    homogeneousCompletion5Pair9_13S 12 * homogeneousCompletion5GPoly 12 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair9_13S 12 * homogeneousCompletion5GPoly 12) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_13S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_13S 12 := by
  have hL0 : homogeneousCompletion5Pair9_13L = homogeneousExponentSup (homogeneousCompletion5Leading 8) (homogeneousCompletion5Leading 12) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair9_13L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_13L (homogeneousCompletion5Leading 8) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_13L (homogeneousCompletion5Leading 12) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair9_13U =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_13_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair9_13V =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_13_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair9_13D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair9_13D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair9_13L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair9_13D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair9_13L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair9_13_degree_bounds_check k)
  unfold homogeneousCompletion5Pair9_13S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_13D k)) 8 12 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
