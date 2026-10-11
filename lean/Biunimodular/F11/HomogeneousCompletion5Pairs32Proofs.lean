/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs32Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs32OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair6_11S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 10
    (rationalSparsePolynomial homogeneousCompletion5Pair6_11U) (rationalSparsePolynomial homogeneousCompletion5Pair6_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_11D k))

theorem homogeneousCompletion5Pair6_11_relation : (∑ k, homogeneousCompletion5Pair6_11S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_11U homogeneousCompletion5Pair6_11V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 10) homogeneousCompletion5Pair6_11D homogeneousCompletion5G homogeneousCompletion5Pair6_11_sp_check

theorem homogeneousCompletion5Pair6_11_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_11S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_11U homogeneousCompletion5Pair6_11V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 10)
    homogeneousCompletion5Pair6_11D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_11W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_11D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_11_top :
    homogeneousCompletion5Pair6_11S 10 * homogeneousCompletion5GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_11S 10 * homogeneousCompletion5GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_11S 10 := by
  have hL0 : homogeneousCompletion5Pair6_11L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_11L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_11L (homogeneousCompletion5Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_11U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_11V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_11D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_11D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_11D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_11L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_11_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_11D k)) 5 10 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair6_12S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 11
    (rationalSparsePolynomial homogeneousCompletion5Pair6_12U) (rationalSparsePolynomial homogeneousCompletion5Pair6_12V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_12D k))

theorem homogeneousCompletion5Pair6_12_relation : (∑ k, homogeneousCompletion5Pair6_12S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_12S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_12U homogeneousCompletion5Pair6_12V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 11) homogeneousCompletion5Pair6_12D homogeneousCompletion5G homogeneousCompletion5Pair6_12_sp_check

theorem homogeneousCompletion5Pair6_12_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_12S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_12S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_12U homogeneousCompletion5Pair6_12V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 11)
    homogeneousCompletion5Pair6_12D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_12W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_12_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_12D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_12_top :
    homogeneousCompletion5Pair6_12S 11 * homogeneousCompletion5GPoly 11 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_12S 11 * homogeneousCompletion5GPoly 11) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_12S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_12S 11 := by
  have hL0 : homogeneousCompletion5Pair6_12L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 11) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_12L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_12L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_12L (homogeneousCompletion5Leading 11) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_12U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_12_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_12V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_12_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_12D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_12D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_12L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_12D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_12L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_12_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_12S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_12D k)) 5 11 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair6_13S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 12
    (rationalSparsePolynomial homogeneousCompletion5Pair6_13U) (rationalSparsePolynomial homogeneousCompletion5Pair6_13V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_13D k))

theorem homogeneousCompletion5Pair6_13_relation : (∑ k, homogeneousCompletion5Pair6_13S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_13S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_13U homogeneousCompletion5Pair6_13V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 12) homogeneousCompletion5Pair6_13D homogeneousCompletion5G homogeneousCompletion5Pair6_13_sp_check

theorem homogeneousCompletion5Pair6_13_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_13S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_13S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_13U homogeneousCompletion5Pair6_13V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 12)
    homogeneousCompletion5Pair6_13D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_13W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_13_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_13D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_13_top :
    homogeneousCompletion5Pair6_13S 12 * homogeneousCompletion5GPoly 12 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_13S 12 * homogeneousCompletion5GPoly 12) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_13S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_13S 12 := by
  have hL0 : homogeneousCompletion5Pair6_13L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 12) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_13L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_13L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_13L (homogeneousCompletion5Leading 12) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_13U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_13_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_13V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_13_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_13D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_13D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_13L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_13D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_13L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_13_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_13S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_13D k)) 5 12 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair6_14S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 13
    (rationalSparsePolynomial homogeneousCompletion5Pair6_14U) (rationalSparsePolynomial homogeneousCompletion5Pair6_14V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_14D k))

theorem homogeneousCompletion5Pair6_14_relation : (∑ k, homogeneousCompletion5Pair6_14S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair6_14S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair6_14U homogeneousCompletion5Pair6_14V
    (homogeneousCompletion5G 5) (homogeneousCompletion5G 13) homogeneousCompletion5Pair6_14D homogeneousCompletion5G homogeneousCompletion5Pair6_14_sp_check

theorem homogeneousCompletion5Pair6_14_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair6_14S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair6_14S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair6_14U homogeneousCompletion5Pair6_14V
    (homogeneousCompletion5M (Fin.last 4) 5) (homogeneousCompletion5M (Fin.last 4) 13)
    homogeneousCompletion5Pair6_14D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair6_14W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair6_14_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair6_14D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair6_14_top :
    homogeneousCompletion5Pair6_14S 13 * homogeneousCompletion5GPoly 13 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair6_14S 13 * homogeneousCompletion5GPoly 13) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_14S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair6_14S 13 := by
  have hL0 : homogeneousCompletion5Pair6_14L = homogeneousExponentSup (homogeneousCompletion5Leading 5) (homogeneousCompletion5Leading 13) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair6_14L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_14L (homogeneousCompletion5Leading 5) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair6_14L (homogeneousCompletion5Leading 13) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair6_14U =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_14_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair6_14V =
      monomial (homogeneousExponent homogeneousCompletion5Pair6_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair6_14_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair6_14D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair6_14D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair6_14L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair6_14D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair6_14L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair6_14_degree_bounds_check k)
  unfold homogeneousCompletion5Pair6_14S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair6_14D k)) 5 13 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
