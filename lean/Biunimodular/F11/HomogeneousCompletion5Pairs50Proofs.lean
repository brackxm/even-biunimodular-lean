/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs50Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs50OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair9_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 8 25
    (rationalSparsePolynomial homogeneousCompletion5Pair9_26U) (rationalSparsePolynomial homogeneousCompletion5Pair9_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_26D k))

theorem homogeneousCompletion5Pair9_26_relation : (∑ k, homogeneousCompletion5Pair9_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair9_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair9_26U homogeneousCompletion5Pair9_26V
    (homogeneousCompletion5G 8) (homogeneousCompletion5G 25) homogeneousCompletion5Pair9_26D homogeneousCompletion5G homogeneousCompletion5Pair9_26_sp_check

theorem homogeneousCompletion5Pair9_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair9_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair9_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair9_26U homogeneousCompletion5Pair9_26V
    (homogeneousCompletion5M (Fin.last 4) 8) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair9_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair9_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair9_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair9_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair9_26_top :
    homogeneousCompletion5Pair9_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair9_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_26S 25 := by
  have hL0 : homogeneousCompletion5Pair9_26L = homogeneousExponentSup (homogeneousCompletion5Leading 8) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair9_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 5, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_26L (homogeneousCompletion5Leading 8) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair9_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair9_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair9_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair9_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair9_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair9_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair9_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair9_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair9_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_26D k)) 8 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair9_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 8 26
    (rationalSparsePolynomial homogeneousCompletion5Pair9_27U) (rationalSparsePolynomial homogeneousCompletion5Pair9_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_27D k))

theorem homogeneousCompletion5Pair9_27_relation : (∑ k, homogeneousCompletion5Pair9_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair9_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair9_27U homogeneousCompletion5Pair9_27V
    (homogeneousCompletion5G 8) (homogeneousCompletion5G 26) homogeneousCompletion5Pair9_27D homogeneousCompletion5G homogeneousCompletion5Pair9_27_sp_check

theorem homogeneousCompletion5Pair9_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair9_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair9_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair9_27U homogeneousCompletion5Pair9_27V
    (homogeneousCompletion5M (Fin.last 4) 8) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair9_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair9_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair9_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair9_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair9_27_top :
    homogeneousCompletion5Pair9_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair9_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair9_27S 26 := by
  have hL0 : homogeneousCompletion5Pair9_27L = homogeneousExponentSup (homogeneousCompletion5Leading 8) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair9_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 5, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_27L (homogeneousCompletion5Leading 8) := by native_decide
  have hV0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair9_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair9_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair9_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair9_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair9_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair9_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair9_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair9_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair9_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair9_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair9_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair9_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair9_27D k)) 8 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair10_11S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 10
    (rationalSparsePolynomial homogeneousCompletion5Pair10_11U) (rationalSparsePolynomial homogeneousCompletion5Pair10_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_11D k))

theorem homogeneousCompletion5Pair10_11_relation : (∑ k, homogeneousCompletion5Pair10_11S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_11U homogeneousCompletion5Pair10_11V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 10) homogeneousCompletion5Pair10_11D homogeneousCompletion5G homogeneousCompletion5Pair10_11_sp_check

theorem homogeneousCompletion5Pair10_11_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_11S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_11U homogeneousCompletion5Pair10_11V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 10)
    homogeneousCompletion5Pair10_11D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_11W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_11D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_11_top :
    homogeneousCompletion5Pair10_11S 10 * homogeneousCompletion5GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_11S 10 * homogeneousCompletion5GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_11S 10 := by
  have hL0 : homogeneousCompletion5Pair10_11L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_11L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_11L (homogeneousCompletion5Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_11U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_11V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_11D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_11D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_11D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_11L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_11_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_11D k)) 9 10 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair10_12S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 11
    (rationalSparsePolynomial homogeneousCompletion5Pair10_12U) (rationalSparsePolynomial homogeneousCompletion5Pair10_12V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_12D k))

theorem homogeneousCompletion5Pair10_12_relation : (∑ k, homogeneousCompletion5Pair10_12S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_12S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_12U homogeneousCompletion5Pair10_12V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 11) homogeneousCompletion5Pair10_12D homogeneousCompletion5G homogeneousCompletion5Pair10_12_sp_check

theorem homogeneousCompletion5Pair10_12_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_12S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_12S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_12U homogeneousCompletion5Pair10_12V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 11)
    homogeneousCompletion5Pair10_12D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_12W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_12_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_12D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_12_top :
    homogeneousCompletion5Pair10_12S 11 * homogeneousCompletion5GPoly 11 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_12S 11 * homogeneousCompletion5GPoly 11) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_12S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_12S 11 := by
  have hL0 : homogeneousCompletion5Pair10_12L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 11) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_12L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_12L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_12L (homogeneousCompletion5Leading 11) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_12U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_12_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_12V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_12_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_12D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_12D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_12L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_12D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_12L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_12_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_12S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_12D k)) 9 11 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
