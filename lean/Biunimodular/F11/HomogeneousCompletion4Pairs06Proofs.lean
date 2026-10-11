/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs06Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs06OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair2_9S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 8
    (rationalSparsePolynomial homogeneousCompletion4Pair2_9U) (rationalSparsePolynomial homogeneousCompletion4Pair2_9V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_9D k))

theorem homogeneousCompletion4Pair2_9_relation : (∑ k, homogeneousCompletion4Pair2_9S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair2_9S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair2_9U homogeneousCompletion4Pair2_9V
    (homogeneousCompletion4G 1) (homogeneousCompletion4G 8) homogeneousCompletion4Pair2_9D homogeneousCompletion4G homogeneousCompletion4Pair2_9_sp_check

theorem homogeneousCompletion4Pair2_9_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair2_9S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair2_9S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair2_9U homogeneousCompletion4Pair2_9V
    (homogeneousCompletion4M (Fin.last 3) 1) (homogeneousCompletion4M (Fin.last 3) 8)
    homogeneousCompletion4Pair2_9D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair2_9W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair2_9_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair2_9D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair2_9_top :
    homogeneousCompletion4Pair2_9S 8 * homogeneousCompletion4GPoly 8 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair2_9S 8 * homogeneousCompletion4GPoly 8) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_9S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_9S 8 := by
  have hL0 : homogeneousCompletion4Pair2_9L = homogeneousExponentSup (homogeneousCompletion4Leading 1) (homogeneousCompletion4Leading 8) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair2_9L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 2, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_9L (homogeneousCompletion4Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_9L (homogeneousCompletion4Leading 8) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair2_9U =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_9_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair2_9V =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_9L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 8)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_9_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair2_9D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair2_9D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair2_9L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair2_9D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair2_9L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair2_9_degree_bounds_check k)
  unfold homogeneousCompletion4Pair2_9S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_9D k)) 1 8 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair2_10S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 9
    (rationalSparsePolynomial homogeneousCompletion4Pair2_10U) (rationalSparsePolynomial homogeneousCompletion4Pair2_10V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_10D k))

theorem homogeneousCompletion4Pair2_10_relation : (∑ k, homogeneousCompletion4Pair2_10S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair2_10S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair2_10U homogeneousCompletion4Pair2_10V
    (homogeneousCompletion4G 1) (homogeneousCompletion4G 9) homogeneousCompletion4Pair2_10D homogeneousCompletion4G homogeneousCompletion4Pair2_10_sp_check

theorem homogeneousCompletion4Pair2_10_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair2_10S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair2_10S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair2_10U homogeneousCompletion4Pair2_10V
    (homogeneousCompletion4M (Fin.last 3) 1) (homogeneousCompletion4M (Fin.last 3) 9)
    homogeneousCompletion4Pair2_10D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair2_10W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair2_10_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair2_10D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair2_10_top :
    homogeneousCompletion4Pair2_10S 9 * homogeneousCompletion4GPoly 9 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair2_10S 9 * homogeneousCompletion4GPoly 9) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_10S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_10S 9 := by
  have hL0 : homogeneousCompletion4Pair2_10L = homogeneousExponentSup (homogeneousCompletion4Leading 1) (homogeneousCompletion4Leading 9) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair2_10L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 2, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_10L (homogeneousCompletion4Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_10L (homogeneousCompletion4Leading 9) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair2_10U =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_10_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair2_10V =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_10L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_10_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair2_10D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair2_10D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair2_10L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair2_10D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair2_10L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair2_10_degree_bounds_check k)
  unfold homogeneousCompletion4Pair2_10S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_10D k)) 1 9 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair2_11S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 10
    (rationalSparsePolynomial homogeneousCompletion4Pair2_11U) (rationalSparsePolynomial homogeneousCompletion4Pair2_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_11D k))

theorem homogeneousCompletion4Pair2_11_relation : (∑ k, homogeneousCompletion4Pair2_11S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair2_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair2_11U homogeneousCompletion4Pair2_11V
    (homogeneousCompletion4G 1) (homogeneousCompletion4G 10) homogeneousCompletion4Pair2_11D homogeneousCompletion4G homogeneousCompletion4Pair2_11_sp_check

theorem homogeneousCompletion4Pair2_11_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair2_11S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair2_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair2_11U homogeneousCompletion4Pair2_11V
    (homogeneousCompletion4M (Fin.last 3) 1) (homogeneousCompletion4M (Fin.last 3) 10)
    homogeneousCompletion4Pair2_11D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair2_11W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair2_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair2_11D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair2_11_top :
    homogeneousCompletion4Pair2_11S 10 * homogeneousCompletion4GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair2_11S 10 * homogeneousCompletion4GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_11S 10 := by
  have hL0 : homogeneousCompletion4Pair2_11L = homogeneousExponentSup (homogeneousCompletion4Leading 1) (homogeneousCompletion4Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair2_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 1, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_11L (homogeneousCompletion4Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_11L (homogeneousCompletion4Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair2_11U =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair2_11V =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair2_11D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair2_11D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair2_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair2_11D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair2_11L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair2_11_degree_bounds_check k)
  unfold homogeneousCompletion4Pair2_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_11D k)) 1 10 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair2_12S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 11
    (rationalSparsePolynomial homogeneousCompletion4Pair2_12U) (rationalSparsePolynomial homogeneousCompletion4Pair2_12V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_12D k))

theorem homogeneousCompletion4Pair2_12_relation : (∑ k, homogeneousCompletion4Pair2_12S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair2_12S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair2_12U homogeneousCompletion4Pair2_12V
    (homogeneousCompletion4G 1) (homogeneousCompletion4G 11) homogeneousCompletion4Pair2_12D homogeneousCompletion4G homogeneousCompletion4Pair2_12_sp_check

theorem homogeneousCompletion4Pair2_12_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair2_12S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair2_12S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair2_12U homogeneousCompletion4Pair2_12V
    (homogeneousCompletion4M (Fin.last 3) 1) (homogeneousCompletion4M (Fin.last 3) 11)
    homogeneousCompletion4Pair2_12D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair2_12W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair2_12_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair2_12D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair2_12_top :
    homogeneousCompletion4Pair2_12S 11 * homogeneousCompletion4GPoly 11 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair2_12S 11 * homogeneousCompletion4GPoly 11) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_12S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_12S 11 := by
  have hL0 : homogeneousCompletion4Pair2_12L = homogeneousExponentSup (homogeneousCompletion4Leading 1) (homogeneousCompletion4Leading 11) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair2_12L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_12L (homogeneousCompletion4Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_12L (homogeneousCompletion4Leading 11) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair2_12U =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_12_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair2_12V =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_12_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair2_12D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair2_12D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair2_12L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair2_12D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair2_12L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair2_12_degree_bounds_check k)
  unfold homogeneousCompletion4Pair2_12S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_12D k)) 1 11 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
