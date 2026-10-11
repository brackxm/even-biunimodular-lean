/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs17Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs17OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair6_11S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 10
    (rationalSparsePolynomial homogeneousCompletion4Pair6_11U) (rationalSparsePolynomial homogeneousCompletion4Pair6_11V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_11D k))

theorem homogeneousCompletion4Pair6_11_relation : (∑ k, homogeneousCompletion4Pair6_11S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair6_11S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair6_11U homogeneousCompletion4Pair6_11V
    (homogeneousCompletion4G 5) (homogeneousCompletion4G 10) homogeneousCompletion4Pair6_11D homogeneousCompletion4G homogeneousCompletion4Pair6_11_sp_check

theorem homogeneousCompletion4Pair6_11_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair6_11S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair6_11S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair6_11U homogeneousCompletion4Pair6_11V
    (homogeneousCompletion4M (Fin.last 3) 5) (homogeneousCompletion4M (Fin.last 3) 10)
    homogeneousCompletion4Pair6_11D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair6_11W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair6_11_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair6_11D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair6_11_top :
    homogeneousCompletion4Pair6_11S 10 * homogeneousCompletion4GPoly 10 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair6_11S 10 * homogeneousCompletion4GPoly 10) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_11S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_11S 10 := by
  have hL0 : homogeneousCompletion4Pair6_11L = homogeneousExponentSup (homogeneousCompletion4Leading 5) (homogeneousCompletion4Leading 10) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair6_11L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_11L (homogeneousCompletion4Leading 5) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_11L (homogeneousCompletion4Leading 10) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair6_11U =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_11_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair6_11V =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_11L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_11_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair6_11D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair6_11D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair6_11L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair6_11D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair6_11L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair6_11_degree_bounds_check k)
  unfold homogeneousCompletion4Pair6_11S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_11D k)) 5 10 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair6_12S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 11
    (rationalSparsePolynomial homogeneousCompletion4Pair6_12U) (rationalSparsePolynomial homogeneousCompletion4Pair6_12V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_12D k))

theorem homogeneousCompletion4Pair6_12_relation : (∑ k, homogeneousCompletion4Pair6_12S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair6_12S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair6_12U homogeneousCompletion4Pair6_12V
    (homogeneousCompletion4G 5) (homogeneousCompletion4G 11) homogeneousCompletion4Pair6_12D homogeneousCompletion4G homogeneousCompletion4Pair6_12_sp_check

theorem homogeneousCompletion4Pair6_12_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair6_12S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair6_12S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair6_12U homogeneousCompletion4Pair6_12V
    (homogeneousCompletion4M (Fin.last 3) 5) (homogeneousCompletion4M (Fin.last 3) 11)
    homogeneousCompletion4Pair6_12D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair6_12W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair6_12_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair6_12D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair6_12_top :
    homogeneousCompletion4Pair6_12S 11 * homogeneousCompletion4GPoly 11 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair6_12S 11 * homogeneousCompletion4GPoly 11) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_12S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_12S 11 := by
  have hL0 : homogeneousCompletion4Pair6_12L = homogeneousExponentSup (homogeneousCompletion4Leading 5) (homogeneousCompletion4Leading 11) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair6_12L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 1, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_12L (homogeneousCompletion4Leading 5) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_12L (homogeneousCompletion4Leading 11) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair6_12U =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_12_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair6_12V =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_12L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 11)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_12_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair6_12D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair6_12D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair6_12L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair6_12D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair6_12L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair6_12_degree_bounds_check k)
  unfold homogeneousCompletion4Pair6_12S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_12D k)) 5 11 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair6_13S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 12
    (rationalSparsePolynomial homogeneousCompletion4Pair6_13U) (rationalSparsePolynomial homogeneousCompletion4Pair6_13V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_13D k))

theorem homogeneousCompletion4Pair6_13_relation : (∑ k, homogeneousCompletion4Pair6_13S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair6_13S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair6_13U homogeneousCompletion4Pair6_13V
    (homogeneousCompletion4G 5) (homogeneousCompletion4G 12) homogeneousCompletion4Pair6_13D homogeneousCompletion4G homogeneousCompletion4Pair6_13_sp_check

theorem homogeneousCompletion4Pair6_13_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair6_13S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair6_13S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair6_13U homogeneousCompletion4Pair6_13V
    (homogeneousCompletion4M (Fin.last 3) 5) (homogeneousCompletion4M (Fin.last 3) 12)
    homogeneousCompletion4Pair6_13D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair6_13W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair6_13_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair6_13D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair6_13_top :
    homogeneousCompletion4Pair6_13S 12 * homogeneousCompletion4GPoly 12 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair6_13S 12 * homogeneousCompletion4GPoly 12) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_13S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_13S 12 := by
  have hL0 : homogeneousCompletion4Pair6_13L = homogeneousExponentSup (homogeneousCompletion4Leading 5) (homogeneousCompletion4Leading 12) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair6_13L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_13L (homogeneousCompletion4Leading 5) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_13L (homogeneousCompletion4Leading 12) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair6_13U =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_13_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair6_13V =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_13L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 12)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_13_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair6_13D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair6_13D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair6_13L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair6_13D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair6_13L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair6_13_degree_bounds_check k)
  unfold homogeneousCompletion4Pair6_13S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_13D k)) 5 12 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair6_14S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 5 13
    (rationalSparsePolynomial homogeneousCompletion4Pair6_14U) (rationalSparsePolynomial homogeneousCompletion4Pair6_14V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_14D k))

theorem homogeneousCompletion4Pair6_14_relation : (∑ k, homogeneousCompletion4Pair6_14S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair6_14S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair6_14U homogeneousCompletion4Pair6_14V
    (homogeneousCompletion4G 5) (homogeneousCompletion4G 13) homogeneousCompletion4Pair6_14D homogeneousCompletion4G homogeneousCompletion4Pair6_14_sp_check

theorem homogeneousCompletion4Pair6_14_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair6_14S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair6_14S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair6_14U homogeneousCompletion4Pair6_14V
    (homogeneousCompletion4M (Fin.last 3) 5) (homogeneousCompletion4M (Fin.last 3) 13)
    homogeneousCompletion4Pair6_14D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair6_14W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair6_14_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair6_14D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair6_14_top :
    homogeneousCompletion4Pair6_14S 13 * homogeneousCompletion4GPoly 13 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair6_14S 13 * homogeneousCompletion4GPoly 13) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_14S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair6_14S 13 := by
  have hL0 : homogeneousCompletion4Pair6_14L = homogeneousExponentSup (homogeneousCompletion4Leading 5) (homogeneousCompletion4Leading 13) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair6_14L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 2, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_14L (homogeneousCompletion4Leading 5) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair6_14L (homogeneousCompletion4Leading 13) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair6_14U =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_14_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair6_14V =
      monomial (homogeneousExponent homogeneousCompletion4Pair6_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair6_14_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair6_14D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair6_14D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair6_14L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair6_14D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair6_14L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair6_14_degree_bounds_check k)
  unfold homogeneousCompletion4Pair6_14S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair6_14D k)) 5 13 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
