/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs04Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs04OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair1_14S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 13
    (rationalSparsePolynomial homogeneousCompletion4Pair1_14U) (rationalSparsePolynomial homogeneousCompletion4Pair1_14V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_14D k))

theorem homogeneousCompletion4Pair1_14_relation : (∑ k, homogeneousCompletion4Pair1_14S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair1_14S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair1_14U homogeneousCompletion4Pair1_14V
    (homogeneousCompletion4G 0) (homogeneousCompletion4G 13) homogeneousCompletion4Pair1_14D homogeneousCompletion4G homogeneousCompletion4Pair1_14_sp_check

theorem homogeneousCompletion4Pair1_14_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair1_14S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair1_14S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair1_14U homogeneousCompletion4Pair1_14V
    (homogeneousCompletion4M (Fin.last 3) 0) (homogeneousCompletion4M (Fin.last 3) 13)
    homogeneousCompletion4Pair1_14D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair1_14W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair1_14_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair1_14D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair1_14_top :
    homogeneousCompletion4Pair1_14S 13 * homogeneousCompletion4GPoly 13 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair1_14S 13 * homogeneousCompletion4GPoly 13) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_14S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_14S 13 := by
  have hL0 : homogeneousCompletion4Pair1_14L = homogeneousExponentSup (homogeneousCompletion4Leading 0) (homogeneousCompletion4Leading 13) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair1_14L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 3, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_14L (homogeneousCompletion4Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_14L (homogeneousCompletion4Leading 13) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair1_14U =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_14_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair1_14V =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_14L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 13)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_14_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair1_14D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair1_14D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair1_14L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair1_14D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair1_14L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair1_14_degree_bounds_check k)
  unfold homogeneousCompletion4Pair1_14S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_14D k)) 0 13 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair1_15S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 14
    (rationalSparsePolynomial homogeneousCompletion4Pair1_15U) (rationalSparsePolynomial homogeneousCompletion4Pair1_15V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_15D k))

theorem homogeneousCompletion4Pair1_15_relation : (∑ k, homogeneousCompletion4Pair1_15S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair1_15S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair1_15U homogeneousCompletion4Pair1_15V
    (homogeneousCompletion4G 0) (homogeneousCompletion4G 14) homogeneousCompletion4Pair1_15D homogeneousCompletion4G homogeneousCompletion4Pair1_15_sp_check

theorem homogeneousCompletion4Pair1_15_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair1_15S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair1_15S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair1_15U homogeneousCompletion4Pair1_15V
    (homogeneousCompletion4M (Fin.last 3) 0) (homogeneousCompletion4M (Fin.last 3) 14)
    homogeneousCompletion4Pair1_15D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair1_15W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair1_15_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair1_15D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair1_15_top :
    homogeneousCompletion4Pair1_15S 14 * homogeneousCompletion4GPoly 14 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair1_15S 14 * homogeneousCompletion4GPoly 14) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_15S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_15S 14 := by
  have hL0 : homogeneousCompletion4Pair1_15L = homogeneousExponentSup (homogeneousCompletion4Leading 0) (homogeneousCompletion4Leading 14) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair1_15L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 4, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_15L (homogeneousCompletion4Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_15L (homogeneousCompletion4Leading 14) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair1_15U =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_15_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair1_15V =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_15L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 14)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_15_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair1_15D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair1_15D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair1_15L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair1_15D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair1_15L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair1_15_degree_bounds_check k)
  unfold homogeneousCompletion4Pair1_15S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_15D k)) 0 14 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair2_3S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 2
    (rationalSparsePolynomial homogeneousCompletion4Pair2_3U) (rationalSparsePolynomial homogeneousCompletion4Pair2_3V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_3D k))

theorem homogeneousCompletion4Pair2_3_relation : (∑ k, homogeneousCompletion4Pair2_3S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair2_3S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair2_3U homogeneousCompletion4Pair2_3V
    (homogeneousCompletion4G 1) (homogeneousCompletion4G 2) homogeneousCompletion4Pair2_3D homogeneousCompletion4G homogeneousCompletion4Pair2_3_sp_check

theorem homogeneousCompletion4Pair2_3_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair2_3S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair2_3S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair2_3U homogeneousCompletion4Pair2_3V
    (homogeneousCompletion4M (Fin.last 3) 1) (homogeneousCompletion4M (Fin.last 3) 2)
    homogeneousCompletion4Pair2_3D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair2_3W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair2_3_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair2_3D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair2_3_top :
    homogeneousCompletion4Pair2_3S 2 * homogeneousCompletion4GPoly 2 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair2_3S 2 * homogeneousCompletion4GPoly 2) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_3S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_3S 2 := by
  have hL0 : homogeneousCompletion4Pair2_3L = homogeneousExponentSup (homogeneousCompletion4Leading 1) (homogeneousCompletion4Leading 2) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair2_3L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_3L (homogeneousCompletion4Leading 1) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_3L (homogeneousCompletion4Leading 2) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair2_3U =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_3_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair2_3V =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_3_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair2_3D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair2_3D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair2_3L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair2_3D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair2_3L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair2_3_degree_bounds_check k)
  unfold homogeneousCompletion4Pair2_3S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_3D k)) 1 2 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair2_4S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 3
    (rationalSparsePolynomial homogeneousCompletion4Pair2_4U) (rationalSparsePolynomial homogeneousCompletion4Pair2_4V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_4D k))

theorem homogeneousCompletion4Pair2_4_relation : (∑ k, homogeneousCompletion4Pair2_4S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair2_4S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair2_4U homogeneousCompletion4Pair2_4V
    (homogeneousCompletion4G 1) (homogeneousCompletion4G 3) homogeneousCompletion4Pair2_4D homogeneousCompletion4G homogeneousCompletion4Pair2_4_sp_check

theorem homogeneousCompletion4Pair2_4_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair2_4S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair2_4S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair2_4U homogeneousCompletion4Pair2_4V
    (homogeneousCompletion4M (Fin.last 3) 1) (homogeneousCompletion4M (Fin.last 3) 3)
    homogeneousCompletion4Pair2_4D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair2_4W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair2_4_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair2_4D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair2_4_top :
    homogeneousCompletion4Pair2_4S 3 * homogeneousCompletion4GPoly 3 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair2_4S 3 * homogeneousCompletion4GPoly 3) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_4S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair2_4S 3 := by
  have hL0 : homogeneousCompletion4Pair2_4L = homogeneousExponentSup (homogeneousCompletion4Leading 1) (homogeneousCompletion4Leading 3) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair2_4L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_4L (homogeneousCompletion4Leading 1) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair2_4L (homogeneousCompletion4Leading 3) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair2_4U =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_4_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair2_4V =
      monomial (homogeneousExponent homogeneousCompletion4Pair2_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair2_4_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair2_4D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair2_4D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair2_4L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair2_4D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair2_4L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair2_4_degree_bounds_check k)
  unfold homogeneousCompletion4Pair2_4S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair2_4D k)) 1 3 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
