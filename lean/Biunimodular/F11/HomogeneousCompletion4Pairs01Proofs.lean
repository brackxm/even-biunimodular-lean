/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisProofs
import Biunimodular.F11.HomogeneousCompletion4Pairs01Checks
import Biunimodular.F11.HomogeneousCompletion4Pairs01OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion4Pair1_2S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 1
    (rationalSparsePolynomial homogeneousCompletion4Pair1_2U) (rationalSparsePolynomial homogeneousCompletion4Pair1_2V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_2D k))

theorem homogeneousCompletion4Pair1_2_relation : (∑ k, homogeneousCompletion4Pair1_2S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair1_2S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair1_2U homogeneousCompletion4Pair1_2V
    (homogeneousCompletion4G 0) (homogeneousCompletion4G 1) homogeneousCompletion4Pair1_2D homogeneousCompletion4G homogeneousCompletion4Pair1_2_sp_check

theorem homogeneousCompletion4Pair1_2_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair1_2S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair1_2S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair1_2U homogeneousCompletion4Pair1_2V
    (homogeneousCompletion4M (Fin.last 3) 0) (homogeneousCompletion4M (Fin.last 3) 1)
    homogeneousCompletion4Pair1_2D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair1_2W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair1_2_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair1_2D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair1_2_top :
    homogeneousCompletion4Pair1_2S 1 * homogeneousCompletion4GPoly 1 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair1_2S 1 * homogeneousCompletion4GPoly 1) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_2S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_2S 1 := by
  have hL0 : homogeneousCompletion4Pair1_2L = homogeneousExponentSup (homogeneousCompletion4Leading 0) (homogeneousCompletion4Leading 1) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair1_2L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_2L (homogeneousCompletion4Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_2L (homogeneousCompletion4Leading 1) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair1_2U =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_2L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_2_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair1_2V =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_2L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_2_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair1_2D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair1_2D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair1_2L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair1_2D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair1_2L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair1_2_degree_bounds_check k)
  unfold homogeneousCompletion4Pair1_2S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_2D k)) 0 1 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair1_3S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 2
    (rationalSparsePolynomial homogeneousCompletion4Pair1_3U) (rationalSparsePolynomial homogeneousCompletion4Pair1_3V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_3D k))

theorem homogeneousCompletion4Pair1_3_relation : (∑ k, homogeneousCompletion4Pair1_3S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair1_3S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair1_3U homogeneousCompletion4Pair1_3V
    (homogeneousCompletion4G 0) (homogeneousCompletion4G 2) homogeneousCompletion4Pair1_3D homogeneousCompletion4G homogeneousCompletion4Pair1_3_sp_check

theorem homogeneousCompletion4Pair1_3_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair1_3S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair1_3S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair1_3U homogeneousCompletion4Pair1_3V
    (homogeneousCompletion4M (Fin.last 3) 0) (homogeneousCompletion4M (Fin.last 3) 2)
    homogeneousCompletion4Pair1_3D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair1_3W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair1_3_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair1_3D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair1_3_top :
    homogeneousCompletion4Pair1_3S 2 * homogeneousCompletion4GPoly 2 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair1_3S 2 * homogeneousCompletion4GPoly 2) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_3S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_3S 2 := by
  have hL0 : homogeneousCompletion4Pair1_3L = homogeneousExponentSup (homogeneousCompletion4Leading 0) (homogeneousCompletion4Leading 2) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair1_3L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_3L (homogeneousCompletion4Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_3L (homogeneousCompletion4Leading 2) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair1_3U =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_3_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair1_3V =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_3_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair1_3D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair1_3D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair1_3L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair1_3D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair1_3L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair1_3_degree_bounds_check k)
  unfold homogeneousCompletion4Pair1_3S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_3D k)) 0 2 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair1_4S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 3
    (rationalSparsePolynomial homogeneousCompletion4Pair1_4U) (rationalSparsePolynomial homogeneousCompletion4Pair1_4V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_4D k))

theorem homogeneousCompletion4Pair1_4_relation : (∑ k, homogeneousCompletion4Pair1_4S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair1_4S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair1_4U homogeneousCompletion4Pair1_4V
    (homogeneousCompletion4G 0) (homogeneousCompletion4G 3) homogeneousCompletion4Pair1_4D homogeneousCompletion4G homogeneousCompletion4Pair1_4_sp_check

theorem homogeneousCompletion4Pair1_4_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair1_4S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair1_4S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair1_4U homogeneousCompletion4Pair1_4V
    (homogeneousCompletion4M (Fin.last 3) 0) (homogeneousCompletion4M (Fin.last 3) 3)
    homogeneousCompletion4Pair1_4D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair1_4W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair1_4_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair1_4D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair1_4_top :
    homogeneousCompletion4Pair1_4S 3 * homogeneousCompletion4GPoly 3 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair1_4S 3 * homogeneousCompletion4GPoly 3) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_4S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_4S 3 := by
  have hL0 : homogeneousCompletion4Pair1_4L = homogeneousExponentSup (homogeneousCompletion4Leading 0) (homogeneousCompletion4Leading 3) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair1_4L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_4L (homogeneousCompletion4Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_4L (homogeneousCompletion4Leading 3) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair1_4U =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_4_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair1_4V =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_4_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair1_4D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair1_4D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair1_4L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair1_4D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair1_4L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair1_4_degree_bounds_check k)
  unfold homogeneousCompletion4Pair1_4S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_4D k)) 0 3 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion4Pair1_5S : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 4
    (rationalSparsePolynomial homogeneousCompletion4Pair1_5U) (rationalSparsePolynomial homogeneousCompletion4Pair1_5V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_5D k))

theorem homogeneousCompletion4Pair1_5_relation : (∑ k, homogeneousCompletion4Pair1_5S k * homogeneousCompletion4GPoly k) = 0 := by
  rw [homogeneousCompletion4Pair1_5S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion4Pair1_5U homogeneousCompletion4Pair1_5V
    (homogeneousCompletion4G 0) (homogeneousCompletion4G 4) homogeneousCompletion4Pair1_5D homogeneousCompletion4G homogeneousCompletion4Pair1_5_sp_check

theorem homogeneousCompletion4Pair1_5_last :
    relationLabelMap (homogeneousCompletion4MPoly (Fin.last 3)) homogeneousCompletion4Pair1_5S ∈ homogeneousCompletion4PreviousIdeal := by
  rw [homogeneousCompletion4Pair1_5S, criticalRelationVector_label]
  simp only [homogeneousCompletion4MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion4Pair1_5U homogeneousCompletion4Pair1_5V
    (homogeneousCompletion4M (Fin.last 3) 0) (homogeneousCompletion4M (Fin.last 3) 4)
    homogeneousCompletion4Pair1_5D (homogeneousCompletion4M (Fin.last 3)) homogeneousCompletion4Pair1_5W
    (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc) homogeneousCompletion4Pair1_5_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4Pair1_5D k) *
    rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

theorem homogeneousCompletion4Pair1_5_top :
    homogeneousCompletion4Pair1_5S 4 * homogeneousCompletion4GPoly 4 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion4Pair1_5S 4 * homogeneousCompletion4GPoly 4) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_5S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion4GPoly homogeneousCompletion4Pair1_5S 4 := by
  have hL0 : homogeneousCompletion4Pair1_5L = homogeneousExponentSup (homogeneousCompletion4Leading 0) (homogeneousCompletion4Leading 4) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion4Pair1_5L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion4_basis_degree, homogeneousCompletion4_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_5L (homogeneousCompletion4Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion4Pair1_5L (homogeneousCompletion4Leading 4) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion4Pair1_5U =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_5_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion4Pair1_5V =
      monomial (homogeneousExponent homogeneousCompletion4Pair1_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion4Pair1_5_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion4_basis_degree]
  have hD (k : Fin 15) : rationalSparsePolynomial (homogeneousCompletion4Pair1_5D k) * homogeneousCompletion4GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion4Pair1_5D k) * homogeneousCompletion4GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion4Pair1_5L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion4Pair1_5D k) (homogeneousCompletion4GPoly k)
      (homogeneousCompletion4Leading k) homogeneousCompletion4Pair1_5L (homogeneousCompletion4_basis_nonzero k) (homogeneousCompletion4_basis_degree k)
      (homogeneousCompletion4Pair1_5_degree_bounds_check k)
  unfold homogeneousCompletion4Pair1_5S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion4GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion4Pair1_5D k)) 0 4 (by decide)
    homogeneousCompletion4_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
