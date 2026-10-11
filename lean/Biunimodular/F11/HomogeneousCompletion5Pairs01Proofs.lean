/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs01Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs01OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair1_2S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 1
    (rationalSparsePolynomial homogeneousCompletion5Pair1_2U) (rationalSparsePolynomial homogeneousCompletion5Pair1_2V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_2D k))

theorem homogeneousCompletion5Pair1_2_relation : (∑ k, homogeneousCompletion5Pair1_2S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_2S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_2U homogeneousCompletion5Pair1_2V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 1) homogeneousCompletion5Pair1_2D homogeneousCompletion5G homogeneousCompletion5Pair1_2_sp_check

theorem homogeneousCompletion5Pair1_2_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_2S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_2S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_2U homogeneousCompletion5Pair1_2V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 1)
    homogeneousCompletion5Pair1_2D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_2W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_2_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_2D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_2_top :
    homogeneousCompletion5Pair1_2S 1 * homogeneousCompletion5GPoly 1 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_2S 1 * homogeneousCompletion5GPoly 1) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_2S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_2S 1 := by
  have hL0 : homogeneousCompletion5Pair1_2L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 1) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_2L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_2L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_2L (homogeneousCompletion5Leading 1) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_2U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_2L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_2_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_2V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_2L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_2_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_2D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_2D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_2L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_2D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_2L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_2_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_2S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_2D k)) 0 1 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair1_3S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 2
    (rationalSparsePolynomial homogeneousCompletion5Pair1_3U) (rationalSparsePolynomial homogeneousCompletion5Pair1_3V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_3D k))

theorem homogeneousCompletion5Pair1_3_relation : (∑ k, homogeneousCompletion5Pair1_3S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_3S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_3U homogeneousCompletion5Pair1_3V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 2) homogeneousCompletion5Pair1_3D homogeneousCompletion5G homogeneousCompletion5Pair1_3_sp_check

theorem homogeneousCompletion5Pair1_3_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_3S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_3S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_3U homogeneousCompletion5Pair1_3V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 2)
    homogeneousCompletion5Pair1_3D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_3W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_3_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_3D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_3_top :
    homogeneousCompletion5Pair1_3S 2 * homogeneousCompletion5GPoly 2 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_3S 2 * homogeneousCompletion5GPoly 2) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_3S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_3S 2 := by
  have hL0 : homogeneousCompletion5Pair1_3L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 2) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_3L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_3L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_3L (homogeneousCompletion5Leading 2) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_3U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_3_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_3V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_3_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_3D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_3D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_3L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_3D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_3L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_3_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_3S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_3D k)) 0 2 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair1_4S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 3
    (rationalSparsePolynomial homogeneousCompletion5Pair1_4U) (rationalSparsePolynomial homogeneousCompletion5Pair1_4V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_4D k))

theorem homogeneousCompletion5Pair1_4_relation : (∑ k, homogeneousCompletion5Pair1_4S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_4S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_4U homogeneousCompletion5Pair1_4V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 3) homogeneousCompletion5Pair1_4D homogeneousCompletion5G homogeneousCompletion5Pair1_4_sp_check

theorem homogeneousCompletion5Pair1_4_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_4S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_4S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_4U homogeneousCompletion5Pair1_4V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 3)
    homogeneousCompletion5Pair1_4D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_4W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_4_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_4D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_4_top :
    homogeneousCompletion5Pair1_4S 3 * homogeneousCompletion5GPoly 3 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_4S 3 * homogeneousCompletion5GPoly 3) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_4S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_4S 3 := by
  have hL0 : homogeneousCompletion5Pair1_4L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 3) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_4L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_4L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_4L (homogeneousCompletion5Leading 3) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_4U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_4_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_4V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_4_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_4D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_4D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_4L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_4D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_4L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_4_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_4S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_4D k)) 0 3 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair1_5S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 4
    (rationalSparsePolynomial homogeneousCompletion5Pair1_5U) (rationalSparsePolynomial homogeneousCompletion5Pair1_5V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_5D k))

theorem homogeneousCompletion5Pair1_5_relation : (∑ k, homogeneousCompletion5Pair1_5S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_5S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_5U homogeneousCompletion5Pair1_5V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 4) homogeneousCompletion5Pair1_5D homogeneousCompletion5G homogeneousCompletion5Pair1_5_sp_check

theorem homogeneousCompletion5Pair1_5_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_5S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_5S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_5U homogeneousCompletion5Pair1_5V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 4)
    homogeneousCompletion5Pair1_5D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_5W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_5_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_5D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_5_top :
    homogeneousCompletion5Pair1_5S 4 * homogeneousCompletion5GPoly 4 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_5S 4 * homogeneousCompletion5GPoly 4) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_5S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_5S 4 := by
  have hL0 : homogeneousCompletion5Pair1_5L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 4) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_5L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_5L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_5L (homogeneousCompletion5Leading 4) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_5U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_5_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_5V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_5_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_5D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_5D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_5L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_5D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_5L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_5_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_5S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_5D k)) 0 4 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
