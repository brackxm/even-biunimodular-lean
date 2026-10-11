/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3BasisProofs
import Biunimodular.F11.HomogeneousCompletion3Pairs01Checks
import Biunimodular.F11.HomogeneousCompletion3Pairs01OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion3Pair1_2S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 1
    (rationalSparsePolynomial homogeneousCompletion3Pair1_2U) (rationalSparsePolynomial homogeneousCompletion3Pair1_2V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_2D k))

theorem homogeneousCompletion3Pair1_2_relation : (∑ k, homogeneousCompletion3Pair1_2S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair1_2S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair1_2U homogeneousCompletion3Pair1_2V
    (homogeneousCompletion3G 0) (homogeneousCompletion3G 1) homogeneousCompletion3Pair1_2D homogeneousCompletion3G homogeneousCompletion3Pair1_2_sp_check

theorem homogeneousCompletion3Pair1_2_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair1_2S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair1_2S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair1_2U homogeneousCompletion3Pair1_2V
    (homogeneousCompletion3M (Fin.last 2) 0) (homogeneousCompletion3M (Fin.last 2) 1)
    homogeneousCompletion3Pair1_2D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair1_2W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair1_2_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair1_2D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair1_2_top :
    homogeneousCompletion3Pair1_2S 1 * homogeneousCompletion3GPoly 1 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair1_2S 1 * homogeneousCompletion3GPoly 1) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_2S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_2S 1 := by
  have hL0 : homogeneousCompletion3Pair1_2L = homogeneousExponentSup (homogeneousCompletion3Leading 0) (homogeneousCompletion3Leading 1) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair1_2L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_2L (homogeneousCompletion3Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_2L (homogeneousCompletion3Leading 1) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair1_2U =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_2L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_2_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair1_2V =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_2L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_2_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair1_2D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair1_2D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair1_2L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair1_2D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair1_2L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair1_2_degree_bounds_check k)
  unfold homogeneousCompletion3Pair1_2S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_2D k)) 0 1 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair1_3S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 2
    (rationalSparsePolynomial homogeneousCompletion3Pair1_3U) (rationalSparsePolynomial homogeneousCompletion3Pair1_3V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_3D k))

theorem homogeneousCompletion3Pair1_3_relation : (∑ k, homogeneousCompletion3Pair1_3S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair1_3S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair1_3U homogeneousCompletion3Pair1_3V
    (homogeneousCompletion3G 0) (homogeneousCompletion3G 2) homogeneousCompletion3Pair1_3D homogeneousCompletion3G homogeneousCompletion3Pair1_3_sp_check

theorem homogeneousCompletion3Pair1_3_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair1_3S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair1_3S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair1_3U homogeneousCompletion3Pair1_3V
    (homogeneousCompletion3M (Fin.last 2) 0) (homogeneousCompletion3M (Fin.last 2) 2)
    homogeneousCompletion3Pair1_3D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair1_3W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair1_3_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair1_3D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair1_3_top :
    homogeneousCompletion3Pair1_3S 2 * homogeneousCompletion3GPoly 2 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair1_3S 2 * homogeneousCompletion3GPoly 2) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_3S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_3S 2 := by
  have hL0 : homogeneousCompletion3Pair1_3L = homogeneousExponentSup (homogeneousCompletion3Leading 0) (homogeneousCompletion3Leading 2) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair1_3L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_3L (homogeneousCompletion3Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_3L (homogeneousCompletion3Leading 2) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair1_3U =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_3_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair1_3V =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_3_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair1_3D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair1_3D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair1_3L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair1_3D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair1_3L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair1_3_degree_bounds_check k)
  unfold homogeneousCompletion3Pair1_3S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_3D k)) 0 2 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair1_4S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 3
    (rationalSparsePolynomial homogeneousCompletion3Pair1_4U) (rationalSparsePolynomial homogeneousCompletion3Pair1_4V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_4D k))

theorem homogeneousCompletion3Pair1_4_relation : (∑ k, homogeneousCompletion3Pair1_4S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair1_4S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair1_4U homogeneousCompletion3Pair1_4V
    (homogeneousCompletion3G 0) (homogeneousCompletion3G 3) homogeneousCompletion3Pair1_4D homogeneousCompletion3G homogeneousCompletion3Pair1_4_sp_check

theorem homogeneousCompletion3Pair1_4_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair1_4S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair1_4S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair1_4U homogeneousCompletion3Pair1_4V
    (homogeneousCompletion3M (Fin.last 2) 0) (homogeneousCompletion3M (Fin.last 2) 3)
    homogeneousCompletion3Pair1_4D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair1_4W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair1_4_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair1_4D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair1_4_top :
    homogeneousCompletion3Pair1_4S 3 * homogeneousCompletion3GPoly 3 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair1_4S 3 * homogeneousCompletion3GPoly 3) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_4S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_4S 3 := by
  have hL0 : homogeneousCompletion3Pair1_4L = homogeneousExponentSup (homogeneousCompletion3Leading 0) (homogeneousCompletion3Leading 3) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair1_4L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_4L (homogeneousCompletion3Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_4L (homogeneousCompletion3Leading 3) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair1_4U =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_4_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair1_4V =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_4_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair1_4D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair1_4D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair1_4L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair1_4D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair1_4L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair1_4_degree_bounds_check k)
  unfold homogeneousCompletion3Pair1_4S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_4D k)) 0 3 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair1_5S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 4
    (rationalSparsePolynomial homogeneousCompletion3Pair1_5U) (rationalSparsePolynomial homogeneousCompletion3Pair1_5V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_5D k))

theorem homogeneousCompletion3Pair1_5_relation : (∑ k, homogeneousCompletion3Pair1_5S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair1_5S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair1_5U homogeneousCompletion3Pair1_5V
    (homogeneousCompletion3G 0) (homogeneousCompletion3G 4) homogeneousCompletion3Pair1_5D homogeneousCompletion3G homogeneousCompletion3Pair1_5_sp_check

theorem homogeneousCompletion3Pair1_5_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair1_5S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair1_5S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair1_5U homogeneousCompletion3Pair1_5V
    (homogeneousCompletion3M (Fin.last 2) 0) (homogeneousCompletion3M (Fin.last 2) 4)
    homogeneousCompletion3Pair1_5D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair1_5W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair1_5_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair1_5D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair1_5_top :
    homogeneousCompletion3Pair1_5S 4 * homogeneousCompletion3GPoly 4 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair1_5S 4 * homogeneousCompletion3GPoly 4) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_5S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_5S 4 := by
  have hL0 : homogeneousCompletion3Pair1_5L = homogeneousExponentSup (homogeneousCompletion3Leading 0) (homogeneousCompletion3Leading 4) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair1_5L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 1, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_5L (homogeneousCompletion3Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_5L (homogeneousCompletion3Leading 4) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair1_5U =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_5_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair1_5V =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_5_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair1_5D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair1_5D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair1_5L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair1_5D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair1_5L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair1_5_degree_bounds_check k)
  unfold homogeneousCompletion3Pair1_5S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_5D k)) 0 4 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
