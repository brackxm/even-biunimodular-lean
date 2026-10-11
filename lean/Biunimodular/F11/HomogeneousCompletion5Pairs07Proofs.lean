/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs07Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs07OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair1_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 25
    (rationalSparsePolynomial homogeneousCompletion5Pair1_26U) (rationalSparsePolynomial homogeneousCompletion5Pair1_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_26D k))

theorem homogeneousCompletion5Pair1_26_relation : (∑ k, homogeneousCompletion5Pair1_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_26U homogeneousCompletion5Pair1_26V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 25) homogeneousCompletion5Pair1_26D homogeneousCompletion5G homogeneousCompletion5Pair1_26_sp_check

theorem homogeneousCompletion5Pair1_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_26U homogeneousCompletion5Pair1_26V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair1_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_26_top :
    homogeneousCompletion5Pair1_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_26S 25 := by
  have hL0 : homogeneousCompletion5Pair1_26L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 5, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_26L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_26D k)) 0 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair1_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 26
    (rationalSparsePolynomial homogeneousCompletion5Pair1_27U) (rationalSparsePolynomial homogeneousCompletion5Pair1_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_27D k))

theorem homogeneousCompletion5Pair1_27_relation : (∑ k, homogeneousCompletion5Pair1_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair1_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair1_27U homogeneousCompletion5Pair1_27V
    (homogeneousCompletion5G 0) (homogeneousCompletion5G 26) homogeneousCompletion5Pair1_27D homogeneousCompletion5G homogeneousCompletion5Pair1_27_sp_check

theorem homogeneousCompletion5Pair1_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair1_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair1_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair1_27U homogeneousCompletion5Pair1_27V
    (homogeneousCompletion5M (Fin.last 4) 0) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair1_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair1_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair1_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair1_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair1_27_top :
    homogeneousCompletion5Pair1_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair1_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair1_27S 26 := by
  have hL0 : homogeneousCompletion5Pair1_27L = homogeneousExponentSup (homogeneousCompletion5Leading 0) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair1_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 5, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_27L (homogeneousCompletion5Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair1_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair1_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair1_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair1_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair1_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair1_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair1_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair1_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair1_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair1_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair1_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair1_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair1_27D k)) 0 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair2_3S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 2
    (rationalSparsePolynomial homogeneousCompletion5Pair2_3U) (rationalSparsePolynomial homogeneousCompletion5Pair2_3V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_3D k))

theorem homogeneousCompletion5Pair2_3_relation : (∑ k, homogeneousCompletion5Pair2_3S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair2_3S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair2_3U homogeneousCompletion5Pair2_3V
    (homogeneousCompletion5G 1) (homogeneousCompletion5G 2) homogeneousCompletion5Pair2_3D homogeneousCompletion5G homogeneousCompletion5Pair2_3_sp_check

theorem homogeneousCompletion5Pair2_3_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair2_3S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair2_3S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair2_3U homogeneousCompletion5Pair2_3V
    (homogeneousCompletion5M (Fin.last 4) 1) (homogeneousCompletion5M (Fin.last 4) 2)
    homogeneousCompletion5Pair2_3D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair2_3W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair2_3_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair2_3D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair2_3_top :
    homogeneousCompletion5Pair2_3S 2 * homogeneousCompletion5GPoly 2 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair2_3S 2 * homogeneousCompletion5GPoly 2) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_3S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_3S 2 := by
  have hL0 : homogeneousCompletion5Pair2_3L = homogeneousExponentSup (homogeneousCompletion5Leading 1) (homogeneousCompletion5Leading 2) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair2_3L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_3L (homogeneousCompletion5Leading 1) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_3L (homogeneousCompletion5Leading 2) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair2_3U =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_3_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair2_3V =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_3_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair2_3D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair2_3D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair2_3L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair2_3D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair2_3L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair2_3_degree_bounds_check k)
  unfold homogeneousCompletion5Pair2_3S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_3D k)) 1 2 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair2_4S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 3
    (rationalSparsePolynomial homogeneousCompletion5Pair2_4U) (rationalSparsePolynomial homogeneousCompletion5Pair2_4V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_4D k))

theorem homogeneousCompletion5Pair2_4_relation : (∑ k, homogeneousCompletion5Pair2_4S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair2_4S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair2_4U homogeneousCompletion5Pair2_4V
    (homogeneousCompletion5G 1) (homogeneousCompletion5G 3) homogeneousCompletion5Pair2_4D homogeneousCompletion5G homogeneousCompletion5Pair2_4_sp_check

theorem homogeneousCompletion5Pair2_4_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair2_4S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair2_4S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair2_4U homogeneousCompletion5Pair2_4V
    (homogeneousCompletion5M (Fin.last 4) 1) (homogeneousCompletion5M (Fin.last 4) 3)
    homogeneousCompletion5Pair2_4D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair2_4W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair2_4_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair2_4D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair2_4_top :
    homogeneousCompletion5Pair2_4S 3 * homogeneousCompletion5GPoly 3 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair2_4S 3 * homogeneousCompletion5GPoly 3) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_4S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair2_4S 3 := by
  have hL0 : homogeneousCompletion5Pair2_4L = homogeneousExponentSup (homogeneousCompletion5Leading 1) (homogeneousCompletion5Leading 3) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair2_4L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_4L (homogeneousCompletion5Leading 1) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair2_4L (homogeneousCompletion5Leading 3) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair2_4U =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_4_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair2_4V =
      monomial (homogeneousExponent homogeneousCompletion5Pair2_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair2_4_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair2_4D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair2_4D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair2_4L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair2_4D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair2_4L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair2_4_degree_bounds_check k)
  unfold homogeneousCompletion5Pair2_4S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair2_4D k)) 1 3 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
