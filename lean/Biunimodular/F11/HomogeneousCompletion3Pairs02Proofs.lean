/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3BasisProofs
import Biunimodular.F11.HomogeneousCompletion3Pairs02Checks
import Biunimodular.F11.HomogeneousCompletion3Pairs02OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion3Pair1_6S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 5
    (rationalSparsePolynomial homogeneousCompletion3Pair1_6U) (rationalSparsePolynomial homogeneousCompletion3Pair1_6V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_6D k))

theorem homogeneousCompletion3Pair1_6_relation : (∑ k, homogeneousCompletion3Pair1_6S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair1_6S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair1_6U homogeneousCompletion3Pair1_6V
    (homogeneousCompletion3G 0) (homogeneousCompletion3G 5) homogeneousCompletion3Pair1_6D homogeneousCompletion3G homogeneousCompletion3Pair1_6_sp_check

theorem homogeneousCompletion3Pair1_6_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair1_6S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair1_6S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair1_6U homogeneousCompletion3Pair1_6V
    (homogeneousCompletion3M (Fin.last 2) 0) (homogeneousCompletion3M (Fin.last 2) 5)
    homogeneousCompletion3Pair1_6D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair1_6W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair1_6_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair1_6D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair1_6_top :
    homogeneousCompletion3Pair1_6S 5 * homogeneousCompletion3GPoly 5 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair1_6S 5 * homogeneousCompletion3GPoly 5) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 5) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_6S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_6S 5 := by
  have hL0 : homogeneousCompletion3Pair1_6L = homogeneousExponentSup (homogeneousCompletion3Leading 0) (homogeneousCompletion3Leading 5) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair1_6L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 5) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 1, 1, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_6L (homogeneousCompletion3Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_6L (homogeneousCompletion3Leading 5) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair1_6U =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_6_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair1_6V =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_6_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair1_6D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair1_6D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair1_6L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair1_6D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair1_6L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair1_6_degree_bounds_check k)
  unfold homogeneousCompletion3Pair1_6S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_6D k)) 0 5 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair1_7S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 6
    (rationalSparsePolynomial homogeneousCompletion3Pair1_7U) (rationalSparsePolynomial homogeneousCompletion3Pair1_7V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_7D k))

theorem homogeneousCompletion3Pair1_7_relation : (∑ k, homogeneousCompletion3Pair1_7S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair1_7S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair1_7U homogeneousCompletion3Pair1_7V
    (homogeneousCompletion3G 0) (homogeneousCompletion3G 6) homogeneousCompletion3Pair1_7D homogeneousCompletion3G homogeneousCompletion3Pair1_7_sp_check

theorem homogeneousCompletion3Pair1_7_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair1_7S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair1_7S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair1_7U homogeneousCompletion3Pair1_7V
    (homogeneousCompletion3M (Fin.last 2) 0) (homogeneousCompletion3M (Fin.last 2) 6)
    homogeneousCompletion3Pair1_7D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair1_7W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair1_7_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair1_7D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair1_7_top :
    homogeneousCompletion3Pair1_7S 6 * homogeneousCompletion3GPoly 6 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair1_7S 6 * homogeneousCompletion3GPoly 6) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 6) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_7S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair1_7S 6 := by
  have hL0 : homogeneousCompletion3Pair1_7L = homogeneousExponentSup (homogeneousCompletion3Leading 0) (homogeneousCompletion3Leading 6) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair1_7L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 6) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 0, 2, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_7L (homogeneousCompletion3Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair1_7L (homogeneousCompletion3Leading 6) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair1_7U =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_7_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair1_7V =
      monomial (homogeneousExponent homogeneousCompletion3Pair1_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair1_7_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair1_7D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair1_7D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair1_7L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair1_7D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair1_7L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair1_7_degree_bounds_check k)
  unfold homogeneousCompletion3Pair1_7S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair1_7D k)) 0 6 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair2_3S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 2
    (rationalSparsePolynomial homogeneousCompletion3Pair2_3U) (rationalSparsePolynomial homogeneousCompletion3Pair2_3V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair2_3D k))

theorem homogeneousCompletion3Pair2_3_relation : (∑ k, homogeneousCompletion3Pair2_3S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair2_3S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair2_3U homogeneousCompletion3Pair2_3V
    (homogeneousCompletion3G 1) (homogeneousCompletion3G 2) homogeneousCompletion3Pair2_3D homogeneousCompletion3G homogeneousCompletion3Pair2_3_sp_check

theorem homogeneousCompletion3Pair2_3_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair2_3S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair2_3S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair2_3U homogeneousCompletion3Pair2_3V
    (homogeneousCompletion3M (Fin.last 2) 1) (homogeneousCompletion3M (Fin.last 2) 2)
    homogeneousCompletion3Pair2_3D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair2_3W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair2_3_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair2_3D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair2_3_top :
    homogeneousCompletion3Pair2_3S 2 * homogeneousCompletion3GPoly 2 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair2_3S 2 * homogeneousCompletion3GPoly 2) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair2_3S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair2_3S 2 := by
  have hL0 : homogeneousCompletion3Pair2_3L = homogeneousExponentSup (homogeneousCompletion3Leading 1) (homogeneousCompletion3Leading 2) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair2_3L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair2_3L (homogeneousCompletion3Leading 1) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair2_3L (homogeneousCompletion3Leading 2) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair2_3U =
      monomial (homogeneousExponent homogeneousCompletion3Pair2_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair2_3_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair2_3V =
      monomial (homogeneousExponent homogeneousCompletion3Pair2_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair2_3_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair2_3D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair2_3D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair2_3L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair2_3D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair2_3L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair2_3_degree_bounds_check k)
  unfold homogeneousCompletion3Pair2_3S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair2_3D k)) 1 2 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair2_4S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 3
    (rationalSparsePolynomial homogeneousCompletion3Pair2_4U) (rationalSparsePolynomial homogeneousCompletion3Pair2_4V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair2_4D k))

theorem homogeneousCompletion3Pair2_4_relation : (∑ k, homogeneousCompletion3Pair2_4S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair2_4S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair2_4U homogeneousCompletion3Pair2_4V
    (homogeneousCompletion3G 1) (homogeneousCompletion3G 3) homogeneousCompletion3Pair2_4D homogeneousCompletion3G homogeneousCompletion3Pair2_4_sp_check

theorem homogeneousCompletion3Pair2_4_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair2_4S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair2_4S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair2_4U homogeneousCompletion3Pair2_4V
    (homogeneousCompletion3M (Fin.last 2) 1) (homogeneousCompletion3M (Fin.last 2) 3)
    homogeneousCompletion3Pair2_4D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair2_4W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair2_4_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair2_4D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair2_4_top :
    homogeneousCompletion3Pair2_4S 3 * homogeneousCompletion3GPoly 3 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair2_4S 3 * homogeneousCompletion3GPoly 3) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair2_4S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair2_4S 3 := by
  have hL0 : homogeneousCompletion3Pair2_4L = homogeneousExponentSup (homogeneousCompletion3Leading 1) (homogeneousCompletion3Leading 3) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair2_4L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair2_4L (homogeneousCompletion3Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair2_4L (homogeneousCompletion3Leading 3) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair2_4U =
      monomial (homogeneousExponent homogeneousCompletion3Pair2_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair2_4_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair2_4V =
      monomial (homogeneousExponent homogeneousCompletion3Pair2_4L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair2_4_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair2_4D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair2_4D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair2_4L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair2_4D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair2_4L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair2_4_degree_bounds_check k)
  unfold homogeneousCompletion3Pair2_4S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair2_4D k)) 1 3 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
