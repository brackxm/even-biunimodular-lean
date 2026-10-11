/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3BasisProofs
import Biunimodular.F11.HomogeneousCompletion3Pairs04Checks
import Biunimodular.F11.HomogeneousCompletion3Pairs04OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion3Pair3_5S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 4
    (rationalSparsePolynomial homogeneousCompletion3Pair3_5U) (rationalSparsePolynomial homogeneousCompletion3Pair3_5V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair3_5D k))

theorem homogeneousCompletion3Pair3_5_relation : (∑ k, homogeneousCompletion3Pair3_5S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair3_5S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair3_5U homogeneousCompletion3Pair3_5V
    (homogeneousCompletion3G 2) (homogeneousCompletion3G 4) homogeneousCompletion3Pair3_5D homogeneousCompletion3G homogeneousCompletion3Pair3_5_sp_check

theorem homogeneousCompletion3Pair3_5_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair3_5S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair3_5S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair3_5U homogeneousCompletion3Pair3_5V
    (homogeneousCompletion3M (Fin.last 2) 2) (homogeneousCompletion3M (Fin.last 2) 4)
    homogeneousCompletion3Pair3_5D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair3_5W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair3_5_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair3_5D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair3_5_top :
    homogeneousCompletion3Pair3_5S 4 * homogeneousCompletion3GPoly 4 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair3_5S 4 * homogeneousCompletion3GPoly 4) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair3_5S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair3_5S 4 := by
  have hL0 : homogeneousCompletion3Pair3_5L = homogeneousExponentSup (homogeneousCompletion3Leading 2) (homogeneousCompletion3Leading 4) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair3_5L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair3_5L (homogeneousCompletion3Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair3_5L (homogeneousCompletion3Leading 4) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair3_5U =
      monomial (homogeneousExponent homogeneousCompletion3Pair3_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair3_5_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair3_5V =
      monomial (homogeneousExponent homogeneousCompletion3Pair3_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair3_5_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair3_5D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair3_5D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair3_5L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair3_5D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair3_5L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair3_5_degree_bounds_check k)
  unfold homogeneousCompletion3Pair3_5S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair3_5D k)) 2 4 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair3_6S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 5
    (rationalSparsePolynomial homogeneousCompletion3Pair3_6U) (rationalSparsePolynomial homogeneousCompletion3Pair3_6V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair3_6D k))

theorem homogeneousCompletion3Pair3_6_relation : (∑ k, homogeneousCompletion3Pair3_6S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair3_6S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair3_6U homogeneousCompletion3Pair3_6V
    (homogeneousCompletion3G 2) (homogeneousCompletion3G 5) homogeneousCompletion3Pair3_6D homogeneousCompletion3G homogeneousCompletion3Pair3_6_sp_check

theorem homogeneousCompletion3Pair3_6_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair3_6S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair3_6S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair3_6U homogeneousCompletion3Pair3_6V
    (homogeneousCompletion3M (Fin.last 2) 2) (homogeneousCompletion3M (Fin.last 2) 5)
    homogeneousCompletion3Pair3_6D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair3_6W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair3_6_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair3_6D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair3_6_top :
    homogeneousCompletion3Pair3_6S 5 * homogeneousCompletion3GPoly 5 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair3_6S 5 * homogeneousCompletion3GPoly 5) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 5) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair3_6S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair3_6S 5 := by
  have hL0 : homogeneousCompletion3Pair3_6L = homogeneousExponentSup (homogeneousCompletion3Leading 2) (homogeneousCompletion3Leading 5) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair3_6L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 5) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair3_6L (homogeneousCompletion3Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair3_6L (homogeneousCompletion3Leading 5) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair3_6U =
      monomial (homogeneousExponent homogeneousCompletion3Pair3_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair3_6_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair3_6V =
      monomial (homogeneousExponent homogeneousCompletion3Pair3_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair3_6_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair3_6D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair3_6D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair3_6L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair3_6D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair3_6L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair3_6_degree_bounds_check k)
  unfold homogeneousCompletion3Pair3_6S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair3_6D k)) 2 5 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair3_7S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 6
    (rationalSparsePolynomial homogeneousCompletion3Pair3_7U) (rationalSparsePolynomial homogeneousCompletion3Pair3_7V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair3_7D k))

theorem homogeneousCompletion3Pair3_7_relation : (∑ k, homogeneousCompletion3Pair3_7S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair3_7S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair3_7U homogeneousCompletion3Pair3_7V
    (homogeneousCompletion3G 2) (homogeneousCompletion3G 6) homogeneousCompletion3Pair3_7D homogeneousCompletion3G homogeneousCompletion3Pair3_7_sp_check

theorem homogeneousCompletion3Pair3_7_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair3_7S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair3_7S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair3_7U homogeneousCompletion3Pair3_7V
    (homogeneousCompletion3M (Fin.last 2) 2) (homogeneousCompletion3M (Fin.last 2) 6)
    homogeneousCompletion3Pair3_7D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair3_7W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair3_7_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair3_7D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair3_7_top :
    homogeneousCompletion3Pair3_7S 6 * homogeneousCompletion3GPoly 6 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair3_7S 6 * homogeneousCompletion3GPoly 6) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 6) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair3_7S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair3_7S 6 := by
  have hL0 : homogeneousCompletion3Pair3_7L = homogeneousExponentSup (homogeneousCompletion3Leading 2) (homogeneousCompletion3Leading 6) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair3_7L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 6) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 0, 1, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair3_7L (homogeneousCompletion3Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair3_7L (homogeneousCompletion3Leading 6) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair3_7U =
      monomial (homogeneousExponent homogeneousCompletion3Pair3_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair3_7_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair3_7V =
      monomial (homogeneousExponent homogeneousCompletion3Pair3_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair3_7_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair3_7D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair3_7D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair3_7L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair3_7D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair3_7L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair3_7_degree_bounds_check k)
  unfold homogeneousCompletion3Pair3_7S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair3_7D k)) 2 6 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion3Pair4_5S : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 4
    (rationalSparsePolynomial homogeneousCompletion3Pair4_5U) (rationalSparsePolynomial homogeneousCompletion3Pair4_5V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair4_5D k))

theorem homogeneousCompletion3Pair4_5_relation : (∑ k, homogeneousCompletion3Pair4_5S k * homogeneousCompletion3GPoly k) = 0 := by
  rw [homogeneousCompletion3Pair4_5S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion3Pair4_5U homogeneousCompletion3Pair4_5V
    (homogeneousCompletion3G 3) (homogeneousCompletion3G 4) homogeneousCompletion3Pair4_5D homogeneousCompletion3G homogeneousCompletion3Pair4_5_sp_check

theorem homogeneousCompletion3Pair4_5_last :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3Pair4_5S ∈ homogeneousCompletion3PreviousIdeal := by
  rw [homogeneousCompletion3Pair4_5S, criticalRelationVector_label]
  simp only [homogeneousCompletion3MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion3Pair4_5U homogeneousCompletion3Pair4_5V
    (homogeneousCompletion3M (Fin.last 2) 3) (homogeneousCompletion3M (Fin.last 2) 4)
    homogeneousCompletion3Pair4_5D (homogeneousCompletion3M (Fin.last 2)) homogeneousCompletion3Pair4_5W
    (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc) homogeneousCompletion3Pair4_5_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3Pair4_5D k) *
    rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

theorem homogeneousCompletion3Pair4_5_top :
    homogeneousCompletion3Pair4_5S 4 * homogeneousCompletion3GPoly 4 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion3Pair4_5S 4 * homogeneousCompletion3GPoly 4) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair4_5S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly homogeneousCompletion3Pair4_5S 4 := by
  have hL0 : homogeneousCompletion3Pair4_5L = homogeneousExponentSup (homogeneousCompletion3Leading 3) (homogeneousCompletion3Leading 4) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion3Pair4_5L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion3_basis_degree, homogeneousCompletion3_basis_degree]
  have hU0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair4_5L (homogeneousCompletion3Leading 3) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion3Pair4_5L (homogeneousCompletion3Leading 4) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion3Pair4_5U =
      monomial (homogeneousExponent homogeneousCompletion3Pair4_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair4_5_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion3Pair4_5V =
      monomial (homogeneousExponent homogeneousCompletion3Pair4_5L - homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion3Pair4_5_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion3_basis_degree]
  have hD (k : Fin 7) : rationalSparsePolynomial (homogeneousCompletion3Pair4_5D k) * homogeneousCompletion3GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion3Pair4_5D k) * homogeneousCompletion3GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion3Pair4_5L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion3Pair4_5D k) (homogeneousCompletion3GPoly k)
      (homogeneousCompletion3Leading k) homogeneousCompletion3Pair4_5L (homogeneousCompletion3_basis_nonzero k) (homogeneousCompletion3_basis_degree k)
      (homogeneousCompletion3Pair4_5_degree_bounds_check k)
  unfold homogeneousCompletion3Pair4_5S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion3GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion3Pair4_5D k)) 3 4 (by decide)
    homogeneousCompletion3_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
