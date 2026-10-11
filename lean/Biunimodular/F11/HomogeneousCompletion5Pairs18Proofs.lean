/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs18Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs18OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair3_21S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 20
    (rationalSparsePolynomial homogeneousCompletion5Pair3_21U) (rationalSparsePolynomial homogeneousCompletion5Pair3_21V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_21D k))

theorem homogeneousCompletion5Pair3_21_relation : (∑ k, homogeneousCompletion5Pair3_21S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair3_21S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair3_21U homogeneousCompletion5Pair3_21V
    (homogeneousCompletion5G 2) (homogeneousCompletion5G 20) homogeneousCompletion5Pair3_21D homogeneousCompletion5G homogeneousCompletion5Pair3_21_sp_check

theorem homogeneousCompletion5Pair3_21_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair3_21S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair3_21S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair3_21U homogeneousCompletion5Pair3_21V
    (homogeneousCompletion5M (Fin.last 4) 2) (homogeneousCompletion5M (Fin.last 4) 20)
    homogeneousCompletion5Pair3_21D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair3_21W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair3_21_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair3_21D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair3_21_top :
    homogeneousCompletion5Pair3_21S 20 * homogeneousCompletion5GPoly 20 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair3_21S 20 * homogeneousCompletion5GPoly 20) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_21S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_21S 20 := by
  have hL0 : homogeneousCompletion5Pair3_21L = homogeneousExponentSup (homogeneousCompletion5Leading 2) (homogeneousCompletion5Leading 20) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair3_21L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_21L (homogeneousCompletion5Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_21L (homogeneousCompletion5Leading 20) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair3_21U =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_21L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_21_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair3_21V =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_21L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_21_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair3_21D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair3_21D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair3_21L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair3_21D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair3_21L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair3_21_degree_bounds_check k)
  unfold homogeneousCompletion5Pair3_21S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_21D k)) 2 20 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair3_22S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 21
    (rationalSparsePolynomial homogeneousCompletion5Pair3_22U) (rationalSparsePolynomial homogeneousCompletion5Pair3_22V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_22D k))

theorem homogeneousCompletion5Pair3_22_relation : (∑ k, homogeneousCompletion5Pair3_22S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair3_22S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair3_22U homogeneousCompletion5Pair3_22V
    (homogeneousCompletion5G 2) (homogeneousCompletion5G 21) homogeneousCompletion5Pair3_22D homogeneousCompletion5G homogeneousCompletion5Pair3_22_sp_check

theorem homogeneousCompletion5Pair3_22_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair3_22S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair3_22S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair3_22U homogeneousCompletion5Pair3_22V
    (homogeneousCompletion5M (Fin.last 4) 2) (homogeneousCompletion5M (Fin.last 4) 21)
    homogeneousCompletion5Pair3_22D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair3_22W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair3_22_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair3_22D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair3_22_top :
    homogeneousCompletion5Pair3_22S 21 * homogeneousCompletion5GPoly 21 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair3_22S 21 * homogeneousCompletion5GPoly 21) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_22S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_22S 21 := by
  have hL0 : homogeneousCompletion5Pair3_22L = homogeneousExponentSup (homogeneousCompletion5Leading 2) (homogeneousCompletion5Leading 21) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair3_22L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 3, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_22L (homogeneousCompletion5Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_22L (homogeneousCompletion5Leading 21) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair3_22U =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_22L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_22_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair3_22V =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_22L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_22_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair3_22D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair3_22D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair3_22L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair3_22D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair3_22L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair3_22_degree_bounds_check k)
  unfold homogeneousCompletion5Pair3_22S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_22D k)) 2 21 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair3_23S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 22
    (rationalSparsePolynomial homogeneousCompletion5Pair3_23U) (rationalSparsePolynomial homogeneousCompletion5Pair3_23V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_23D k))

theorem homogeneousCompletion5Pair3_23_relation : (∑ k, homogeneousCompletion5Pair3_23S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair3_23S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair3_23U homogeneousCompletion5Pair3_23V
    (homogeneousCompletion5G 2) (homogeneousCompletion5G 22) homogeneousCompletion5Pair3_23D homogeneousCompletion5G homogeneousCompletion5Pair3_23_sp_check

theorem homogeneousCompletion5Pair3_23_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair3_23S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair3_23S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair3_23U homogeneousCompletion5Pair3_23V
    (homogeneousCompletion5M (Fin.last 4) 2) (homogeneousCompletion5M (Fin.last 4) 22)
    homogeneousCompletion5Pair3_23D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair3_23W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair3_23_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair3_23D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair3_23_top :
    homogeneousCompletion5Pair3_23S 22 * homogeneousCompletion5GPoly 22 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair3_23S 22 * homogeneousCompletion5GPoly 22) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_23S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_23S 22 := by
  have hL0 : homogeneousCompletion5Pair3_23L = homogeneousExponentSup (homogeneousCompletion5Leading 2) (homogeneousCompletion5Leading 22) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair3_23L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_23L (homogeneousCompletion5Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_23L (homogeneousCompletion5Leading 22) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair3_23U =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_23L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_23_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair3_23V =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_23L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_23_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair3_23D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair3_23D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair3_23L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair3_23D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair3_23L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair3_23_degree_bounds_check k)
  unfold homogeneousCompletion5Pair3_23S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_23D k)) 2 22 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair3_24S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 2 23
    (rationalSparsePolynomial homogeneousCompletion5Pair3_24U) (rationalSparsePolynomial homogeneousCompletion5Pair3_24V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_24D k))

theorem homogeneousCompletion5Pair3_24_relation : (∑ k, homogeneousCompletion5Pair3_24S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair3_24S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair3_24U homogeneousCompletion5Pair3_24V
    (homogeneousCompletion5G 2) (homogeneousCompletion5G 23) homogeneousCompletion5Pair3_24D homogeneousCompletion5G homogeneousCompletion5Pair3_24_sp_check

theorem homogeneousCompletion5Pair3_24_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair3_24S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair3_24S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair3_24U homogeneousCompletion5Pair3_24V
    (homogeneousCompletion5M (Fin.last 4) 2) (homogeneousCompletion5M (Fin.last 4) 23)
    homogeneousCompletion5Pair3_24D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair3_24W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair3_24_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair3_24D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair3_24_top :
    homogeneousCompletion5Pair3_24S 23 * homogeneousCompletion5GPoly 23 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair3_24S 23 * homogeneousCompletion5GPoly 23) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_24S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair3_24S 23 := by
  have hL0 : homogeneousCompletion5Pair3_24L = homogeneousExponentSup (homogeneousCompletion5Leading 2) (homogeneousCompletion5Leading 23) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair3_24L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_24L (homogeneousCompletion5Leading 2) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair3_24L (homogeneousCompletion5Leading 23) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair3_24U =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_24L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_24_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair3_24V =
      monomial (homogeneousExponent homogeneousCompletion5Pair3_24L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair3_24_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair3_24D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair3_24D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair3_24L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair3_24D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair3_24L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair3_24_degree_bounds_check k)
  unfold homogeneousCompletion5Pair3_24S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair3_24D k)) 2 23 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
