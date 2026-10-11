/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs53Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs53OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair10_21S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 20
    (rationalSparsePolynomial homogeneousCompletion5Pair10_21U) (rationalSparsePolynomial homogeneousCompletion5Pair10_21V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_21D k))

theorem homogeneousCompletion5Pair10_21_relation : (∑ k, homogeneousCompletion5Pair10_21S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_21S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_21U homogeneousCompletion5Pair10_21V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 20) homogeneousCompletion5Pair10_21D homogeneousCompletion5G homogeneousCompletion5Pair10_21_sp_check

theorem homogeneousCompletion5Pair10_21_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_21S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_21S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_21U homogeneousCompletion5Pair10_21V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 20)
    homogeneousCompletion5Pair10_21D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_21W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_21_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_21D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_21_top :
    homogeneousCompletion5Pair10_21S 20 * homogeneousCompletion5GPoly 20 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_21S 20 * homogeneousCompletion5GPoly 20) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_21S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_21S 20 := by
  have hL0 : homogeneousCompletion5Pair10_21L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 20) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_21L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_21L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_21L (homogeneousCompletion5Leading 20) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_21U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_21L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_21_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_21V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_21L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_21_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_21D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_21D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_21L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_21D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_21L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_21_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_21S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_21D k)) 9 20 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair10_22S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 21
    (rationalSparsePolynomial homogeneousCompletion5Pair10_22U) (rationalSparsePolynomial homogeneousCompletion5Pair10_22V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_22D k))

theorem homogeneousCompletion5Pair10_22_relation : (∑ k, homogeneousCompletion5Pair10_22S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_22S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_22U homogeneousCompletion5Pair10_22V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 21) homogeneousCompletion5Pair10_22D homogeneousCompletion5G homogeneousCompletion5Pair10_22_sp_check

theorem homogeneousCompletion5Pair10_22_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_22S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_22S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_22U homogeneousCompletion5Pair10_22V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 21)
    homogeneousCompletion5Pair10_22D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_22W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_22_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_22D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_22_top :
    homogeneousCompletion5Pair10_22S 21 * homogeneousCompletion5GPoly 21 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_22S 21 * homogeneousCompletion5GPoly 21) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_22S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_22S 21 := by
  have hL0 : homogeneousCompletion5Pair10_22L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 21) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_22L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_22L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_22L (homogeneousCompletion5Leading 21) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_22U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_22L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_22_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_22V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_22L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_22_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_22D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_22D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_22L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_22D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_22L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_22_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_22S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_22D k)) 9 21 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair10_23S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 22
    (rationalSparsePolynomial homogeneousCompletion5Pair10_23U) (rationalSparsePolynomial homogeneousCompletion5Pair10_23V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_23D k))

theorem homogeneousCompletion5Pair10_23_relation : (∑ k, homogeneousCompletion5Pair10_23S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_23S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_23U homogeneousCompletion5Pair10_23V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 22) homogeneousCompletion5Pair10_23D homogeneousCompletion5G homogeneousCompletion5Pair10_23_sp_check

theorem homogeneousCompletion5Pair10_23_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_23S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_23S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_23U homogeneousCompletion5Pair10_23V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 22)
    homogeneousCompletion5Pair10_23D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_23W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_23_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_23D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_23_top :
    homogeneousCompletion5Pair10_23S 22 * homogeneousCompletion5GPoly 22 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_23S 22 * homogeneousCompletion5GPoly 22) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_23S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_23S 22 := by
  have hL0 : homogeneousCompletion5Pair10_23L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 22) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_23L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_23L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_23L (homogeneousCompletion5Leading 22) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_23U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_23L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_23_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_23V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_23L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_23_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_23D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_23D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_23L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_23D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_23L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_23_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_23S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_23D k)) 9 22 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair10_24S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 9 23
    (rationalSparsePolynomial homogeneousCompletion5Pair10_24U) (rationalSparsePolynomial homogeneousCompletion5Pair10_24V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_24D k))

theorem homogeneousCompletion5Pair10_24_relation : (∑ k, homogeneousCompletion5Pair10_24S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair10_24S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair10_24U homogeneousCompletion5Pair10_24V
    (homogeneousCompletion5G 9) (homogeneousCompletion5G 23) homogeneousCompletion5Pair10_24D homogeneousCompletion5G homogeneousCompletion5Pair10_24_sp_check

theorem homogeneousCompletion5Pair10_24_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair10_24S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair10_24S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair10_24U homogeneousCompletion5Pair10_24V
    (homogeneousCompletion5M (Fin.last 4) 9) (homogeneousCompletion5M (Fin.last 4) 23)
    homogeneousCompletion5Pair10_24D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair10_24W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair10_24_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair10_24D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair10_24_top :
    homogeneousCompletion5Pair10_24S 23 * homogeneousCompletion5GPoly 23 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair10_24S 23 * homogeneousCompletion5GPoly 23) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_24S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair10_24S 23 := by
  have hL0 : homogeneousCompletion5Pair10_24L = homogeneousExponentSup (homogeneousCompletion5Leading 9) (homogeneousCompletion5Leading 23) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair10_24L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 4, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_24L (homogeneousCompletion5Leading 9) := by native_decide
  have hV0 : (⟨0, 0, 1, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair10_24L (homogeneousCompletion5Leading 23) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair10_24U =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_24L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 9)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_24_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair10_24V =
      monomial (homogeneousExponent homogeneousCompletion5Pair10_24L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair10_24_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair10_24D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair10_24D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair10_24L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair10_24D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair10_24L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair10_24_degree_bounds_check k)
  unfold homogeneousCompletion5Pair10_24S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair10_24D k)) 9 23 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
