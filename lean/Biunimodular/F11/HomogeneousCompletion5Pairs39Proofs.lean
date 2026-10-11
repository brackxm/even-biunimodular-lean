/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs39Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs39OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair7_19S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 18
    (rationalSparsePolynomial homogeneousCompletion5Pair7_19U) (rationalSparsePolynomial homogeneousCompletion5Pair7_19V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_19D k))

theorem homogeneousCompletion5Pair7_19_relation : (∑ k, homogeneousCompletion5Pair7_19S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_19S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_19U homogeneousCompletion5Pair7_19V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 18) homogeneousCompletion5Pair7_19D homogeneousCompletion5G homogeneousCompletion5Pair7_19_sp_check

theorem homogeneousCompletion5Pair7_19_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_19S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_19S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_19U homogeneousCompletion5Pair7_19V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 18)
    homogeneousCompletion5Pair7_19D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_19W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_19_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_19D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_19_top :
    homogeneousCompletion5Pair7_19S 18 * homogeneousCompletion5GPoly 18 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_19S 18 * homogeneousCompletion5GPoly 18) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_19S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_19S 18 := by
  have hL0 : homogeneousCompletion5Pair7_19L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 18) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_19L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_19L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_19L (homogeneousCompletion5Leading 18) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_19U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_19L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_19_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_19V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_19L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_19_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_19D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_19D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_19L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_19D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_19L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_19_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_19S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_19D k)) 6 18 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_20S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 19
    (rationalSparsePolynomial homogeneousCompletion5Pair7_20U) (rationalSparsePolynomial homogeneousCompletion5Pair7_20V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_20D k))

theorem homogeneousCompletion5Pair7_20_relation : (∑ k, homogeneousCompletion5Pair7_20S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_20S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_20U homogeneousCompletion5Pair7_20V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 19) homogeneousCompletion5Pair7_20D homogeneousCompletion5G homogeneousCompletion5Pair7_20_sp_check

theorem homogeneousCompletion5Pair7_20_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_20S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_20S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_20U homogeneousCompletion5Pair7_20V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 19)
    homogeneousCompletion5Pair7_20D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_20W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_20_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_20D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_20_top :
    homogeneousCompletion5Pair7_20S 19 * homogeneousCompletion5GPoly 19 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_20S 19 * homogeneousCompletion5GPoly 19) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_20S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_20S 19 := by
  have hL0 : homogeneousCompletion5Pair7_20L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 19) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_20L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_20L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_20L (homogeneousCompletion5Leading 19) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_20U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_20L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_20_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_20V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_20L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_20_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_20D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_20D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_20L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_20D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_20L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_20_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_20S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_20D k)) 6 19 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_21S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 20
    (rationalSparsePolynomial homogeneousCompletion5Pair7_21U) (rationalSparsePolynomial homogeneousCompletion5Pair7_21V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_21D k))

theorem homogeneousCompletion5Pair7_21_relation : (∑ k, homogeneousCompletion5Pair7_21S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_21S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_21U homogeneousCompletion5Pair7_21V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 20) homogeneousCompletion5Pair7_21D homogeneousCompletion5G homogeneousCompletion5Pair7_21_sp_check

theorem homogeneousCompletion5Pair7_21_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_21S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_21S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_21U homogeneousCompletion5Pair7_21V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 20)
    homogeneousCompletion5Pair7_21D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_21W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_21_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_21D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_21_top :
    homogeneousCompletion5Pair7_21S 20 * homogeneousCompletion5GPoly 20 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_21S 20 * homogeneousCompletion5GPoly 20) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_21S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_21S 20 := by
  have hL0 : homogeneousCompletion5Pair7_21L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 20) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_21L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_21L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_21L (homogeneousCompletion5Leading 20) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_21U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_21L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_21_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_21V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_21L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_21_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_21D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_21D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_21L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_21D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_21L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_21_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_21S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_21D k)) 6 20 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_22S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 21
    (rationalSparsePolynomial homogeneousCompletion5Pair7_22U) (rationalSparsePolynomial homogeneousCompletion5Pair7_22V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_22D k))

theorem homogeneousCompletion5Pair7_22_relation : (∑ k, homogeneousCompletion5Pair7_22S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_22S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_22U homogeneousCompletion5Pair7_22V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 21) homogeneousCompletion5Pair7_22D homogeneousCompletion5G homogeneousCompletion5Pair7_22_sp_check

theorem homogeneousCompletion5Pair7_22_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_22S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_22S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_22U homogeneousCompletion5Pair7_22V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 21)
    homogeneousCompletion5Pair7_22D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_22W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_22_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_22D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_22_top :
    homogeneousCompletion5Pair7_22S 21 * homogeneousCompletion5GPoly 21 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_22S 21 * homogeneousCompletion5GPoly 21) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_22S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_22S 21 := by
  have hL0 : homogeneousCompletion5Pair7_22L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 21) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_22L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_22L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_22L (homogeneousCompletion5Leading 21) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_22U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_22L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_22_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_22V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_22L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 21)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_22_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_22D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_22D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_22L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_22D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_22L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_22_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_22S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_22D k)) 6 21 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
