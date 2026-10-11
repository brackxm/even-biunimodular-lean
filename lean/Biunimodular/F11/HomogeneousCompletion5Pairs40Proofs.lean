/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs40Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs40OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair7_23S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 22
    (rationalSparsePolynomial homogeneousCompletion5Pair7_23U) (rationalSparsePolynomial homogeneousCompletion5Pair7_23V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_23D k))

theorem homogeneousCompletion5Pair7_23_relation : (∑ k, homogeneousCompletion5Pair7_23S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_23S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_23U homogeneousCompletion5Pair7_23V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 22) homogeneousCompletion5Pair7_23D homogeneousCompletion5G homogeneousCompletion5Pair7_23_sp_check

theorem homogeneousCompletion5Pair7_23_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_23S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_23S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_23U homogeneousCompletion5Pair7_23V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 22)
    homogeneousCompletion5Pair7_23D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_23W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_23_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_23D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_23_top :
    homogeneousCompletion5Pair7_23S 22 * homogeneousCompletion5GPoly 22 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_23S 22 * homogeneousCompletion5GPoly 22) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_23S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_23S 22 := by
  have hL0 : homogeneousCompletion5Pair7_23L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 22) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_23L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 3, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_23L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_23L (homogeneousCompletion5Leading 22) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_23U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_23L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_23_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_23V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_23L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 22)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_23_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_23D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_23D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_23L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_23D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_23L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_23_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_23S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_23D k)) 6 22 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_24S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 23
    (rationalSparsePolynomial homogeneousCompletion5Pair7_24U) (rationalSparsePolynomial homogeneousCompletion5Pair7_24V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_24D k))

theorem homogeneousCompletion5Pair7_24_relation : (∑ k, homogeneousCompletion5Pair7_24S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_24S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_24U homogeneousCompletion5Pair7_24V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 23) homogeneousCompletion5Pair7_24D homogeneousCompletion5G homogeneousCompletion5Pair7_24_sp_check

theorem homogeneousCompletion5Pair7_24_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_24S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_24S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_24U homogeneousCompletion5Pair7_24V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 23)
    homogeneousCompletion5Pair7_24D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_24W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_24_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_24D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_24_top :
    homogeneousCompletion5Pair7_24S 23 * homogeneousCompletion5GPoly 23 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_24S 23 * homogeneousCompletion5GPoly 23) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_24S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_24S 23 := by
  have hL0 : homogeneousCompletion5Pair7_24L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 23) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_24L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 3, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_24L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_24L (homogeneousCompletion5Leading 23) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_24U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_24L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_24_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_24V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_24L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 23)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_24_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_24D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_24D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_24L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_24D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_24L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_24_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_24S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_24D k)) 6 23 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_25S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 24
    (rationalSparsePolynomial homogeneousCompletion5Pair7_25U) (rationalSparsePolynomial homogeneousCompletion5Pair7_25V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_25D k))

theorem homogeneousCompletion5Pair7_25_relation : (∑ k, homogeneousCompletion5Pair7_25S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_25S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_25U homogeneousCompletion5Pair7_25V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 24) homogeneousCompletion5Pair7_25D homogeneousCompletion5G homogeneousCompletion5Pair7_25_sp_check

theorem homogeneousCompletion5Pair7_25_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_25S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_25S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_25U homogeneousCompletion5Pair7_25V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 24)
    homogeneousCompletion5Pair7_25D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_25W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_25_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_25D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_25_top :
    homogeneousCompletion5Pair7_25S 24 * homogeneousCompletion5GPoly 24 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_25S 24 * homogeneousCompletion5GPoly 24) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_25S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_25S 24 := by
  have hL0 : homogeneousCompletion5Pair7_25L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 24) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_25L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 3, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_25L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_25L (homogeneousCompletion5Leading 24) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_25U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_25_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_25V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_25L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 24)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_25_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_25D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_25D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_25L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_25D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_25L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_25_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_25S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_25D k)) 6 24 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair7_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 6 25
    (rationalSparsePolynomial homogeneousCompletion5Pair7_26U) (rationalSparsePolynomial homogeneousCompletion5Pair7_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_26D k))

theorem homogeneousCompletion5Pair7_26_relation : (∑ k, homogeneousCompletion5Pair7_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair7_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair7_26U homogeneousCompletion5Pair7_26V
    (homogeneousCompletion5G 6) (homogeneousCompletion5G 25) homogeneousCompletion5Pair7_26D homogeneousCompletion5G homogeneousCompletion5Pair7_26_sp_check

theorem homogeneousCompletion5Pair7_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair7_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair7_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair7_26U homogeneousCompletion5Pair7_26V
    (homogeneousCompletion5M (Fin.last 4) 6) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair7_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair7_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair7_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair7_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair7_26_top :
    homogeneousCompletion5Pair7_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair7_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair7_26S 25 := by
  have hL0 : homogeneousCompletion5Pair7_26L = homogeneousExponentSup (homogeneousCompletion5Leading 6) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair7_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 5, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_26L (homogeneousCompletion5Leading 6) := by native_decide
  have hV0 : (⟨0, 0, 2, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair7_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair7_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair7_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair7_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair7_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair7_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair7_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair7_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair7_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair7_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair7_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair7_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair7_26D k)) 6 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
