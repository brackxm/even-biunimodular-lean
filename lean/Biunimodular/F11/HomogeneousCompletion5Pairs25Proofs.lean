/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs25Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs25OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair4_26S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 25
    (rationalSparsePolynomial homogeneousCompletion5Pair4_26U) (rationalSparsePolynomial homogeneousCompletion5Pair4_26V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_26D k))

theorem homogeneousCompletion5Pair4_26_relation : (∑ k, homogeneousCompletion5Pair4_26S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair4_26S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair4_26U homogeneousCompletion5Pair4_26V
    (homogeneousCompletion5G 3) (homogeneousCompletion5G 25) homogeneousCompletion5Pair4_26D homogeneousCompletion5G homogeneousCompletion5Pair4_26_sp_check

theorem homogeneousCompletion5Pair4_26_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair4_26S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair4_26S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair4_26U homogeneousCompletion5Pair4_26V
    (homogeneousCompletion5M (Fin.last 4) 3) (homogeneousCompletion5M (Fin.last 4) 25)
    homogeneousCompletion5Pair4_26D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair4_26W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair4_26_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair4_26D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair4_26_top :
    homogeneousCompletion5Pair4_26S 25 * homogeneousCompletion5GPoly 25 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair4_26S 25 * homogeneousCompletion5GPoly 25) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_26S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_26S 25 := by
  have hL0 : homogeneousCompletion5Pair4_26L = homogeneousExponentSup (homogeneousCompletion5Leading 3) (homogeneousCompletion5Leading 25) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair4_26L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 5, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_26L (homogeneousCompletion5Leading 3) := by native_decide
  have hV0 : (⟨1, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_26L (homogeneousCompletion5Leading 25) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair4_26U =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_26_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair4_26V =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_26L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 25)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_26_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair4_26D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair4_26D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair4_26L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair4_26D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair4_26L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair4_26_degree_bounds_check k)
  unfold homogeneousCompletion5Pair4_26S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_26D k)) 3 25 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair4_27S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 26
    (rationalSparsePolynomial homogeneousCompletion5Pair4_27U) (rationalSparsePolynomial homogeneousCompletion5Pair4_27V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_27D k))

theorem homogeneousCompletion5Pair4_27_relation : (∑ k, homogeneousCompletion5Pair4_27S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair4_27S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair4_27U homogeneousCompletion5Pair4_27V
    (homogeneousCompletion5G 3) (homogeneousCompletion5G 26) homogeneousCompletion5Pair4_27D homogeneousCompletion5G homogeneousCompletion5Pair4_27_sp_check

theorem homogeneousCompletion5Pair4_27_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair4_27S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair4_27S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair4_27U homogeneousCompletion5Pair4_27V
    (homogeneousCompletion5M (Fin.last 4) 3) (homogeneousCompletion5M (Fin.last 4) 26)
    homogeneousCompletion5Pair4_27D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair4_27W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair4_27_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair4_27D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair4_27_top :
    homogeneousCompletion5Pair4_27S 26 * homogeneousCompletion5GPoly 26 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair4_27S 26 * homogeneousCompletion5GPoly 26) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_27S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_27S 26 := by
  have hL0 : homogeneousCompletion5Pair4_27L = homogeneousExponentSup (homogeneousCompletion5Leading 3) (homogeneousCompletion5Leading 26) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair4_27L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 6, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_27L (homogeneousCompletion5Leading 3) := by native_decide
  have hV0 : (⟨1, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_27L (homogeneousCompletion5Leading 26) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair4_27U =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_27_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair4_27V =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_27L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 26)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_27_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair4_27D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair4_27D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair4_27L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair4_27D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair4_27L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair4_27_degree_bounds_check k)
  unfold homogeneousCompletion5Pair4_27S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_27D k)) 3 26 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair5_6S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 5
    (rationalSparsePolynomial homogeneousCompletion5Pair5_6U) (rationalSparsePolynomial homogeneousCompletion5Pair5_6V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_6D k))

theorem homogeneousCompletion5Pair5_6_relation : (∑ k, homogeneousCompletion5Pair5_6S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_6S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_6U homogeneousCompletion5Pair5_6V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 5) homogeneousCompletion5Pair5_6D homogeneousCompletion5G homogeneousCompletion5Pair5_6_sp_check

theorem homogeneousCompletion5Pair5_6_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_6S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_6S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_6U homogeneousCompletion5Pair5_6V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 5)
    homogeneousCompletion5Pair5_6D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_6W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_6_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_6D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_6_top :
    homogeneousCompletion5Pair5_6S 5 * homogeneousCompletion5GPoly 5 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_6S 5 * homogeneousCompletion5GPoly 5) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_6S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_6S 5 := by
  have hL0 : homogeneousCompletion5Pair5_6L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 5) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_6L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_6L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_6L (homogeneousCompletion5Leading 5) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_6U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_6_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_6V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_6L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 5)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_6_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_6D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_6D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_6L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_6D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_6L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_6_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_6S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_6D k)) 4 5 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair5_7S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 6
    (rationalSparsePolynomial homogeneousCompletion5Pair5_7U) (rationalSparsePolynomial homogeneousCompletion5Pair5_7V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_7D k))

theorem homogeneousCompletion5Pair5_7_relation : (∑ k, homogeneousCompletion5Pair5_7S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_7S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_7U homogeneousCompletion5Pair5_7V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 6) homogeneousCompletion5Pair5_7D homogeneousCompletion5G homogeneousCompletion5Pair5_7_sp_check

theorem homogeneousCompletion5Pair5_7_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_7S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_7S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_7U homogeneousCompletion5Pair5_7V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 6)
    homogeneousCompletion5Pair5_7D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_7W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_7_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_7D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_7_top :
    homogeneousCompletion5Pair5_7S 6 * homogeneousCompletion5GPoly 6 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_7S 6 * homogeneousCompletion5GPoly 6) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_7S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_7S 6 := by
  have hL0 : homogeneousCompletion5Pair5_7L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 6) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_7L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 2, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_7L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_7L (homogeneousCompletion5Leading 6) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_7U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_7_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_7V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_7L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 6)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_7_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_7D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_7D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_7L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_7D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_7L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_7_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_7S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_7D k)) 4 6 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
