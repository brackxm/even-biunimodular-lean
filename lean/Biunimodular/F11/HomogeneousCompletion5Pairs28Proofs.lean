/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs28Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs28OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair5_16S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 15
    (rationalSparsePolynomial homogeneousCompletion5Pair5_16U) (rationalSparsePolynomial homogeneousCompletion5Pair5_16V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_16D k))

theorem homogeneousCompletion5Pair5_16_relation : (∑ k, homogeneousCompletion5Pair5_16S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_16S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_16U homogeneousCompletion5Pair5_16V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 15) homogeneousCompletion5Pair5_16D homogeneousCompletion5G homogeneousCompletion5Pair5_16_sp_check

theorem homogeneousCompletion5Pair5_16_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_16S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_16S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_16U homogeneousCompletion5Pair5_16V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 15)
    homogeneousCompletion5Pair5_16D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_16W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_16_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_16D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_16_top :
    homogeneousCompletion5Pair5_16S 15 * homogeneousCompletion5GPoly 15 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_16S 15 * homogeneousCompletion5GPoly 15) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 15) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_16S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_16S 15 := by
  have hL0 : homogeneousCompletion5Pair5_16L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 15) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_16L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 15) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 2, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_16L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_16L (homogeneousCompletion5Leading 15) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_16U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_16L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_16_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_16V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_16L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 15)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_16_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_16D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_16D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_16L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_16D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_16L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_16_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_16S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_16D k)) 4 15 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair5_17S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 16
    (rationalSparsePolynomial homogeneousCompletion5Pair5_17U) (rationalSparsePolynomial homogeneousCompletion5Pair5_17V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_17D k))

theorem homogeneousCompletion5Pair5_17_relation : (∑ k, homogeneousCompletion5Pair5_17S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_17S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_17U homogeneousCompletion5Pair5_17V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 16) homogeneousCompletion5Pair5_17D homogeneousCompletion5G homogeneousCompletion5Pair5_17_sp_check

theorem homogeneousCompletion5Pair5_17_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_17S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_17S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_17U homogeneousCompletion5Pair5_17V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 16)
    homogeneousCompletion5Pair5_17D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_17W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_17_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_17D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_17_top :
    homogeneousCompletion5Pair5_17S 16 * homogeneousCompletion5GPoly 16 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_17S 16 * homogeneousCompletion5GPoly 16) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 16) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_17S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_17S 16 := by
  have hL0 : homogeneousCompletion5Pair5_17L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 16) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_17L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 16) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 1, 2, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_17L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_17L (homogeneousCompletion5Leading 16) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_17U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_17L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_17_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_17V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_17L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 16)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_17_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_17D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_17D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_17L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_17D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_17L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_17_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_17S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_17D k)) 4 16 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair5_18S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 17
    (rationalSparsePolynomial homogeneousCompletion5Pair5_18U) (rationalSparsePolynomial homogeneousCompletion5Pair5_18V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_18D k))

theorem homogeneousCompletion5Pair5_18_relation : (∑ k, homogeneousCompletion5Pair5_18S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_18S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_18U homogeneousCompletion5Pair5_18V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 17) homogeneousCompletion5Pair5_18D homogeneousCompletion5G homogeneousCompletion5Pair5_18_sp_check

theorem homogeneousCompletion5Pair5_18_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_18S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_18S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_18U homogeneousCompletion5Pair5_18V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 17)
    homogeneousCompletion5Pair5_18D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_18W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_18_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_18D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_18_top :
    homogeneousCompletion5Pair5_18S 17 * homogeneousCompletion5GPoly 17 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_18S 17 * homogeneousCompletion5GPoly 17) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_18S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_18S 17 := by
  have hL0 : homogeneousCompletion5Pair5_18L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 17) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_18L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 3, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_18L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_18L (homogeneousCompletion5Leading 17) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_18U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_18L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_18_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_18V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_18L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_18_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_18D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_18D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_18L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_18D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_18L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_18_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_18S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_18D k)) 4 17 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair5_19S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 4 18
    (rationalSparsePolynomial homogeneousCompletion5Pair5_19U) (rationalSparsePolynomial homogeneousCompletion5Pair5_19V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_19D k))

theorem homogeneousCompletion5Pair5_19_relation : (∑ k, homogeneousCompletion5Pair5_19S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair5_19S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair5_19U homogeneousCompletion5Pair5_19V
    (homogeneousCompletion5G 4) (homogeneousCompletion5G 18) homogeneousCompletion5Pair5_19D homogeneousCompletion5G homogeneousCompletion5Pair5_19_sp_check

theorem homogeneousCompletion5Pair5_19_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair5_19S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair5_19S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair5_19U homogeneousCompletion5Pair5_19V
    (homogeneousCompletion5M (Fin.last 4) 4) (homogeneousCompletion5M (Fin.last 4) 18)
    homogeneousCompletion5Pair5_19D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair5_19W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair5_19_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair5_19D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair5_19_top :
    homogeneousCompletion5Pair5_19S 18 * homogeneousCompletion5GPoly 18 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair5_19S 18 * homogeneousCompletion5GPoly 18) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_19S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair5_19S 18 := by
  have hL0 : homogeneousCompletion5Pair5_19L = homogeneousExponentSup (homogeneousCompletion5Leading 4) (homogeneousCompletion5Leading 18) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair5_19L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 2, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_19L (homogeneousCompletion5Leading 4) := by native_decide
  have hV0 : (⟨2, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair5_19L (homogeneousCompletion5Leading 18) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair5_19U =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_19L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 4)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_19_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair5_19V =
      monomial (homogeneousExponent homogeneousCompletion5Pair5_19L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair5_19_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair5_19D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair5_19D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair5_19L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair5_19D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair5_19L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair5_19_degree_bounds_check k)
  unfold homogeneousCompletion5Pair5_19S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair5_19D k)) 4 18 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
