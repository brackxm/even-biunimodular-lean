/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs56Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs56OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair11_17S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 16
    (rationalSparsePolynomial homogeneousCompletion5Pair11_17U) (rationalSparsePolynomial homogeneousCompletion5Pair11_17V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_17D k))

theorem homogeneousCompletion5Pair11_17_relation : (∑ k, homogeneousCompletion5Pair11_17S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair11_17S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair11_17U homogeneousCompletion5Pair11_17V
    (homogeneousCompletion5G 10) (homogeneousCompletion5G 16) homogeneousCompletion5Pair11_17D homogeneousCompletion5G homogeneousCompletion5Pair11_17_sp_check

theorem homogeneousCompletion5Pair11_17_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair11_17S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair11_17S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair11_17U homogeneousCompletion5Pair11_17V
    (homogeneousCompletion5M (Fin.last 4) 10) (homogeneousCompletion5M (Fin.last 4) 16)
    homogeneousCompletion5Pair11_17D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair11_17W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair11_17_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair11_17D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair11_17_top :
    homogeneousCompletion5Pair11_17S 16 * homogeneousCompletion5GPoly 16 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair11_17S 16 * homogeneousCompletion5GPoly 16) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 16) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_17S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_17S 16 := by
  have hL0 : homogeneousCompletion5Pair11_17L = homogeneousExponentSup (homogeneousCompletion5Leading 10) (homogeneousCompletion5Leading 16) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair11_17L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 16) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 0, 2, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_17L (homogeneousCompletion5Leading 10) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_17L (homogeneousCompletion5Leading 16) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair11_17U =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_17L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_17_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair11_17V =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_17L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 16)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_17_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair11_17D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair11_17D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair11_17L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair11_17D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair11_17L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair11_17_degree_bounds_check k)
  unfold homogeneousCompletion5Pair11_17S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_17D k)) 10 16 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair11_18S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 17
    (rationalSparsePolynomial homogeneousCompletion5Pair11_18U) (rationalSparsePolynomial homogeneousCompletion5Pair11_18V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_18D k))

theorem homogeneousCompletion5Pair11_18_relation : (∑ k, homogeneousCompletion5Pair11_18S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair11_18S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair11_18U homogeneousCompletion5Pair11_18V
    (homogeneousCompletion5G 10) (homogeneousCompletion5G 17) homogeneousCompletion5Pair11_18D homogeneousCompletion5G homogeneousCompletion5Pair11_18_sp_check

theorem homogeneousCompletion5Pair11_18_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair11_18S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair11_18S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair11_18U homogeneousCompletion5Pair11_18V
    (homogeneousCompletion5M (Fin.last 4) 10) (homogeneousCompletion5M (Fin.last 4) 17)
    homogeneousCompletion5Pair11_18D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair11_18W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair11_18_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair11_18D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair11_18_top :
    homogeneousCompletion5Pair11_18S 17 * homogeneousCompletion5GPoly 17 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair11_18S 17 * homogeneousCompletion5GPoly 17) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_18S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_18S 17 := by
  have hL0 : homogeneousCompletion5Pair11_18L = homogeneousExponentSup (homogeneousCompletion5Leading 10) (homogeneousCompletion5Leading 17) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair11_18L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_18L (homogeneousCompletion5Leading 10) := by native_decide
  have hV0 : (⟨0, 1, 1, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_18L (homogeneousCompletion5Leading 17) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair11_18U =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_18L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_18_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair11_18V =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_18L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_18_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair11_18D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair11_18D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair11_18L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair11_18D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair11_18L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair11_18_degree_bounds_check k)
  unfold homogeneousCompletion5Pair11_18S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_18D k)) 10 17 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair11_19S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 18
    (rationalSparsePolynomial homogeneousCompletion5Pair11_19U) (rationalSparsePolynomial homogeneousCompletion5Pair11_19V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_19D k))

theorem homogeneousCompletion5Pair11_19_relation : (∑ k, homogeneousCompletion5Pair11_19S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair11_19S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair11_19U homogeneousCompletion5Pair11_19V
    (homogeneousCompletion5G 10) (homogeneousCompletion5G 18) homogeneousCompletion5Pair11_19D homogeneousCompletion5G homogeneousCompletion5Pair11_19_sp_check

theorem homogeneousCompletion5Pair11_19_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair11_19S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair11_19S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair11_19U homogeneousCompletion5Pair11_19V
    (homogeneousCompletion5M (Fin.last 4) 10) (homogeneousCompletion5M (Fin.last 4) 18)
    homogeneousCompletion5Pair11_19D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair11_19W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair11_19_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair11_19D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair11_19_top :
    homogeneousCompletion5Pair11_19S 18 * homogeneousCompletion5GPoly 18 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair11_19S 18 * homogeneousCompletion5GPoly 18) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_19S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_19S 18 := by
  have hL0 : homogeneousCompletion5Pair11_19L = homogeneousExponentSup (homogeneousCompletion5Leading 10) (homogeneousCompletion5Leading 18) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair11_19L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_19L (homogeneousCompletion5Leading 10) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_19L (homogeneousCompletion5Leading 18) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair11_19U =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_19L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_19_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair11_19V =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_19L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_19_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair11_19D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair11_19D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair11_19L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair11_19D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair11_19L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair11_19_degree_bounds_check k)
  unfold homogeneousCompletion5Pair11_19S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_19D k)) 10 18 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair11_20S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 10 19
    (rationalSparsePolynomial homogeneousCompletion5Pair11_20U) (rationalSparsePolynomial homogeneousCompletion5Pair11_20V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_20D k))

theorem homogeneousCompletion5Pair11_20_relation : (∑ k, homogeneousCompletion5Pair11_20S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair11_20S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair11_20U homogeneousCompletion5Pair11_20V
    (homogeneousCompletion5G 10) (homogeneousCompletion5G 19) homogeneousCompletion5Pair11_20D homogeneousCompletion5G homogeneousCompletion5Pair11_20_sp_check

theorem homogeneousCompletion5Pair11_20_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair11_20S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair11_20S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair11_20U homogeneousCompletion5Pair11_20V
    (homogeneousCompletion5M (Fin.last 4) 10) (homogeneousCompletion5M (Fin.last 4) 19)
    homogeneousCompletion5Pair11_20D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair11_20W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair11_20_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair11_20D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair11_20_top :
    homogeneousCompletion5Pair11_20S 19 * homogeneousCompletion5GPoly 19 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair11_20S 19 * homogeneousCompletion5GPoly 19) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_20S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair11_20S 19 := by
  have hL0 : homogeneousCompletion5Pair11_20L = homogeneousExponentSup (homogeneousCompletion5Leading 10) (homogeneousCompletion5Leading 19) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair11_20L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 2, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_20L (homogeneousCompletion5Leading 10) := by native_decide
  have hV0 : (⟨0, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair11_20L (homogeneousCompletion5Leading 19) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair11_20U =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_20L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 10)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_20_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair11_20V =
      monomial (homogeneousExponent homogeneousCompletion5Pair11_20L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair11_20_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair11_20D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair11_20D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair11_20L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair11_20D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair11_20L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair11_20_degree_bounds_check k)
  unfold homogeneousCompletion5Pair11_20S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair11_20D k)) 10 19 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
