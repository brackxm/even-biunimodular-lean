/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisProofs
import Biunimodular.F11.HomogeneousCompletion5Pairs23Checks
import Biunimodular.F11.HomogeneousCompletion5Pairs23OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion5Pair4_18S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 17
    (rationalSparsePolynomial homogeneousCompletion5Pair4_18U) (rationalSparsePolynomial homogeneousCompletion5Pair4_18V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_18D k))

theorem homogeneousCompletion5Pair4_18_relation : (∑ k, homogeneousCompletion5Pair4_18S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair4_18S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair4_18U homogeneousCompletion5Pair4_18V
    (homogeneousCompletion5G 3) (homogeneousCompletion5G 17) homogeneousCompletion5Pair4_18D homogeneousCompletion5G homogeneousCompletion5Pair4_18_sp_check

theorem homogeneousCompletion5Pair4_18_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair4_18S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair4_18S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair4_18U homogeneousCompletion5Pair4_18V
    (homogeneousCompletion5M (Fin.last 4) 3) (homogeneousCompletion5M (Fin.last 4) 17)
    homogeneousCompletion5Pair4_18D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair4_18W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair4_18_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair4_18D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair4_18_top :
    homogeneousCompletion5Pair4_18S 17 * homogeneousCompletion5GPoly 17 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair4_18S 17 * homogeneousCompletion5GPoly 17) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_18S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_18S 17 := by
  have hL0 : homogeneousCompletion5Pair4_18L = homogeneousExponentSup (homogeneousCompletion5Leading 3) (homogeneousCompletion5Leading 17) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair4_18L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 3, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_18L (homogeneousCompletion5Leading 3) := by native_decide
  have hV0 : (⟨1, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_18L (homogeneousCompletion5Leading 17) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair4_18U =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_18L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_18_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair4_18V =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_18L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 17)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_18_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair4_18D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair4_18D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair4_18L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair4_18D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair4_18L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair4_18_degree_bounds_check k)
  unfold homogeneousCompletion5Pair4_18S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_18D k)) 3 17 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair4_19S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 18
    (rationalSparsePolynomial homogeneousCompletion5Pair4_19U) (rationalSparsePolynomial homogeneousCompletion5Pair4_19V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_19D k))

theorem homogeneousCompletion5Pair4_19_relation : (∑ k, homogeneousCompletion5Pair4_19S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair4_19S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair4_19U homogeneousCompletion5Pair4_19V
    (homogeneousCompletion5G 3) (homogeneousCompletion5G 18) homogeneousCompletion5Pair4_19D homogeneousCompletion5G homogeneousCompletion5Pair4_19_sp_check

theorem homogeneousCompletion5Pair4_19_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair4_19S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair4_19S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair4_19U homogeneousCompletion5Pair4_19V
    (homogeneousCompletion5M (Fin.last 4) 3) (homogeneousCompletion5M (Fin.last 4) 18)
    homogeneousCompletion5Pair4_19D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair4_19W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair4_19_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair4_19D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair4_19_top :
    homogeneousCompletion5Pair4_19S 18 * homogeneousCompletion5GPoly 18 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair4_19S 18 * homogeneousCompletion5GPoly 18) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_19S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_19S 18 := by
  have hL0 : homogeneousCompletion5Pair4_19L = homogeneousExponentSup (homogeneousCompletion5Leading 3) (homogeneousCompletion5Leading 18) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair4_19L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 2, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_19L (homogeneousCompletion5Leading 3) := by native_decide
  have hV0 : (⟨1, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_19L (homogeneousCompletion5Leading 18) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair4_19U =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_19L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_19_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair4_19V =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_19L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 18)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_19_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair4_19D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair4_19D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair4_19L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair4_19D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair4_19L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair4_19_degree_bounds_check k)
  unfold homogeneousCompletion5Pair4_19S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_19D k)) 3 18 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair4_20S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 19
    (rationalSparsePolynomial homogeneousCompletion5Pair4_20U) (rationalSparsePolynomial homogeneousCompletion5Pair4_20V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_20D k))

theorem homogeneousCompletion5Pair4_20_relation : (∑ k, homogeneousCompletion5Pair4_20S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair4_20S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair4_20U homogeneousCompletion5Pair4_20V
    (homogeneousCompletion5G 3) (homogeneousCompletion5G 19) homogeneousCompletion5Pair4_20D homogeneousCompletion5G homogeneousCompletion5Pair4_20_sp_check

theorem homogeneousCompletion5Pair4_20_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair4_20S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair4_20S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair4_20U homogeneousCompletion5Pair4_20V
    (homogeneousCompletion5M (Fin.last 4) 3) (homogeneousCompletion5M (Fin.last 4) 19)
    homogeneousCompletion5Pair4_20D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair4_20W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair4_20_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair4_20D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair4_20_top :
    homogeneousCompletion5Pair4_20S 19 * homogeneousCompletion5GPoly 19 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair4_20S 19 * homogeneousCompletion5GPoly 19) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_20S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_20S 19 := by
  have hL0 : homogeneousCompletion5Pair4_20L = homogeneousExponentSup (homogeneousCompletion5Leading 3) (homogeneousCompletion5Leading 19) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair4_20L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 1, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_20L (homogeneousCompletion5Leading 3) := by native_decide
  have hV0 : (⟨1, 1, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_20L (homogeneousCompletion5Leading 19) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair4_20U =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_20L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_20_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair4_20V =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_20L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 19)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_20_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair4_20D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair4_20D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair4_20L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair4_20D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair4_20L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair4_20_degree_bounds_check k)
  unfold homogeneousCompletion5Pair4_20S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_20D k)) 3 19 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion5Pair4_21S : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 3 20
    (rationalSparsePolynomial homogeneousCompletion5Pair4_21U) (rationalSparsePolynomial homogeneousCompletion5Pair4_21V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_21D k))

theorem homogeneousCompletion5Pair4_21_relation : (∑ k, homogeneousCompletion5Pair4_21S k * homogeneousCompletion5GPoly k) = 0 := by
  rw [homogeneousCompletion5Pair4_21S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion5Pair4_21U homogeneousCompletion5Pair4_21V
    (homogeneousCompletion5G 3) (homogeneousCompletion5G 20) homogeneousCompletion5Pair4_21D homogeneousCompletion5G homogeneousCompletion5Pair4_21_sp_check

theorem homogeneousCompletion5Pair4_21_last :
    relationLabelMap (homogeneousCompletion5MPoly (Fin.last 4)) homogeneousCompletion5Pair4_21S ∈ homogeneousCompletion5PreviousIdeal := by
  rw [homogeneousCompletion5Pair4_21S, criticalRelationVector_label]
  simp only [homogeneousCompletion5MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion5Pair4_21U homogeneousCompletion5Pair4_21V
    (homogeneousCompletion5M (Fin.last 4) 3) (homogeneousCompletion5M (Fin.last 4) 20)
    homogeneousCompletion5Pair4_21D (homogeneousCompletion5M (Fin.last 4)) homogeneousCompletion5Pair4_21W
    (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc) homogeneousCompletion5Pair4_21_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5Pair4_21D k) *
    rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

theorem homogeneousCompletion5Pair4_21_top :
    homogeneousCompletion5Pair4_21S 20 * homogeneousCompletion5GPoly 20 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion5Pair4_21S 20 * homogeneousCompletion5GPoly 20) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_21S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion5GPoly homogeneousCompletion5Pair4_21S 20 := by
  have hL0 : homogeneousCompletion5Pair4_21L = homogeneousExponentSup (homogeneousCompletion5Leading 3) (homogeneousCompletion5Leading 20) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion5Pair4_21L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion5_basis_degree, homogeneousCompletion5_basis_degree]
  have hU0 : (⟨0, 0, 0, 3, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_21L (homogeneousCompletion5Leading 3) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion5Pair4_21L (homogeneousCompletion5Leading 20) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion5Pair4_21U =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_21L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 3)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_21_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion5Pair4_21V =
      monomial (homogeneousExponent homogeneousCompletion5Pair4_21L - homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly 20)) (1 : ℂ) := by
    rw [homogeneousCompletion5Pair4_21_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion5_basis_degree]
  have hD (k : Fin 27) : rationalSparsePolynomial (homogeneousCompletion5Pair4_21D k) * homogeneousCompletion5GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion5Pair4_21D k) * homogeneousCompletion5GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion5Pair4_21L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion5Pair4_21D k) (homogeneousCompletion5GPoly k)
      (homogeneousCompletion5Leading k) homogeneousCompletion5Pair4_21L (homogeneousCompletion5_basis_nonzero k) (homogeneousCompletion5_basis_degree k)
      (homogeneousCompletion5Pair4_21_degree_bounds_check k)
  unfold homogeneousCompletion5Pair4_21S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion5GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion5Pair4_21D k)) 3 20 (by decide)
    homogeneousCompletion5_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
