/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion2BasisProofs
import Biunimodular.F11.HomogeneousCompletion2Pairs01Checks
import Biunimodular.F11.HomogeneousCompletion2Pairs01OrderChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion2Pair1_2S : Fin 3 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 1
    (rationalSparsePolynomial homogeneousCompletion2Pair1_2U) (rationalSparsePolynomial homogeneousCompletion2Pair1_2V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion2Pair1_2D k))

theorem homogeneousCompletion2Pair1_2_relation : (∑ k, homogeneousCompletion2Pair1_2S k * homogeneousCompletion2GPoly k) = 0 := by
  rw [homogeneousCompletion2Pair1_2S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion2Pair1_2U homogeneousCompletion2Pair1_2V
    (homogeneousCompletion2G 0) (homogeneousCompletion2G 1) homogeneousCompletion2Pair1_2D homogeneousCompletion2G homogeneousCompletion2Pair1_2_sp_check

theorem homogeneousCompletion2Pair1_2_last :
    relationLabelMap (homogeneousCompletion2MPoly (Fin.last 1)) homogeneousCompletion2Pair1_2S ∈ homogeneousCompletion2PreviousIdeal := by
  rw [homogeneousCompletion2Pair1_2S, criticalRelationVector_label]
  simp only [homogeneousCompletion2MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion2Pair1_2U homogeneousCompletion2Pair1_2V
    (homogeneousCompletion2M (Fin.last 1) 0) (homogeneousCompletion2M (Fin.last 1) 1)
    homogeneousCompletion2Pair1_2D (homogeneousCompletion2M (Fin.last 1)) homogeneousCompletion2Pair1_2W
    (fun i : Fin 1 => homogeneousCompletion2Original i.castSucc) homogeneousCompletion2Pair1_2_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion2Pair1_2D k) *
    rationalSparsePolynomial (homogeneousCompletion2M (Fin.last 1) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion2PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion2PreviousIdeal.mul_mem_left _ (homogeneousCompletion2_original_mem i))

theorem homogeneousCompletion2Pair1_2_top :
    homogeneousCompletion2Pair1_2S 1 * homogeneousCompletion2GPoly 1 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion2Pair1_2S 1 * homogeneousCompletion2GPoly 1) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 1) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion2GPoly homogeneousCompletion2Pair1_2S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion2GPoly homogeneousCompletion2Pair1_2S 1 := by
  have hL0 : homogeneousCompletion2Pair1_2L = homogeneousExponentSup (homogeneousCompletion2Leading 0) (homogeneousCompletion2Leading 1) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion2Pair1_2L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 1) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion2_basis_degree, homogeneousCompletion2_basis_degree]
  have hU0 : (⟨0, 0, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion2Pair1_2L (homogeneousCompletion2Leading 0) := by native_decide
  have hV0 : (⟨0, 0, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion2Pair1_2L (homogeneousCompletion2Leading 1) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion2Pair1_2U =
      monomial (homogeneousExponent homogeneousCompletion2Pair1_2L - homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion2Pair1_2_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion2_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion2Pair1_2V =
      monomial (homogeneousExponent homogeneousCompletion2Pair1_2L - homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion2Pair1_2_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion2_basis_degree]
  have hD (k : Fin 3) : rationalSparsePolynomial (homogeneousCompletion2Pair1_2D k) * homogeneousCompletion2GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion2Pair1_2D k) * homogeneousCompletion2GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion2Pair1_2L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion2Pair1_2D k) (homogeneousCompletion2GPoly k)
      (homogeneousCompletion2Leading k) homogeneousCompletion2Pair1_2L (homogeneousCompletion2_basis_nonzero k) (homogeneousCompletion2_basis_degree k)
      (homogeneousCompletion2Pair1_2_degree_bounds_check k)
  unfold homogeneousCompletion2Pair1_2S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion2GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion2Pair1_2D k)) 0 1 (by decide)
    homogeneousCompletion2_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion2Pair1_3S : Fin 3 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 0 2
    (rationalSparsePolynomial homogeneousCompletion2Pair1_3U) (rationalSparsePolynomial homogeneousCompletion2Pair1_3V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion2Pair1_3D k))

theorem homogeneousCompletion2Pair1_3_relation : (∑ k, homogeneousCompletion2Pair1_3S k * homogeneousCompletion2GPoly k) = 0 := by
  rw [homogeneousCompletion2Pair1_3S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion2Pair1_3U homogeneousCompletion2Pair1_3V
    (homogeneousCompletion2G 0) (homogeneousCompletion2G 2) homogeneousCompletion2Pair1_3D homogeneousCompletion2G homogeneousCompletion2Pair1_3_sp_check

theorem homogeneousCompletion2Pair1_3_last :
    relationLabelMap (homogeneousCompletion2MPoly (Fin.last 1)) homogeneousCompletion2Pair1_3S ∈ homogeneousCompletion2PreviousIdeal := by
  rw [homogeneousCompletion2Pair1_3S, criticalRelationVector_label]
  simp only [homogeneousCompletion2MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion2Pair1_3U homogeneousCompletion2Pair1_3V
    (homogeneousCompletion2M (Fin.last 1) 0) (homogeneousCompletion2M (Fin.last 1) 2)
    homogeneousCompletion2Pair1_3D (homogeneousCompletion2M (Fin.last 1)) homogeneousCompletion2Pair1_3W
    (fun i : Fin 1 => homogeneousCompletion2Original i.castSucc) homogeneousCompletion2Pair1_3_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion2Pair1_3D k) *
    rationalSparsePolynomial (homogeneousCompletion2M (Fin.last 1) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion2PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion2PreviousIdeal.mul_mem_left _ (homogeneousCompletion2_original_mem i))

theorem homogeneousCompletion2Pair1_3_top :
    homogeneousCompletion2Pair1_3S 2 * homogeneousCompletion2GPoly 2 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion2Pair1_3S 2 * homogeneousCompletion2GPoly 2) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 2) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion2GPoly homogeneousCompletion2Pair1_3S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion2GPoly homogeneousCompletion2Pair1_3S 2 := by
  have hL0 : homogeneousCompletion2Pair1_3L = homogeneousExponentSup (homogeneousCompletion2Leading 0) (homogeneousCompletion2Leading 2) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion2Pair1_3L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 0) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 2) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion2_basis_degree, homogeneousCompletion2_basis_degree]
  have hU0 : (⟨0, 1, 0, 1, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion2Pair1_3L (homogeneousCompletion2Leading 0) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion2Pair1_3L (homogeneousCompletion2Leading 2) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion2Pair1_3U =
      monomial (homogeneousExponent homogeneousCompletion2Pair1_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 0)) (1 : ℂ) := by
    rw [homogeneousCompletion2Pair1_3_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion2_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion2Pair1_3V =
      monomial (homogeneousExponent homogeneousCompletion2Pair1_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion2Pair1_3_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion2_basis_degree]
  have hD (k : Fin 3) : rationalSparsePolynomial (homogeneousCompletion2Pair1_3D k) * homogeneousCompletion2GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion2Pair1_3D k) * homogeneousCompletion2GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion2Pair1_3L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion2Pair1_3D k) (homogeneousCompletion2GPoly k)
      (homogeneousCompletion2Leading k) homogeneousCompletion2Pair1_3L (homogeneousCompletion2_basis_nonzero k) (homogeneousCompletion2_basis_degree k)
      (homogeneousCompletion2Pair1_3_degree_bounds_check k)
  unfold homogeneousCompletion2Pair1_3S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion2GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion2Pair1_3D k)) 0 2 (by decide)
    homogeneousCompletion2_basis_nonzero (by simpa only [hL] using hD)

def homogeneousCompletion2Pair2_3S : Fin 3 → MvPolynomial (Fin 6) ℂ :=
  criticalRelationVector 1 2
    (rationalSparsePolynomial homogeneousCompletion2Pair2_3U) (rationalSparsePolynomial homogeneousCompletion2Pair2_3V)
    (fun k => rationalSparsePolynomial (homogeneousCompletion2Pair2_3D k))

theorem homogeneousCompletion2Pair2_3_relation : (∑ k, homogeneousCompletion2Pair2_3S k * homogeneousCompletion2GPoly k) = 0 := by
  rw [homogeneousCompletion2Pair2_3S, criticalRelationVector_sum]
  exact rationalSparseZeroCheck.sub_sum homogeneousCompletion2Pair2_3U homogeneousCompletion2Pair2_3V
    (homogeneousCompletion2G 1) (homogeneousCompletion2G 2) homogeneousCompletion2Pair2_3D homogeneousCompletion2G homogeneousCompletion2Pair2_3_sp_check

theorem homogeneousCompletion2Pair2_3_last :
    relationLabelMap (homogeneousCompletion2MPoly (Fin.last 1)) homogeneousCompletion2Pair2_3S ∈ homogeneousCompletion2PreviousIdeal := by
  rw [homogeneousCompletion2Pair2_3S, criticalRelationVector_label]
  simp only [homogeneousCompletion2MPoly]
  have heq := rationalSparseZeroCheck.sub_sum_eq_sum homogeneousCompletion2Pair2_3U homogeneousCompletion2Pair2_3V
    (homogeneousCompletion2M (Fin.last 1) 1) (homogeneousCompletion2M (Fin.last 1) 2)
    homogeneousCompletion2Pair2_3D (homogeneousCompletion2M (Fin.last 1)) homogeneousCompletion2Pair2_3W
    (fun i : Fin 1 => homogeneousCompletion2Original i.castSucc) homogeneousCompletion2Pair2_3_last_check
  change _ - _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion2Pair2_3D k) *
    rationalSparsePolynomial (homogeneousCompletion2M (Fin.last 1) k)) ∈ _
  rw [heq]
  exact homogeneousCompletion2PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion2PreviousIdeal.mul_mem_left _ (homogeneousCompletion2_original_mem i))

theorem homogeneousCompletion2Pair2_3_top :
    homogeneousCompletion2Pair2_3S 2 * homogeneousCompletion2GPoly 2 ≠ 0 ∧
    homogeneousGrevlexOrder.degree (homogeneousCompletion2Pair2_3S 2 * homogeneousCompletion2GPoly 2) =
      homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 2) ∧
    ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion2GPoly homogeneousCompletion2Pair2_3S k ≤
      schreyerKey homogeneousGrevlexOrder homogeneousCompletion2GPoly homogeneousCompletion2Pair2_3S 2 := by
  have hL0 : homogeneousCompletion2Pair2_3L = homogeneousExponentSup (homogeneousCompletion2Leading 1) (homogeneousCompletion2Leading 2) := by
    native_decide
  have hL : homogeneousExponent homogeneousCompletion2Pair2_3L =
      homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 1) ⊔
        homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 2) := by
    rw [hL0, homogeneousExponent_sup, homogeneousCompletion2_basis_degree, homogeneousCompletion2_basis_degree]
  have hU0 : (⟨0, 1, 0, 0, 1, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion2Pair2_3L (homogeneousCompletion2Leading 1) := by native_decide
  have hV0 : (⟨1, 0, 0, 0, 0, 0⟩ : FixedSliceSparseExponent) =
      homogeneousExponentSub homogeneousCompletion2Pair2_3L (homogeneousCompletion2Leading 2) := by native_decide
  have hU : rationalSparsePolynomial homogeneousCompletion2Pair2_3U =
      monomial (homogeneousExponent homogeneousCompletion2Pair2_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 1)) (1 : ℂ) := by
    rw [homogeneousCompletion2Pair2_3_monomials_check.1, rationalSparsePolynomial_monomial, hU0,
      homogeneousExponent_sub, ← homogeneousCompletion2_basis_degree]
  have hV : rationalSparsePolynomial homogeneousCompletion2Pair2_3V =
      monomial (homogeneousExponent homogeneousCompletion2Pair2_3L - homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly 2)) (1 : ℂ) := by
    rw [homogeneousCompletion2Pair2_3_monomials_check.2, rationalSparsePolynomial_monomial, hV0,
      homogeneousExponent_sub, ← homogeneousCompletion2_basis_degree]
  have hD (k : Fin 3) : rationalSparsePolynomial (homogeneousCompletion2Pair2_3D k) * homogeneousCompletion2GPoly k = 0 ∨
      homogeneousGrevlexOrder.degree (rationalSparsePolynomial (homogeneousCompletion2Pair2_3D k) * homogeneousCompletion2GPoly k)
        ≺[homogeneousGrevlexOrder] homogeneousExponent homogeneousCompletion2Pair2_3L :=
    rationalSparsePolynomial_mul_strict_bound (homogeneousCompletion2Pair2_3D k) (homogeneousCompletion2GPoly k)
      (homogeneousCompletion2Leading k) homogeneousCompletion2Pair2_3L (homogeneousCompletion2_basis_nonzero k) (homogeneousCompletion2_basis_degree k)
      (homogeneousCompletion2Pair2_3_degree_bounds_check k)
  unfold homogeneousCompletion2Pair2_3S
  rw [hU, hV, hL]
  exact criticalRelationVector_top homogeneousGrevlexOrder homogeneousCompletion2GPoly
    (fun k => rationalSparsePolynomial (homogeneousCompletion2Pair2_3D k)) 1 2 (by decide)
    homogeneousCompletion2_basis_nonzero (by simpa only [hL] using hD)

end
end Biunimodular.F11
