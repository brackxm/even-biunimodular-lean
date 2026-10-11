/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceHomogeneousAffineChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

theorem fixedSliceHomogeneousQuadric_smul {K : Type*} [Field K]
    (F : Even6 K →ₗ[K] Even6 K) (c : K) (j : Fin 6) :
    fixedSliceHomogeneousQuadric (c • F) j = C c * fixedSliceHomogeneousQuadric F j := by
  classical
  have hf : ∀ k, fixedSliceFourierLinearForm (c • F) k =
      C c * fixedSliceFourierLinearForm F k := by
    intro k
    simp only [fixedSliceFourierLinearForm, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [fixedSliceHomogeneousQuadric, hf j, hf 0, fixedSliceHomogeneousQuadric]
  ring

theorem fixedSliceBaseIdeal_scale {K : Type*} [Field K] {n : ℕ}
    (gs : List (MvPolynomial (Fin n) K)) (c : K) (hc : c ≠ 0) :
    RedundantCoordinate.baseIdeal (gs.map (fun p => C c * p)) =
      RedundantCoordinate.baseIdeal gs := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (RedundantCoordinate.baseIdeal gs).mul_mem_left _ (Ideal.subset_span hq)
  · apply Ideal.span_le.mpr
    intro p hp
    change p ∈ RedundantCoordinate.baseIdeal (gs.map (fun q => C c * q))
    have h : C c * p ∈ RedundantCoordinate.baseIdeal (gs.map (fun q => C c * q)) :=
      Ideal.subset_span (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hi := (RedundantCoordinate.baseIdeal (gs.map (fun q => C c * q))).mul_mem_left
      (C c⁻¹) h
    simpa only [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] using hi

theorem fixedSliceNormalizedAffineGenerators_eq_scale :
    even11FixedSliceHomogeneousGenerators.map fixedSliceHomogeneousAffineMap =
      fixedSliceFiveGenerators.map (fun p => C ((Real.sqrt 11 : ℂ)⁻¹) * p) := by
  rw [← fixedSliceHomogeneousAffineGenerators_eq]
  simp only [even11FixedSliceHomogeneousGenerators, fixedSliceHomogeneousGenerators,
    even11FourierNormalized, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [fixedSliceHomogeneousQuadric_smul, map_mul]
  simp [fixedSliceHomogeneousAffineMap]

theorem fixedSliceNormalizedAffineIdeal_eq :
    RedundantCoordinate.baseIdeal
      (even11FixedSliceHomogeneousGenerators.map fixedSliceHomogeneousAffineMap) =
        RedundantCoordinate.baseIdeal fixedSliceFiveGenerators := by
  rw [fixedSliceNormalizedAffineGenerators_eq_scale]
  apply fixedSliceBaseIdeal_scale
  apply inv_ne_zero
  exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 11)).ne'

abbrev FixedSliceNormalizedAffineChartAlgebra :=
  RedundantCoordinate.BaseAlgebra
    (even11FixedSliceHomogeneousGenerators.map fixedSliceHomogeneousAffineMap)

def fixedSliceNormalizedAffineChartEquivFive :
    FixedSliceNormalizedAffineChartAlgebra ≃ₐ[ℂ] FixedSliceFiveCoordinateAlgebra :=
  Ideal.quotientEquivAlgOfEq ℂ fixedSliceNormalizedAffineIdeal_eq

theorem fixedSliceNormalizedAffineChart_finrank :
    Module.finrank ℂ FixedSliceNormalizedAffineChartAlgebra = 32 := by
  rw [fixedSliceNormalizedAffineChartEquivFive.toLinearEquiv.finrank_eq]
  exact fixedSliceFiveCoordinateAlgebra_finrank

instance fixedSliceNormalizedAffineChart_isReduced :
    IsReduced FixedSliceNormalizedAffineChartAlgebra :=
  isReduced_of_injective fixedSliceNormalizedAffineChartEquivFive.toRingHom
    fixedSliceNormalizedAffineChartEquivFive.injective

end
end Biunimodular.F11
