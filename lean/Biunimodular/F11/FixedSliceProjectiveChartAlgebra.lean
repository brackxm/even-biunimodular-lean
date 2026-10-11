/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceHomogeneousLocalization
import Biunimodular.F11.FixedSliceRegularPresentation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual homogeneous equation `qᵢ/h₀²` in the projective chart. -/
def fixedSliceProjectiveChartEquation (i : Fin 5) : FixedSliceProjectiveChartRing :=
  Away.mk (homogeneousSubmodule (Fin 6) ℂ) (isHomogeneous_X ℂ (0 : Fin 6)) 2
    (fixedSliceHomogeneousQuadric even11FourierNormalized i.succ)
    (by simpa using fixedSliceHomogeneousQuadric_isHomogeneous even11FourierNormalized i.succ)

def fixedSliceProjectiveChartIdeal : Ideal FixedSliceProjectiveChartRing :=
  Ideal.span (Set.range fixedSliceProjectiveChartEquation)

/-- The coordinate ring obtained by imposing the original five homogeneous
quadrics in the actual projective chart localization. -/
abbrev FixedSliceProjectiveChartAlgebra :=
  FixedSliceProjectiveChartRing ⧸ fixedSliceProjectiveChartIdeal

theorem fixedSliceProjectiveChartIdeal_map :
    fixedSliceProjectiveChartIdeal.map fixedSliceProjectiveChartEquivPolynomial.toRingHom =
      RedundantCoordinate.baseIdeal
        (even11FixedSliceHomogeneousGenerators.map fixedSliceHomogeneousAffineMap) := by
  rw [fixedSliceProjectiveChartIdeal, Ideal.map_span]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_range,
    List.mem_map, even11FixedSliceHomogeneousGenerators,
    fixedSliceHomogeneousGenerators, List.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨fixedSliceHomogeneousQuadric even11FourierNormalized i.succ, ⟨i, rfl⟩, ?_⟩
    exact (fixedSliceProjectiveChartToAffine_mk 2 _ _).symm
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨fixedSliceProjectiveChartEquation i, ⟨i, rfl⟩,
      fixedSliceProjectiveChartToAffine_mk 2 _ _⟩

def fixedSliceProjectiveChartEquivNormalized :
    FixedSliceProjectiveChartAlgebra ≃ₐ[ℂ] FixedSliceNormalizedAffineChartAlgebra :=
  Ideal.quotientEquivAlg _ _ fixedSliceProjectiveChartEquivPolynomial
    fixedSliceProjectiveChartIdeal_map.symm

theorem fixedSliceProjectiveChart_finrank :
    Module.finrank ℂ FixedSliceProjectiveChartAlgebra = 32 := by
  rw [fixedSliceProjectiveChartEquivNormalized.toLinearEquiv.finrank_eq]
  exact fixedSliceNormalizedAffineChart_finrank

instance fixedSliceProjectiveChart_isReduced : IsReduced FixedSliceProjectiveChartAlgebra :=
  isReduced_of_injective fixedSliceProjectiveChartEquivNormalized.toRingHom
    fixedSliceProjectiveChartEquivNormalized.injective

instance fixedSliceProjectiveChart_etale : Algebra.Etale ℂ FixedSliceProjectiveChartAlgebra :=
  Algebra.Etale.of_equiv fixedSliceProjectiveChartEquivNormalized.symm

instance fixedSliceProjectiveChart_moduleFinite : Module.Finite ℂ FixedSliceProjectiveChartAlgebra :=
  Module.finite_of_finrank_pos (by rw [fixedSliceProjectiveChart_finrank]; norm_num)

instance fixedSliceProjectiveChart_nontrivial : Nontrivial FixedSliceProjectiveChartAlgebra :=
  Module.nontrivial_of_finrank_pos (R := ℂ)
    (by rw [fixedSliceProjectiveChart_finrank]; norm_num)

instance fixedSliceProjectiveChart_artinian : IsArtinianRing FixedSliceProjectiveChartAlgebra :=
  IsArtinianRing.of_finite ℂ FixedSliceProjectiveChartAlgebra

theorem fixedSliceProjectiveChart_krullDimension :
    ringKrullDim FixedSliceProjectiveChartAlgebra = 0 :=
  ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- The actual projective chart has a regular trace-polynomial presentation. -/
def fixedSliceProjectiveChartEquivTrace :
    FixedSliceProjectiveChartAlgebra ≃ₐ[ℂ]
      (Polynomial ℂ ⧸ Ideal.span {fixedSliceTraceComplexPolynomial}) :=
  fixedSliceProjectiveChartEquivNormalized.trans fixedSliceNormalizedAffineChartEquivTrace

end
end Biunimodular.F11
