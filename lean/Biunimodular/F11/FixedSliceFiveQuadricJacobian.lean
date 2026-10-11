/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.EtaleSquarePresentation
import Biunimodular.F11.FixedSliceProjectiveChartAlgebra
import Mathlib.RingTheory.Smooth.StandardSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

/-- The original normalized homogeneous equation dehomogenized in the
certified affine coordinate order. -/
def fixedSliceFiveChartRelation (i : Fin 5) : FixedSliceFivePolynomial :=
  fixedSliceHomogeneousAffineMap
    (fixedSliceHomogeneousQuadric even11FourierNormalized i.succ)

theorem fixedSliceFiveChartRelationIdeal_eq :
    Ideal.span (Set.range fixedSliceFiveChartRelation) =
      RedundantCoordinate.baseIdeal
        (even11FixedSliceHomogeneousGenerators.map fixedSliceHomogeneousAffineMap) := by
  unfold RedundantCoordinate.baseIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_ofPred_eq, even11FixedSliceHomogeneousGenerators,
    fixedSliceHomogeneousGenerators, List.map_ofFn, List.mem_ofFn,
    Function.comp_apply, fixedSliceFiveChartRelation]

abbrev FixedSliceFiveChartPresentationAlgebra :=
  FixedSliceFivePolynomial ⧸ Ideal.span (Set.range fixedSliceFiveChartRelation)

def fixedSliceFiveChartPresentationEquivNormalized :
    FixedSliceFiveChartPresentationAlgebra ≃ₐ[ℂ] FixedSliceNormalizedAffineChartAlgebra :=
  Ideal.quotientEquivAlgOfEq ℂ fixedSliceFiveChartRelationIdeal_eq

instance fixedSliceFiveChartPresentation_etale : Algebra.Etale ℂ FixedSliceFiveChartPresentationAlgebra :=
  Algebra.Etale.of_equiv fixedSliceFiveChartPresentationEquivNormalized.symm

instance fixedSliceFiveChartPresentation_moduleFinite :
    Module.Finite ℂ FixedSliceFiveChartPresentationAlgebra :=
  Module.Finite.equiv fixedSliceFiveChartPresentationEquivNormalized.toLinearEquiv.symm

instance fixedSliceFiveChartPresentation_noetherian :
    IsNoetherianRing FixedSliceFiveChartPresentationAlgebra := by
  let : IsArtinianRing FixedSliceFiveChartPresentationAlgebra :=
    IsArtinianRing.of_finite ℂ _
  infer_instance

/-- The square presentation uses exactly the original five equations in
the five affine variables. -/
def fixedSliceFiveQuadricPrePresentation :
    Algebra.PreSubmersivePresentation ℂ FixedSliceFiveChartPresentationAlgebra (Fin 5) (Fin 5) :=
  Algebra.PreSubmersivePresentation.naive (v := fixedSliceFiveChartRelation)
    _root_.id Function.injective_id

theorem fixedSliceFiveQuadricJacobian_isUnit :
    IsUnit fixedSliceFiveQuadricPrePresentation.jacobian :=
  etaleSquarePresentation_jacobian_isUnit fixedSliceFiveQuadricPrePresentation rfl

/-- The original five equations form a nonsingular square presentation of
the chart, with an invertible five-by-five Jacobian in its coordinate ring. -/
def fixedSliceFiveQuadricSubmersivePresentation :
    Algebra.SubmersivePresentation ℂ FixedSliceFiveChartPresentationAlgebra (Fin 5) (Fin 5) where
  __ := fixedSliceFiveQuadricPrePresentation
  jacobian_isUnit := fixedSliceFiveQuadricJacobian_isUnit

theorem fixedSliceFiveQuadricSubmersivePresentation_relations (i : Fin 5) :
    fixedSliceFiveQuadricSubmersivePresentation.relation i = fixedSliceFiveChartRelation i := rfl

instance fixedSliceFiveQuadric_standardSmoothDimensionZero :
    Algebra.IsStandardSmoothOfRelativeDimension 0 ℂ FixedSliceFiveChartPresentationAlgebra :=
  fixedSliceFiveQuadricSubmersivePresentation.isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

end
end Biunimodular.F11
