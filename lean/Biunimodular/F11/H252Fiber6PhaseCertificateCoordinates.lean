/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6PointVerified
import Biunimodular.F11.H252Fiber6LaurentRankCoordinates
import Biunimodular.F11.H252FiberPhaseReconstruction
import Biunimodular.F11.TorusFiberProjectionMembership

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
noncomputable section

private def fiber6ProjectionIdeal : Ideal H252LocalizedTorusAlgebra :=
  algebraProjectionIdeal (RingHom.id _) (h252FiberProjection 5)

private abbrev Fiber6ProjectionAlgebra := H252LocalizedTorusAlgebra ⧸ fiber6ProjectionIdeal

private def fiber6ProjectionMk : H252LocalizedTorusAlgebra →+* Fiber6ProjectionAlgebra :=
  Ideal.Quotient.mk fiber6ProjectionIdeal

private def fiber6ProjectionVar (i : Fin 7) : Fiber6ProjectionAlgebra :=
  fiber6ProjectionMk (h252LocalizedTorusVar i)

private theorem fiber6Projection_factor_zero :
    integerCoefficientEval (fiber6ProjectionVar 4) h252FiberCRTQ6 = 0 := by
  change integerCoefficientEval (fiber6ProjectionMk (h252LocalizedTorusVar 4)) _ = 0
  rw [← integerCoefficientEval_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change h252FiberProjection 5 *
    integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ6 = 0
  exact h252FiberProjection_annihilator 5

private theorem fiber6Projection_generators_zero :
    ∀ g ∈ h252Fiber6LaurentRankOriginalGenerators,
      rurInverseSparseEval g (fiber6ProjectionVar 0) (fiber6ProjectionVar 1)
        (fiber6ProjectionVar 2) (fiber6ProjectionVar 3) (fiber6ProjectionVar 5)
        (fiber6ProjectionVar 4) (fiber6ProjectionVar 6) = 0 := by
  intro g hg
  have hz : rurInverseSparseEval g (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1)
      (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5)
      (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
    simp only [h252Fiber6LaurentRankOriginalGenerators, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact rurInverseGenerator1_quotient_zero
    · exact rurInverseGenerator2_quotient_zero
    · exact rurInverseGenerator3_quotient_zero
    · exact rurInverseGenerator4_quotient_zero
    · exact rurInverseGenerator5_quotient_zero
  change rurInverseSparseEval g (fiber6ProjectionMk _) (fiber6ProjectionMk _)
    (fiber6ProjectionMk _) (fiber6ProjectionMk _) (fiber6ProjectionMk _)
    (fiber6ProjectionMk _) (fiber6ProjectionMk _) = 0
  rw [← rurInverseSparseEval_map, hz, map_zero]

private theorem localizedPhaseVar_isUnit (i : Fin 5) : IsUnit (h252LocalizedPhaseVars i) :=
  isUnit_iff_exists_inv.mpr ⟨h252LocalizedInverseVars i, h252LocalizedPhaseVars_units i⟩

private theorem fiber6Projection_units : ∀ j : Fin 4,
    IsUnit (![fiber6ProjectionVar 0,fiber6ProjectionVar 1,
      fiber6ProjectionVar 2,fiber6ProjectionVar 3] j) := by
  intro j
  have hu := (localizedPhaseVar_isUnit j.castSucc).map fiber6ProjectionMk
  fin_cases j <;> exact hu


private theorem fiber6Projection_phase_values :
    ∀ j : Fin 4, ![fiber6ProjectionVar 0,fiber6ProjectionVar 1,fiber6ProjectionVar 2,fiber6ProjectionVar 3] j =
      ![h252Fiber6Pointc1 (fiber6ProjectionVar 4),h252Fiber6Pointc2 (fiber6ProjectionVar 4),
        h252Fiber6Pointc3 (fiber6ProjectionVar 4),h252Fiber6Pointc4 (fiber6ProjectionVar 4)] j := by
  apply h252Fiber6LaurentRank_phase_unique (fiber6ProjectionVar 0) (fiber6ProjectionVar 1) (fiber6ProjectionVar 2) (fiber6ProjectionVar 3)
    (fiber6ProjectionVar 5) (h252Fiber6Pointc1 (fiber6ProjectionVar 4)) (h252Fiber6Pointc2 (fiber6ProjectionVar 4))
    (h252Fiber6Pointc3 (fiber6ProjectionVar 4)) (h252Fiber6Pointc4 (fiber6ProjectionVar 4)) 0 (fiber6ProjectionVar 4) (fiber6ProjectionVar 6)
    fiber6Projection_factor_zero fiber6Projection_generators_zero
  · intro g hg
    simp only [h252Fiber6LaurentRankOriginalGenerators, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact h252Fiber6PointG1_zero _ _ _ fiber6Projection_factor_zero
    · exact h252Fiber6PointG2_zero _ _ _ fiber6Projection_factor_zero
    · exact h252Fiber6PointG3_zero _ _ _ fiber6Projection_factor_zero
    · exact h252Fiber6PointG4_zero _ _ _ fiber6Projection_factor_zero
    · exact h252Fiber6PointG5_zero _ _ _ fiber6Projection_factor_zero
  · exact fiber6Projection_units
  · intro j
    fin_cases j
    · exact h252Fiber6Pointc1_isUnit _ fiber6Projection_factor_zero
    · exact h252Fiber6Pointc2_isUnit _ fiber6Projection_factor_zero
    · exact h252Fiber6Pointc3_isUnit _ fiber6Projection_factor_zero
    · exact h252Fiber6Pointc4_isUnit _ fiber6Projection_factor_zero

def h252Fiber6PhaseCertificateCoordinateScales : Fin 4 → ℤ := fun _ => h252Fiber6PointScale
def h252Fiber6PhaseCertificateCoordinateNumerators : Fin 4 → List ℤ :=
  ![h252Fiber6Pointc1Coeffs,h252Fiber6Pointc2Coeffs,h252Fiber6Pointc3Coeffs,h252Fiber6Pointc4Coeffs]
def h252Fiber6PhaseCertificateCoordinateRemainders (j : Fin 4) : List ℤ :=
  integerCoefficientScale (-1) (h252Fiber6PhaseCertificateCoordinateNumerators j)
theorem h252Fiber6PhaseCertificateCoordinate_positive : ∀ j, 0 < h252Fiber6PhaseCertificateCoordinateScales j := by
  intro j
  exact h252Fiber6PointScale_pos
theorem h252Fiber6PhaseCertificateCoordinate_projected (j : Fin 4) :
    h252FiberProjection 5 *
      ((h252Fiber6PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) *
        h252FiberCoordinateValues (j.castAdd 5) +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber6PhaseCertificateCoordinateRemainders j)) = 0 := by
  rw [h252FiberCoordinateValues_phase]
  have hz : fiber6ProjectionMk
      ((h252Fiber6PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) * h252LocalizedPhaseVars j.castSucc +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber6PhaseCertificateCoordinateRemainders j)) = 0 := by
    have he := integerCoefficientEval_map (R := H252LocalizedTorusAlgebra) (S := Fiber6ProjectionAlgebra) fiber6ProjectionMk (h252LocalizedTorusVar 4) (h252Fiber6PhaseCertificateCoordinateRemainders j)
    rw [map_add, map_mul, map_intCast, he]
    rw [h252Fiber6PhaseCertificateCoordinateRemainders, integerCoefficientEval_scale]
    simp only [Int.cast_neg, Int.cast_one]
    have h := fiber6Projection_phase_values j
    fin_cases j
    · change (h252Fiber6PointScale : Fiber6ProjectionAlgebra) * fiber6ProjectionVar 0 + (-1 : Fiber6ProjectionAlgebra) *
          integerCoefficientEval (fiber6ProjectionVar 4) h252Fiber6Pointc1Coeffs = 0
      change fiber6ProjectionVar 0 = h252Fiber6Pointc1 (fiber6ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber6ProjectionAlgebra) (fiber6ProjectionVar 4) h252Fiber6PointScale (ne_of_gt h252Fiber6PointScale_pos) h252Fiber6Pointc1Coeffs
      change (h252Fiber6PointScale : Fiber6ProjectionAlgebra) * h252Fiber6Pointc1 (fiber6ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber6PointScale : Fiber6ProjectionAlgebra) * fiber6ProjectionVar 1 + (-1 : Fiber6ProjectionAlgebra) *
          integerCoefficientEval (fiber6ProjectionVar 4) h252Fiber6Pointc2Coeffs = 0
      change fiber6ProjectionVar 1 = h252Fiber6Pointc2 (fiber6ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber6ProjectionAlgebra) (fiber6ProjectionVar 4) h252Fiber6PointScale (ne_of_gt h252Fiber6PointScale_pos) h252Fiber6Pointc2Coeffs
      change (h252Fiber6PointScale : Fiber6ProjectionAlgebra) * h252Fiber6Pointc2 (fiber6ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber6PointScale : Fiber6ProjectionAlgebra) * fiber6ProjectionVar 2 + (-1 : Fiber6ProjectionAlgebra) *
          integerCoefficientEval (fiber6ProjectionVar 4) h252Fiber6Pointc3Coeffs = 0
      change fiber6ProjectionVar 2 = h252Fiber6Pointc3 (fiber6ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber6ProjectionAlgebra) (fiber6ProjectionVar 4) h252Fiber6PointScale (ne_of_gt h252Fiber6PointScale_pos) h252Fiber6Pointc3Coeffs
      change (h252Fiber6PointScale : Fiber6ProjectionAlgebra) * h252Fiber6Pointc3 (fiber6ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber6PointScale : Fiber6ProjectionAlgebra) * fiber6ProjectionVar 3 + (-1 : Fiber6ProjectionAlgebra) *
          integerCoefficientEval (fiber6ProjectionVar 4) h252Fiber6Pointc4Coeffs = 0
      change fiber6ProjectionVar 3 = h252Fiber6Pointc4 (fiber6ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber6ProjectionAlgebra) (fiber6ProjectionVar 4) h252Fiber6PointScale (ne_of_gt h252Fiber6PointScale_pos) h252Fiber6Pointc4Coeffs
      change (h252Fiber6PointScale : Fiber6ProjectionAlgebra) * h252Fiber6Pointc4 (fiber6ProjectionVar 4) = _ at hs
      linear_combination hs
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end
end Biunimodular.F11
