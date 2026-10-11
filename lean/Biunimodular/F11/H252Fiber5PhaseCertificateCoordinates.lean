/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber5PointVerified
import Biunimodular.F11.H252Fiber5LaurentRankCoordinates
import Biunimodular.F11.H252FiberPhaseReconstruction
import Biunimodular.F11.TorusFiberProjectionMembership

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
noncomputable section

private def fiber5ProjectionIdeal : Ideal H252LocalizedTorusAlgebra :=
  algebraProjectionIdeal (RingHom.id _) (h252FiberProjection 4)

private abbrev Fiber5ProjectionAlgebra := H252LocalizedTorusAlgebra ⧸ fiber5ProjectionIdeal

private def fiber5ProjectionMk : H252LocalizedTorusAlgebra →+* Fiber5ProjectionAlgebra :=
  Ideal.Quotient.mk fiber5ProjectionIdeal

private def fiber5ProjectionVar (i : Fin 7) : Fiber5ProjectionAlgebra :=
  fiber5ProjectionMk (h252LocalizedTorusVar i)

private theorem fiber5Projection_factor_zero :
    integerCoefficientEval (fiber5ProjectionVar 4) h252FiberCRTQ5 = 0 := by
  change integerCoefficientEval (fiber5ProjectionMk (h252LocalizedTorusVar 4)) _ = 0
  rw [← integerCoefficientEval_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change h252FiberProjection 4 *
    integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ5 = 0
  exact h252FiberProjection_annihilator 4

private theorem fiber5Projection_generators_zero :
    ∀ g ∈ h252Fiber5LaurentRankOriginalGenerators,
      rurInverseSparseEval g (fiber5ProjectionVar 0) (fiber5ProjectionVar 1)
        (fiber5ProjectionVar 2) (fiber5ProjectionVar 3) (fiber5ProjectionVar 5)
        (fiber5ProjectionVar 4) (fiber5ProjectionVar 6) = 0 := by
  intro g hg
  have hz : rurInverseSparseEval g (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1)
      (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5)
      (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
    simp only [h252Fiber5LaurentRankOriginalGenerators, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact rurInverseGenerator1_quotient_zero
    · exact rurInverseGenerator2_quotient_zero
    · exact rurInverseGenerator3_quotient_zero
    · exact rurInverseGenerator4_quotient_zero
    · exact rurInverseGenerator5_quotient_zero
  change rurInverseSparseEval g (fiber5ProjectionMk _) (fiber5ProjectionMk _)
    (fiber5ProjectionMk _) (fiber5ProjectionMk _) (fiber5ProjectionMk _)
    (fiber5ProjectionMk _) (fiber5ProjectionMk _) = 0
  rw [← rurInverseSparseEval_map, hz, map_zero]

private theorem localizedPhaseVar_isUnit (i : Fin 5) : IsUnit (h252LocalizedPhaseVars i) :=
  isUnit_iff_exists_inv.mpr ⟨h252LocalizedInverseVars i, h252LocalizedPhaseVars_units i⟩

private theorem fiber5Projection_units : ∀ j : Fin 4,
    IsUnit (![fiber5ProjectionVar 0,fiber5ProjectionVar 1,
      fiber5ProjectionVar 2,fiber5ProjectionVar 3] j) := by
  intro j
  have hu := (localizedPhaseVar_isUnit j.castSucc).map fiber5ProjectionMk
  fin_cases j <;> exact hu


private theorem fiber5Projection_phase_values :
    ∀ j : Fin 4, ![fiber5ProjectionVar 0,fiber5ProjectionVar 1,fiber5ProjectionVar 2,fiber5ProjectionVar 3] j =
      ![h252Fiber5Pointc1 (fiber5ProjectionVar 4),h252Fiber5Pointc2 (fiber5ProjectionVar 4),
        h252Fiber5Pointc3 (fiber5ProjectionVar 4),h252Fiber5Pointc4 (fiber5ProjectionVar 4)] j := by
  apply h252Fiber5LaurentRank_phase_unique (fiber5ProjectionVar 0) (fiber5ProjectionVar 1) (fiber5ProjectionVar 2) (fiber5ProjectionVar 3)
    (fiber5ProjectionVar 5) (h252Fiber5Pointc1 (fiber5ProjectionVar 4)) (h252Fiber5Pointc2 (fiber5ProjectionVar 4))
    (h252Fiber5Pointc3 (fiber5ProjectionVar 4)) (h252Fiber5Pointc4 (fiber5ProjectionVar 4)) 0 (fiber5ProjectionVar 4) (fiber5ProjectionVar 6)
    fiber5Projection_factor_zero fiber5Projection_generators_zero
  · intro g hg
    simp only [h252Fiber5LaurentRankOriginalGenerators, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact h252Fiber5PointG1_zero _ _ _ fiber5Projection_factor_zero
    · exact h252Fiber5PointG2_zero _ _ _ fiber5Projection_factor_zero
    · exact h252Fiber5PointG3_zero _ _ _ fiber5Projection_factor_zero
    · exact h252Fiber5PointG4_zero _ _ _ fiber5Projection_factor_zero
    · exact h252Fiber5PointG5_zero _ _ _ fiber5Projection_factor_zero
  · exact fiber5Projection_units
  · intro j
    fin_cases j
    · exact h252Fiber5Pointc1_isUnit _ fiber5Projection_factor_zero
    · exact h252Fiber5Pointc2_isUnit _ fiber5Projection_factor_zero
    · exact h252Fiber5Pointc3_isUnit _ fiber5Projection_factor_zero
    · exact h252Fiber5Pointc4_isUnit _ fiber5Projection_factor_zero

def h252Fiber5PhaseCertificateCoordinateScales : Fin 4 → ℤ := fun _ => h252Fiber5PointScale
def h252Fiber5PhaseCertificateCoordinateNumerators : Fin 4 → List ℤ :=
  ![h252Fiber5Pointc1Coeffs,h252Fiber5Pointc2Coeffs,h252Fiber5Pointc3Coeffs,h252Fiber5Pointc4Coeffs]
def h252Fiber5PhaseCertificateCoordinateRemainders (j : Fin 4) : List ℤ :=
  integerCoefficientScale (-1) (h252Fiber5PhaseCertificateCoordinateNumerators j)
theorem h252Fiber5PhaseCertificateCoordinate_positive : ∀ j, 0 < h252Fiber5PhaseCertificateCoordinateScales j := by
  intro j
  exact h252Fiber5PointScale_pos
theorem h252Fiber5PhaseCertificateCoordinate_projected (j : Fin 4) :
    h252FiberProjection 4 *
      ((h252Fiber5PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) *
        h252FiberCoordinateValues (j.castAdd 5) +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber5PhaseCertificateCoordinateRemainders j)) = 0 := by
  rw [h252FiberCoordinateValues_phase]
  have hz : fiber5ProjectionMk
      ((h252Fiber5PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) * h252LocalizedPhaseVars j.castSucc +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber5PhaseCertificateCoordinateRemainders j)) = 0 := by
    have he := integerCoefficientEval_map (R := H252LocalizedTorusAlgebra) (S := Fiber5ProjectionAlgebra) fiber5ProjectionMk (h252LocalizedTorusVar 4) (h252Fiber5PhaseCertificateCoordinateRemainders j)
    rw [map_add, map_mul, map_intCast, he]
    rw [h252Fiber5PhaseCertificateCoordinateRemainders, integerCoefficientEval_scale]
    simp only [Int.cast_neg, Int.cast_one]
    have h := fiber5Projection_phase_values j
    fin_cases j
    · change (h252Fiber5PointScale : Fiber5ProjectionAlgebra) * fiber5ProjectionVar 0 + (-1 : Fiber5ProjectionAlgebra) *
          integerCoefficientEval (fiber5ProjectionVar 4) h252Fiber5Pointc1Coeffs = 0
      change fiber5ProjectionVar 0 = h252Fiber5Pointc1 (fiber5ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber5ProjectionAlgebra) (fiber5ProjectionVar 4) h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc1Coeffs
      change (h252Fiber5PointScale : Fiber5ProjectionAlgebra) * h252Fiber5Pointc1 (fiber5ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber5PointScale : Fiber5ProjectionAlgebra) * fiber5ProjectionVar 1 + (-1 : Fiber5ProjectionAlgebra) *
          integerCoefficientEval (fiber5ProjectionVar 4) h252Fiber5Pointc2Coeffs = 0
      change fiber5ProjectionVar 1 = h252Fiber5Pointc2 (fiber5ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber5ProjectionAlgebra) (fiber5ProjectionVar 4) h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc2Coeffs
      change (h252Fiber5PointScale : Fiber5ProjectionAlgebra) * h252Fiber5Pointc2 (fiber5ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber5PointScale : Fiber5ProjectionAlgebra) * fiber5ProjectionVar 2 + (-1 : Fiber5ProjectionAlgebra) *
          integerCoefficientEval (fiber5ProjectionVar 4) h252Fiber5Pointc3Coeffs = 0
      change fiber5ProjectionVar 2 = h252Fiber5Pointc3 (fiber5ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber5ProjectionAlgebra) (fiber5ProjectionVar 4) h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc3Coeffs
      change (h252Fiber5PointScale : Fiber5ProjectionAlgebra) * h252Fiber5Pointc3 (fiber5ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber5PointScale : Fiber5ProjectionAlgebra) * fiber5ProjectionVar 3 + (-1 : Fiber5ProjectionAlgebra) *
          integerCoefficientEval (fiber5ProjectionVar 4) h252Fiber5Pointc4Coeffs = 0
      change fiber5ProjectionVar 3 = h252Fiber5Pointc4 (fiber5ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber5ProjectionAlgebra) (fiber5ProjectionVar 4) h252Fiber5PointScale (ne_of_gt h252Fiber5PointScale_pos) h252Fiber5Pointc4Coeffs
      change (h252Fiber5PointScale : Fiber5ProjectionAlgebra) * h252Fiber5Pointc4 (fiber5ProjectionVar 4) = _ at hs
      linear_combination hs
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end
end Biunimodular.F11
