/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3PointVerified
import Biunimodular.F11.H252Fiber3LaurentRankCoordinates
import Biunimodular.F11.H252FiberPhaseReconstruction
import Biunimodular.F11.TorusFiberProjectionMembership

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

private def fiber3ProjectionIdeal : Ideal H252LocalizedTorusAlgebra :=
  algebraProjectionIdeal (RingHom.id _) (h252FiberProjection 2)

private abbrev Fiber3ProjectionAlgebra := H252LocalizedTorusAlgebra ⧸ fiber3ProjectionIdeal

private def fiber3ProjectionMk : H252LocalizedTorusAlgebra →+* Fiber3ProjectionAlgebra :=
  Ideal.Quotient.mk fiber3ProjectionIdeal

private def fiber3ProjectionVar (i : Fin 7) : Fiber3ProjectionAlgebra :=
  fiber3ProjectionMk (h252LocalizedTorusVar i)

private theorem fiber3Projection_factor_zero :
    integerCoefficientEval (fiber3ProjectionVar 4) h252FiberCRTQ3 = 0 := by
  change integerCoefficientEval (fiber3ProjectionMk (h252LocalizedTorusVar 4)) _ = 0
  rw [← integerCoefficientEval_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change h252FiberProjection 2 *
    integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ3 = 0
  exact h252FiberProjection_annihilator 2

private theorem fiber3Projection_generators_zero :
    ∀ g ∈ h252Fiber3LaurentRankOriginalGenerators,
      rurInverseSparseEval g (fiber3ProjectionVar 0) (fiber3ProjectionVar 1)
        (fiber3ProjectionVar 2) (fiber3ProjectionVar 3) (fiber3ProjectionVar 5)
        (fiber3ProjectionVar 4) (fiber3ProjectionVar 6) = 0 := by
  intro g hg
  have hz : rurInverseSparseEval g (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1)
      (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5)
      (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
    simp only [h252Fiber3LaurentRankOriginalGenerators, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact rurInverseGenerator1_quotient_zero
    · exact rurInverseGenerator2_quotient_zero
    · exact rurInverseGenerator3_quotient_zero
    · exact rurInverseGenerator4_quotient_zero
    · exact rurInverseGenerator5_quotient_zero
  change rurInverseSparseEval g (fiber3ProjectionMk _) (fiber3ProjectionMk _)
    (fiber3ProjectionMk _) (fiber3ProjectionMk _) (fiber3ProjectionMk _)
    (fiber3ProjectionMk _) (fiber3ProjectionMk _) = 0
  rw [← rurInverseSparseEval_map, hz, map_zero]

private theorem localizedPhaseVar_isUnit (i : Fin 5) : IsUnit (h252LocalizedPhaseVars i) :=
  isUnit_iff_exists_inv.mpr ⟨h252LocalizedInverseVars i, h252LocalizedPhaseVars_units i⟩

private theorem fiber3Projection_units : ∀ j : Fin 4,
    IsUnit (![fiber3ProjectionVar 0,fiber3ProjectionVar 1,
      fiber3ProjectionVar 2,fiber3ProjectionVar 3] j) := by
  intro j
  have hu := (localizedPhaseVar_isUnit j.castSucc).map fiber3ProjectionMk
  fin_cases j <;> exact hu


private theorem fiber3Projection_phase_values :
    ∀ j : Fin 4, ![fiber3ProjectionVar 0,fiber3ProjectionVar 1,fiber3ProjectionVar 2,fiber3ProjectionVar 3] j =
      ![h252Fiber3Pointc1 (fiber3ProjectionVar 4),h252Fiber3Pointc2 (fiber3ProjectionVar 4),
        h252Fiber3Pointc3 (fiber3ProjectionVar 4),h252Fiber3Pointc4 (fiber3ProjectionVar 4)] j := by
  apply h252Fiber3LaurentRank_phase_unique (fiber3ProjectionVar 0) (fiber3ProjectionVar 1) (fiber3ProjectionVar 2) (fiber3ProjectionVar 3)
    (fiber3ProjectionVar 5) (h252Fiber3Pointc1 (fiber3ProjectionVar 4)) (h252Fiber3Pointc2 (fiber3ProjectionVar 4))
    (h252Fiber3Pointc3 (fiber3ProjectionVar 4)) (h252Fiber3Pointc4 (fiber3ProjectionVar 4)) 0 (fiber3ProjectionVar 4) (fiber3ProjectionVar 6)
    fiber3Projection_factor_zero fiber3Projection_generators_zero
  · intro g hg
    simp only [h252Fiber3LaurentRankOriginalGenerators, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact h252Fiber3PointG1_zero _ _ _ fiber3Projection_factor_zero
    · exact h252Fiber3PointG2_zero _ _ _ fiber3Projection_factor_zero
    · exact h252Fiber3PointG3_zero _ _ _ fiber3Projection_factor_zero
    · exact h252Fiber3PointG4_zero _ _ _ fiber3Projection_factor_zero
    · exact h252Fiber3PointG5_zero _ _ _ fiber3Projection_factor_zero
  · exact fiber3Projection_units
  · intro j
    fin_cases j
    · exact h252Fiber3Pointc1_isUnit _ fiber3Projection_factor_zero
    · exact h252Fiber3Pointc2_isUnit _ fiber3Projection_factor_zero
    · exact h252Fiber3Pointc3_isUnit _ fiber3Projection_factor_zero
    · exact h252Fiber3Pointc4_isUnit _ fiber3Projection_factor_zero

def h252Fiber3PhaseCertificateCoordinateScales : Fin 4 → ℤ := fun _ => h252Fiber3PointScale
def h252Fiber3PhaseCertificateCoordinateNumerators : Fin 4 → List ℤ :=
  ![h252Fiber3Pointc1Coeffs,h252Fiber3Pointc2Coeffs,h252Fiber3Pointc3Coeffs,h252Fiber3Pointc4Coeffs]
def h252Fiber3PhaseCertificateCoordinateRemainders (j : Fin 4) : List ℤ :=
  integerCoefficientScale (-1) (h252Fiber3PhaseCertificateCoordinateNumerators j)
theorem h252Fiber3PhaseCertificateCoordinate_positive : ∀ j, 0 < h252Fiber3PhaseCertificateCoordinateScales j := by
  intro j
  exact h252Fiber3PointScale_pos
theorem h252Fiber3PhaseCertificateCoordinate_projected (j : Fin 4) :
    h252FiberProjection 2 *
      ((h252Fiber3PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) *
        h252FiberCoordinateValues (j.castAdd 5) +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber3PhaseCertificateCoordinateRemainders j)) = 0 := by
  rw [h252FiberCoordinateValues_phase]
  have hz : fiber3ProjectionMk
      ((h252Fiber3PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) * h252LocalizedPhaseVars j.castSucc +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber3PhaseCertificateCoordinateRemainders j)) = 0 := by
    have he := integerCoefficientEval_map (R := H252LocalizedTorusAlgebra) (S := Fiber3ProjectionAlgebra) fiber3ProjectionMk (h252LocalizedTorusVar 4) (h252Fiber3PhaseCertificateCoordinateRemainders j)
    rw [map_add, map_mul, map_intCast, he]
    rw [h252Fiber3PhaseCertificateCoordinateRemainders, integerCoefficientEval_scale]
    simp only [Int.cast_neg, Int.cast_one]
    have h := fiber3Projection_phase_values j
    fin_cases j
    · change (h252Fiber3PointScale : Fiber3ProjectionAlgebra) * fiber3ProjectionVar 0 + (-1 : Fiber3ProjectionAlgebra) *
          integerCoefficientEval (fiber3ProjectionVar 4) h252Fiber3Pointc1Coeffs = 0
      change fiber3ProjectionVar 0 = h252Fiber3Pointc1 (fiber3ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber3ProjectionAlgebra) (fiber3ProjectionVar 4) h252Fiber3PointScale (ne_of_gt h252Fiber3PointScale_pos) h252Fiber3Pointc1Coeffs
      change (h252Fiber3PointScale : Fiber3ProjectionAlgebra) * h252Fiber3Pointc1 (fiber3ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber3PointScale : Fiber3ProjectionAlgebra) * fiber3ProjectionVar 1 + (-1 : Fiber3ProjectionAlgebra) *
          integerCoefficientEval (fiber3ProjectionVar 4) h252Fiber3Pointc2Coeffs = 0
      change fiber3ProjectionVar 1 = h252Fiber3Pointc2 (fiber3ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber3ProjectionAlgebra) (fiber3ProjectionVar 4) h252Fiber3PointScale (ne_of_gt h252Fiber3PointScale_pos) h252Fiber3Pointc2Coeffs
      change (h252Fiber3PointScale : Fiber3ProjectionAlgebra) * h252Fiber3Pointc2 (fiber3ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber3PointScale : Fiber3ProjectionAlgebra) * fiber3ProjectionVar 2 + (-1 : Fiber3ProjectionAlgebra) *
          integerCoefficientEval (fiber3ProjectionVar 4) h252Fiber3Pointc3Coeffs = 0
      change fiber3ProjectionVar 2 = h252Fiber3Pointc3 (fiber3ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber3ProjectionAlgebra) (fiber3ProjectionVar 4) h252Fiber3PointScale (ne_of_gt h252Fiber3PointScale_pos) h252Fiber3Pointc3Coeffs
      change (h252Fiber3PointScale : Fiber3ProjectionAlgebra) * h252Fiber3Pointc3 (fiber3ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber3PointScale : Fiber3ProjectionAlgebra) * fiber3ProjectionVar 3 + (-1 : Fiber3ProjectionAlgebra) *
          integerCoefficientEval (fiber3ProjectionVar 4) h252Fiber3Pointc4Coeffs = 0
      change fiber3ProjectionVar 3 = h252Fiber3Pointc4 (fiber3ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber3ProjectionAlgebra) (fiber3ProjectionVar 4) h252Fiber3PointScale (ne_of_gt h252Fiber3PointScale_pos) h252Fiber3Pointc4Coeffs
      change (h252Fiber3PointScale : Fiber3ProjectionAlgebra) * h252Fiber3Pointc4 (fiber3ProjectionVar 4) = _ at hs
      linear_combination hs
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end
end Biunimodular.F11
