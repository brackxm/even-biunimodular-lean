/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4PointVerified
import Biunimodular.F11.H252Fiber4LaurentRankCoordinates
import Biunimodular.F11.H252FiberPhaseReconstruction
import Biunimodular.F11.TorusFiberProjectionMembership

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
noncomputable section

private def fiber4ProjectionIdeal : Ideal H252LocalizedTorusAlgebra :=
  algebraProjectionIdeal (RingHom.id _) (h252FiberProjection 3)

private abbrev Fiber4ProjectionAlgebra := H252LocalizedTorusAlgebra ⧸ fiber4ProjectionIdeal

private def fiber4ProjectionMk : H252LocalizedTorusAlgebra →+* Fiber4ProjectionAlgebra :=
  Ideal.Quotient.mk fiber4ProjectionIdeal

private def fiber4ProjectionVar (i : Fin 7) : Fiber4ProjectionAlgebra :=
  fiber4ProjectionMk (h252LocalizedTorusVar i)

private theorem fiber4Projection_factor_zero :
    integerCoefficientEval (fiber4ProjectionVar 4) h252FiberCRTQ4 = 0 := by
  change integerCoefficientEval (fiber4ProjectionMk (h252LocalizedTorusVar 4)) _ = 0
  rw [← integerCoefficientEval_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change h252FiberProjection 3 *
    integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ4 = 0
  exact h252FiberProjection_annihilator 3

private theorem fiber4Projection_generators_zero :
    ∀ g ∈ h252Fiber4LaurentRankOriginalGenerators,
      rurInverseSparseEval g (fiber4ProjectionVar 0) (fiber4ProjectionVar 1)
        (fiber4ProjectionVar 2) (fiber4ProjectionVar 3) (fiber4ProjectionVar 5)
        (fiber4ProjectionVar 4) (fiber4ProjectionVar 6) = 0 := by
  intro g hg
  have hz : rurInverseSparseEval g (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1)
      (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5)
      (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
    simp only [h252Fiber4LaurentRankOriginalGenerators, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact rurInverseGenerator1_quotient_zero
    · exact rurInverseGenerator2_quotient_zero
    · exact rurInverseGenerator3_quotient_zero
    · exact rurInverseGenerator4_quotient_zero
    · exact rurInverseGenerator5_quotient_zero
  change rurInverseSparseEval g (fiber4ProjectionMk _) (fiber4ProjectionMk _)
    (fiber4ProjectionMk _) (fiber4ProjectionMk _) (fiber4ProjectionMk _)
    (fiber4ProjectionMk _) (fiber4ProjectionMk _) = 0
  rw [← rurInverseSparseEval_map, hz, map_zero]

private theorem localizedPhaseVar_isUnit (i : Fin 5) : IsUnit (h252LocalizedPhaseVars i) :=
  isUnit_iff_exists_inv.mpr ⟨h252LocalizedInverseVars i, h252LocalizedPhaseVars_units i⟩

private theorem fiber4Projection_units : ∀ j : Fin 4,
    IsUnit (![fiber4ProjectionVar 0,fiber4ProjectionVar 1,
      fiber4ProjectionVar 2,fiber4ProjectionVar 3] j) := by
  intro j
  have hu := (localizedPhaseVar_isUnit j.castSucc).map fiber4ProjectionMk
  fin_cases j <;> exact hu


private theorem fiber4Projection_phase_values :
    ∀ j : Fin 4, ![fiber4ProjectionVar 0,fiber4ProjectionVar 1,fiber4ProjectionVar 2,fiber4ProjectionVar 3] j =
      ![h252Fiber4Pointc1 (fiber4ProjectionVar 4),h252Fiber4Pointc2 (fiber4ProjectionVar 4),
        h252Fiber4Pointc3 (fiber4ProjectionVar 4),h252Fiber4Pointc4 (fiber4ProjectionVar 4)] j := by
  apply h252Fiber4LaurentRank_phase_unique (fiber4ProjectionVar 0) (fiber4ProjectionVar 1) (fiber4ProjectionVar 2) (fiber4ProjectionVar 3)
    (fiber4ProjectionVar 5) (h252Fiber4Pointc1 (fiber4ProjectionVar 4)) (h252Fiber4Pointc2 (fiber4ProjectionVar 4))
    (h252Fiber4Pointc3 (fiber4ProjectionVar 4)) (h252Fiber4Pointc4 (fiber4ProjectionVar 4)) 0 (fiber4ProjectionVar 4) (fiber4ProjectionVar 6)
    fiber4Projection_factor_zero fiber4Projection_generators_zero
  · intro g hg
    simp only [h252Fiber4LaurentRankOriginalGenerators, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact h252Fiber4PointG1_zero _ _ _ fiber4Projection_factor_zero
    · exact h252Fiber4PointG2_zero _ _ _ fiber4Projection_factor_zero
    · exact h252Fiber4PointG3_zero _ _ _ fiber4Projection_factor_zero
    · exact h252Fiber4PointG4_zero _ _ _ fiber4Projection_factor_zero
    · exact h252Fiber4PointG5_zero _ _ _ fiber4Projection_factor_zero
  · exact fiber4Projection_units
  · intro j
    fin_cases j
    · exact h252Fiber4Pointc1_isUnit _ fiber4Projection_factor_zero
    · exact h252Fiber4Pointc2_isUnit _ fiber4Projection_factor_zero
    · exact h252Fiber4Pointc3_isUnit _ fiber4Projection_factor_zero
    · exact h252Fiber4Pointc4_isUnit _ fiber4Projection_factor_zero

def h252Fiber4PhaseCertificateCoordinateScales : Fin 4 → ℤ := fun _ => h252Fiber4PointScale
def h252Fiber4PhaseCertificateCoordinateNumerators : Fin 4 → List ℤ :=
  ![h252Fiber4Pointc1Coeffs,h252Fiber4Pointc2Coeffs,h252Fiber4Pointc3Coeffs,h252Fiber4Pointc4Coeffs]
def h252Fiber4PhaseCertificateCoordinateRemainders (j : Fin 4) : List ℤ :=
  integerCoefficientScale (-1) (h252Fiber4PhaseCertificateCoordinateNumerators j)
theorem h252Fiber4PhaseCertificateCoordinate_positive : ∀ j, 0 < h252Fiber4PhaseCertificateCoordinateScales j := by
  intro j
  exact h252Fiber4PointScale_pos
theorem h252Fiber4PhaseCertificateCoordinate_projected (j : Fin 4) :
    h252FiberProjection 3 *
      ((h252Fiber4PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) *
        h252FiberCoordinateValues (j.castAdd 5) +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber4PhaseCertificateCoordinateRemainders j)) = 0 := by
  rw [h252FiberCoordinateValues_phase]
  have hz : fiber4ProjectionMk
      ((h252Fiber4PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) * h252LocalizedPhaseVars j.castSucc +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber4PhaseCertificateCoordinateRemainders j)) = 0 := by
    have he := integerCoefficientEval_map (R := H252LocalizedTorusAlgebra) (S := Fiber4ProjectionAlgebra) fiber4ProjectionMk (h252LocalizedTorusVar 4) (h252Fiber4PhaseCertificateCoordinateRemainders j)
    rw [map_add, map_mul, map_intCast, he]
    rw [h252Fiber4PhaseCertificateCoordinateRemainders, integerCoefficientEval_scale]
    simp only [Int.cast_neg, Int.cast_one]
    have h := fiber4Projection_phase_values j
    fin_cases j
    · change (h252Fiber4PointScale : Fiber4ProjectionAlgebra) * fiber4ProjectionVar 0 + (-1 : Fiber4ProjectionAlgebra) *
          integerCoefficientEval (fiber4ProjectionVar 4) h252Fiber4Pointc1Coeffs = 0
      change fiber4ProjectionVar 0 = h252Fiber4Pointc1 (fiber4ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber4ProjectionAlgebra) (fiber4ProjectionVar 4) h252Fiber4PointScale (ne_of_gt h252Fiber4PointScale_pos) h252Fiber4Pointc1Coeffs
      change (h252Fiber4PointScale : Fiber4ProjectionAlgebra) * h252Fiber4Pointc1 (fiber4ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber4PointScale : Fiber4ProjectionAlgebra) * fiber4ProjectionVar 1 + (-1 : Fiber4ProjectionAlgebra) *
          integerCoefficientEval (fiber4ProjectionVar 4) h252Fiber4Pointc2Coeffs = 0
      change fiber4ProjectionVar 1 = h252Fiber4Pointc2 (fiber4ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber4ProjectionAlgebra) (fiber4ProjectionVar 4) h252Fiber4PointScale (ne_of_gt h252Fiber4PointScale_pos) h252Fiber4Pointc2Coeffs
      change (h252Fiber4PointScale : Fiber4ProjectionAlgebra) * h252Fiber4Pointc2 (fiber4ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber4PointScale : Fiber4ProjectionAlgebra) * fiber4ProjectionVar 2 + (-1 : Fiber4ProjectionAlgebra) *
          integerCoefficientEval (fiber4ProjectionVar 4) h252Fiber4Pointc3Coeffs = 0
      change fiber4ProjectionVar 2 = h252Fiber4Pointc3 (fiber4ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber4ProjectionAlgebra) (fiber4ProjectionVar 4) h252Fiber4PointScale (ne_of_gt h252Fiber4PointScale_pos) h252Fiber4Pointc3Coeffs
      change (h252Fiber4PointScale : Fiber4ProjectionAlgebra) * h252Fiber4Pointc3 (fiber4ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber4PointScale : Fiber4ProjectionAlgebra) * fiber4ProjectionVar 3 + (-1 : Fiber4ProjectionAlgebra) *
          integerCoefficientEval (fiber4ProjectionVar 4) h252Fiber4Pointc4Coeffs = 0
      change fiber4ProjectionVar 3 = h252Fiber4Pointc4 (fiber4ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber4ProjectionAlgebra) (fiber4ProjectionVar 4) h252Fiber4PointScale (ne_of_gt h252Fiber4PointScale_pos) h252Fiber4Pointc4Coeffs
      change (h252Fiber4PointScale : Fiber4ProjectionAlgebra) * h252Fiber4Pointc4 (fiber4ProjectionVar 4) = _ at hs
      linear_combination hs
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end
end Biunimodular.F11
