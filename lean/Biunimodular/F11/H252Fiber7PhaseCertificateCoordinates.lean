/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7PointVerified
import Biunimodular.F11.H252Fiber7LaurentRankCoordinates
import Biunimodular.F11.H252FiberPhaseReconstruction
import Biunimodular.F11.TorusFiberProjectionMembership

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
noncomputable section

private def fiber7ProjectionIdeal : Ideal H252LocalizedTorusAlgebra :=
  algebraProjectionIdeal (RingHom.id _) (h252FiberProjection 6)

private abbrev Fiber7ProjectionAlgebra := H252LocalizedTorusAlgebra ⧸ fiber7ProjectionIdeal

private def fiber7ProjectionMk : H252LocalizedTorusAlgebra →+* Fiber7ProjectionAlgebra :=
  Ideal.Quotient.mk fiber7ProjectionIdeal

private def fiber7ProjectionVar (i : Fin 7) : Fiber7ProjectionAlgebra :=
  fiber7ProjectionMk (h252LocalizedTorusVar i)

private theorem fiber7Projection_factor_zero :
    integerCoefficientEval (fiber7ProjectionVar 4) h252FiberCRTQ7 = 0 := by
  change integerCoefficientEval (fiber7ProjectionMk (h252LocalizedTorusVar 4)) _ = 0
  rw [← integerCoefficientEval_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change h252FiberProjection 6 *
    integerCoefficientEval (h252LocalizedTorusVar 4) h252FiberCRTQ7 = 0
  exact h252FiberProjection_annihilator 6

private theorem fiber7Projection_generators_zero :
    ∀ g ∈ h252Fiber7LaurentRankOriginalGenerators,
      rurInverseSparseEval g (fiber7ProjectionVar 0) (fiber7ProjectionVar 1)
        (fiber7ProjectionVar 2) (fiber7ProjectionVar 3) (fiber7ProjectionVar 5)
        (fiber7ProjectionVar 4) (fiber7ProjectionVar 6) = 0 := by
  intro g hg
  have hz : rurInverseSparseEval g (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1)
      (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5)
      (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
    simp only [h252Fiber7LaurentRankOriginalGenerators, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact rurInverseGenerator1_quotient_zero
    · exact rurInverseGenerator2_quotient_zero
    · exact rurInverseGenerator3_quotient_zero
    · exact rurInverseGenerator4_quotient_zero
    · exact rurInverseGenerator5_quotient_zero
  change rurInverseSparseEval g (fiber7ProjectionMk _) (fiber7ProjectionMk _)
    (fiber7ProjectionMk _) (fiber7ProjectionMk _) (fiber7ProjectionMk _)
    (fiber7ProjectionMk _) (fiber7ProjectionMk _) = 0
  rw [← rurInverseSparseEval_map, hz, map_zero]

private theorem localizedPhaseVar_isUnit (i : Fin 5) : IsUnit (h252LocalizedPhaseVars i) :=
  isUnit_iff_exists_inv.mpr ⟨h252LocalizedInverseVars i, h252LocalizedPhaseVars_units i⟩

private theorem fiber7Projection_units : ∀ j : Fin 4,
    IsUnit (![fiber7ProjectionVar 0,fiber7ProjectionVar 1,
      fiber7ProjectionVar 2,fiber7ProjectionVar 3] j) := by
  intro j
  have hu := (localizedPhaseVar_isUnit j.castSucc).map fiber7ProjectionMk
  fin_cases j <;> exact hu


private theorem fiber7Projection_phase_values :
    ∀ j : Fin 4, ![fiber7ProjectionVar 0,fiber7ProjectionVar 1,fiber7ProjectionVar 2,fiber7ProjectionVar 3] j =
      ![h252Fiber7Pointc1 (fiber7ProjectionVar 4),h252Fiber7Pointc2 (fiber7ProjectionVar 4),
        h252Fiber7Pointc3 (fiber7ProjectionVar 4),h252Fiber7Pointc4 (fiber7ProjectionVar 4)] j := by
  apply h252Fiber7LaurentRank_phase_unique (fiber7ProjectionVar 0) (fiber7ProjectionVar 1) (fiber7ProjectionVar 2) (fiber7ProjectionVar 3)
    (fiber7ProjectionVar 5) (h252Fiber7Pointc1 (fiber7ProjectionVar 4)) (h252Fiber7Pointc2 (fiber7ProjectionVar 4))
    (h252Fiber7Pointc3 (fiber7ProjectionVar 4)) (h252Fiber7Pointc4 (fiber7ProjectionVar 4)) 0 (fiber7ProjectionVar 4) (fiber7ProjectionVar 6)
    fiber7Projection_factor_zero fiber7Projection_generators_zero
  · intro g hg
    simp only [h252Fiber7LaurentRankOriginalGenerators, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact h252Fiber7PointG1_zero _ _ _ fiber7Projection_factor_zero
    · exact h252Fiber7PointG2_zero _ _ _ fiber7Projection_factor_zero
    · exact h252Fiber7PointG3_zero _ _ _ fiber7Projection_factor_zero
    · exact h252Fiber7PointG4_zero _ _ _ fiber7Projection_factor_zero
    · exact h252Fiber7PointG5_zero _ _ _ fiber7Projection_factor_zero
  · exact fiber7Projection_units
  · intro j
    fin_cases j
    · exact h252Fiber7Pointc1_isUnit _ fiber7Projection_factor_zero
    · exact h252Fiber7Pointc2_isUnit _ fiber7Projection_factor_zero
    · exact h252Fiber7Pointc3_isUnit _ fiber7Projection_factor_zero
    · exact h252Fiber7Pointc4_isUnit _ fiber7Projection_factor_zero

def h252Fiber7PhaseCertificateCoordinateScales : Fin 4 → ℤ := fun _ => h252Fiber7PointScale
def h252Fiber7PhaseCertificateCoordinateNumerators : Fin 4 → List ℤ :=
  ![h252Fiber7Pointc1Coeffs,h252Fiber7Pointc2Coeffs,h252Fiber7Pointc3Coeffs,h252Fiber7Pointc4Coeffs]
def h252Fiber7PhaseCertificateCoordinateRemainders (j : Fin 4) : List ℤ :=
  integerCoefficientScale (-1) (h252Fiber7PhaseCertificateCoordinateNumerators j)
theorem h252Fiber7PhaseCertificateCoordinate_positive : ∀ j, 0 < h252Fiber7PhaseCertificateCoordinateScales j := by
  intro j
  exact h252Fiber7PointScale_pos
theorem h252Fiber7PhaseCertificateCoordinate_projected (j : Fin 4) :
    h252FiberProjection 6 *
      ((h252Fiber7PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) *
        h252FiberCoordinateValues (j.castAdd 5) +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber7PhaseCertificateCoordinateRemainders j)) = 0 := by
  rw [h252FiberCoordinateValues_phase]
  have hz : fiber7ProjectionMk
      ((h252Fiber7PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) * h252LocalizedPhaseVars j.castSucc +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber7PhaseCertificateCoordinateRemainders j)) = 0 := by
    have he := integerCoefficientEval_map (R := H252LocalizedTorusAlgebra) (S := Fiber7ProjectionAlgebra) fiber7ProjectionMk (h252LocalizedTorusVar 4) (h252Fiber7PhaseCertificateCoordinateRemainders j)
    rw [map_add, map_mul, map_intCast, he]
    rw [h252Fiber7PhaseCertificateCoordinateRemainders, integerCoefficientEval_scale]
    simp only [Int.cast_neg, Int.cast_one]
    have h := fiber7Projection_phase_values j
    fin_cases j
    · change (h252Fiber7PointScale : Fiber7ProjectionAlgebra) * fiber7ProjectionVar 0 + (-1 : Fiber7ProjectionAlgebra) *
          integerCoefficientEval (fiber7ProjectionVar 4) h252Fiber7Pointc1Coeffs = 0
      change fiber7ProjectionVar 0 = h252Fiber7Pointc1 (fiber7ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber7ProjectionAlgebra) (fiber7ProjectionVar 4) h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos) h252Fiber7Pointc1Coeffs
      change (h252Fiber7PointScale : Fiber7ProjectionAlgebra) * h252Fiber7Pointc1 (fiber7ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber7PointScale : Fiber7ProjectionAlgebra) * fiber7ProjectionVar 1 + (-1 : Fiber7ProjectionAlgebra) *
          integerCoefficientEval (fiber7ProjectionVar 4) h252Fiber7Pointc2Coeffs = 0
      change fiber7ProjectionVar 1 = h252Fiber7Pointc2 (fiber7ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber7ProjectionAlgebra) (fiber7ProjectionVar 4) h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos) h252Fiber7Pointc2Coeffs
      change (h252Fiber7PointScale : Fiber7ProjectionAlgebra) * h252Fiber7Pointc2 (fiber7ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber7PointScale : Fiber7ProjectionAlgebra) * fiber7ProjectionVar 2 + (-1 : Fiber7ProjectionAlgebra) *
          integerCoefficientEval (fiber7ProjectionVar 4) h252Fiber7Pointc3Coeffs = 0
      change fiber7ProjectionVar 2 = h252Fiber7Pointc3 (fiber7ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber7ProjectionAlgebra) (fiber7ProjectionVar 4) h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos) h252Fiber7Pointc3Coeffs
      change (h252Fiber7PointScale : Fiber7ProjectionAlgebra) * h252Fiber7Pointc3 (fiber7ProjectionVar 4) = _ at hs
      linear_combination hs
    · change (h252Fiber7PointScale : Fiber7ProjectionAlgebra) * fiber7ProjectionVar 3 + (-1 : Fiber7ProjectionAlgebra) *
          integerCoefficientEval (fiber7ProjectionVar 4) h252Fiber7Pointc4Coeffs = 0
      change fiber7ProjectionVar 3 = h252Fiber7Pointc4 (fiber7ProjectionVar 4) at h
      rw [h]
      have hs := torusScaledRationalValue_scaled (R := Fiber7ProjectionAlgebra) (fiber7ProjectionVar 4) h252Fiber7PointScale (ne_of_gt h252Fiber7PointScale_pos) h252Fiber7Pointc4Coeffs
      change (h252Fiber7PointScale : Fiber7ProjectionAlgebra) * h252Fiber7Pointc4 (fiber7ProjectionVar 4) = _ at hs
      linear_combination hs
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end
end Biunimodular.F11
