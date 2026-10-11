/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber2LaurentRankCoordinates
import Biunimodular.F11.H252FiberPhaseReconstruction
import Biunimodular.F11.TorusFiberProjectionMembership

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

private def gaussianProjectionIdeal : Ideal H252LocalizedTorusAlgebra :=
  algebraProjectionIdeal (RingHom.id _) (h252FiberProjection 1)

private abbrev GaussianProjectionAlgebra := H252LocalizedTorusAlgebra ⧸ gaussianProjectionIdeal

private def gaussianProjectionMk : H252LocalizedTorusAlgebra →+* GaussianProjectionAlgebra :=
  Ideal.Quotient.mk gaussianProjectionIdeal

private def gaussianProjectionVar (i : Fin 7) : GaussianProjectionAlgebra :=
  gaussianProjectionMk (h252LocalizedTorusVar i)

private theorem gaussianProjection_factor_zero :
    integerCoefficientEval (gaussianProjectionVar 4) [1,1,1,1,1,1,1,1,1,1,1] = 0 := by
  change integerCoefficientEval (gaussianProjectionMk (h252LocalizedTorusVar 4)) _ = 0
  rw [← integerCoefficientEval_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change h252FiberProjection 1 *
    integerCoefficientEval (h252LocalizedTorusVar 4) [1,1,1,1,1,1,1,1,1,1,1] = 0
  exact h252FiberProjection_annihilator 1

private theorem gaussianProjection_generators_zero :
    ∀ g ∈ h252Fiber2LaurentRankOriginalGenerators,
      rurInverseSparseEval g (gaussianProjectionVar 0) (gaussianProjectionVar 1)
        (gaussianProjectionVar 2) (gaussianProjectionVar 3) (gaussianProjectionVar 5)
        (gaussianProjectionVar 4) (gaussianProjectionVar 6) = 0 := by
  intro g hg
  have hz : rurInverseSparseEval g (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1)
      (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5)
      (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
    simp only [h252Fiber2LaurentRankOriginalGenerators, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact rurInverseGenerator1_quotient_zero
    · exact rurInverseGenerator2_quotient_zero
    · exact rurInverseGenerator3_quotient_zero
    · exact rurInverseGenerator4_quotient_zero
    · exact rurInverseGenerator5_quotient_zero
  change rurInverseSparseEval g (gaussianProjectionMk _) (gaussianProjectionMk _)
    (gaussianProjectionMk _) (gaussianProjectionMk _) (gaussianProjectionMk _)
    (gaussianProjectionMk _) (gaussianProjectionMk _) = 0
  rw [← rurInverseSparseEval_map, hz, map_zero]

private theorem localizedPhaseVar_isUnit (i : Fin 5) : IsUnit (h252LocalizedPhaseVars i) :=
  isUnit_iff_exists_inv.mpr ⟨h252LocalizedInverseVars i, h252LocalizedPhaseVars_units i⟩

private theorem gaussianProjection_units : ∀ j : Fin 4,
    IsUnit (![gaussianProjectionVar 0,gaussianProjectionVar 1,
      gaussianProjectionVar 2,gaussianProjectionVar 3] j) := by
  intro j
  have hu := (localizedPhaseVar_isUnit j.castSucc).map gaussianProjectionMk
  fin_cases j <;> exact hu

theorem h252Fiber2PhaseCertificate_phase_projected (j : Fin 4) :
    h252FiberProjection 1 * (h252LocalizedPhaseVars j.castSucc -
      (h252LocalizedTorusVar 4) ^ h252Fiber2LaurentRankCoordinatePowers j) = 0 := by
  have h := h252Fiber2LaurentRank_phase_coordinates
    (gaussianProjectionVar 0) (gaussianProjectionVar 1) (gaussianProjectionVar 2)
    (gaussianProjectionVar 3) (gaussianProjectionVar 5) (gaussianProjectionVar 4)
    (gaussianProjectionVar 6) gaussianProjection_factor_zero
    gaussianProjection_generators_zero gaussianProjection_units j
  have hz : gaussianProjectionMk (h252LocalizedPhaseVars j.castSucc -
      (h252LocalizedTorusVar 4) ^ h252Fiber2LaurentRankCoordinatePowers j) = 0 := by
    rw [map_sub, map_pow]
    apply sub_eq_zero.mpr
    fin_cases j <;> exact h
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact hm

def h252Fiber2PhaseCertificateCoordinateScales : Fin 4 → ℤ := fun _ => 1

def h252Fiber2PhaseCertificateCoordinateRemainders : Fin 4 → List ℤ :=
  ![[0,0,0,0,-1], [0,0,0,0,0,-1], [0,0,0,-1], [0,0,0,0,0,0,0,0,0,-1]]

theorem h252Fiber2PhaseCertificateCoordinate_positive :
    ∀ j, 0 < h252Fiber2PhaseCertificateCoordinateScales j := by native_decide

theorem h252Fiber2PhaseCertificateCoordinate_projected (j : Fin 4) :
    h252FiberProjection 1 *
      ((h252Fiber2PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) *
        h252FiberCoordinateValues (j.castAdd 5) +
        integerCoefficientEval (h252LocalizedTorusVar 4)
          (h252Fiber2PhaseCertificateCoordinateRemainders j)) = 0 := by
  rw [h252FiberCoordinateValues_phase]
  have he : (h252Fiber2PhaseCertificateCoordinateScales j : H252LocalizedTorusAlgebra) *
      h252LocalizedPhaseVars j.castSucc + integerCoefficientEval (h252LocalizedTorusVar 4)
        (h252Fiber2PhaseCertificateCoordinateRemainders j) =
      h252LocalizedPhaseVars j.castSucc -
        (h252LocalizedTorusVar 4) ^ h252Fiber2LaurentRankCoordinatePowers j := by
    fin_cases j <;>
      simp [h252Fiber2PhaseCertificateCoordinateScales,
        h252Fiber2PhaseCertificateCoordinateRemainders, h252Fiber2LaurentRankCoordinatePowers,
        integerCoefficientEval] <;> ring
  rw [he]
  exact h252Fiber2PhaseCertificate_phase_projected j

end
end Biunimodular.F11
