/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber1CertificateCoordinates
import Biunimodular.F11.H252Fiber2PhaseCertificateCoordinates
import Biunimodular.F11.H252Fiber3PhaseCertificateCoordinates
import Biunimodular.F11.H252Fiber4PhaseCertificateCoordinates
import Biunimodular.F11.H252Fiber5PhaseCertificateCoordinates
import Biunimodular.F11.H252Fiber6PhaseCertificateCoordinates
import Biunimodular.F11.H252Fiber7PhaseCertificateCoordinates
import Biunimodular.F11.H252LocalizedTorusSchemeCriterion
import Biunimodular.F11.H252ComplexPhaseEtaleCriterion

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- The seven exact fiber certificates supply all four missing phase coordinates. -/
def h252FullFiberScales : Fin 7 → Fin 4 → ℤ :=
  ![fun j => h252Fiber1CertificateCoordinateScales (j.castAdd 5),
    h252Fiber2PhaseCertificateCoordinateScales,
    h252Fiber3PhaseCertificateCoordinateScales,
    h252Fiber4PhaseCertificateCoordinateScales,
    h252Fiber5PhaseCertificateCoordinateScales,
    h252Fiber6PhaseCertificateCoordinateScales,
    h252Fiber7PhaseCertificateCoordinateScales]

def h252FullFiberRemainders : Fin 7 → Fin 4 → List ℤ :=
  ![fun j => h252Fiber1CertificateCoordinateRemainders (j.castAdd 5),
    h252Fiber2PhaseCertificateCoordinateRemainders,
    h252Fiber3PhaseCertificateCoordinateRemainders,
    h252Fiber4PhaseCertificateCoordinateRemainders,
    h252Fiber5PhaseCertificateCoordinateRemainders,
    h252Fiber6PhaseCertificateCoordinateRemainders,
    h252Fiber7PhaseCertificateCoordinateRemainders]

theorem h252LocalizedZ5Coordinate_surjective :
    Function.Surjective h252LocalizedZ5Coordinate := by
  apply h252LocalizedZ5Coordinate_surjective_of_four_fiber_relations
    h252FullFiberScales h252FullFiberRemainders
  · intro i j
    fin_cases i
    · exact ne_of_gt (h252Fiber1CertificateCoordinate_positive (j.castAdd 5))
    · exact ne_of_gt (h252Fiber2PhaseCertificateCoordinate_positive j)
    · exact ne_of_gt (h252Fiber3PhaseCertificateCoordinate_positive j)
    · exact ne_of_gt (h252Fiber4PhaseCertificateCoordinate_positive j)
    · exact ne_of_gt (h252Fiber5PhaseCertificateCoordinate_positive j)
    · exact ne_of_gt (h252Fiber6PhaseCertificateCoordinate_positive j)
    · exact ne_of_gt (h252Fiber7PhaseCertificateCoordinate_positive j)
  · intro i j
    rw [← h252FiberCoordinateValues_phase]
    fin_cases i
    · exact h252Fiber1CertificateCoordinate_projected (j.castAdd 5)
    · exact h252Fiber2PhaseCertificateCoordinate_projected j
    · exact h252Fiber3PhaseCertificateCoordinate_projected j
    · exact h252Fiber4PhaseCertificateCoordinate_projected j
    · exact h252Fiber5PhaseCertificateCoordinate_projected j
    · exact h252Fiber6PhaseCertificateCoordinate_projected j
    · exact h252Fiber7PhaseCertificateCoordinate_projected j

theorem h252LocalizedTorusCoordinate_surjective :
    Function.Surjective h252LocalizedTorusCoordinate :=
  h252LocalizedTorusCoordinate_surjective_of_z5 h252LocalizedZ5Coordinate_surjective

theorem h252ComplexPhaseKCoordinate_surjective :
    Function.Surjective h252ComplexPhaseKCoordinate :=
  h252ComplexPhaseKCoordinate_surjective_of_torus h252LocalizedTorusCoordinate_surjective

/-- The actual original ten-equation complex scheme consists of exactly
252 reduced points and is finite étale; its original square Jacobian is a unit. -/
theorem h252FullComplexScheme :
    IsReduced H252ComplexPhaseAlgebra ∧
      Module.finrank ℂ H252ComplexPhaseAlgebra = 252 ∧
      Nat.card (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ) = 252 ∧
      Algebra.Etale ℂ H252ComplexPhaseAlgebra ∧
      Module.Finite ℂ H252ComplexPhaseAlgebra ∧
      IsUnit h252ComplexPhasePrePresentation.jacobian :=
  ⟨h252ComplexPhase_isReduced_of_surjective h252ComplexPhaseKCoordinate_surjective,
    h252ComplexPhase_finrank_of_surjective h252ComplexPhaseKCoordinate_surjective,
    h252ComplexPhase_point_count_of_surjective h252ComplexPhaseKCoordinate_surjective,
    h252ComplexPhase_etale_of_surjective h252ComplexPhaseKCoordinate_surjective,
    h252ComplexPhase_moduleFinite_of_surjective h252ComplexPhaseKCoordinate_surjective,
    h252ComplexPhaseJacobian_isUnit_of_surjective h252ComplexPhaseKCoordinate_surjective⟩

theorem h252LocalizedTorusIdeal_isRadical : h252LocalizedTorusIdeal.IsRadical :=
  h252LocalizedTorusIdeal_isRadical_of_surjective h252LocalizedTorusCoordinate_surjective

theorem h252ComplexPhaseIdeal_isRadical : h252ComplexPhaseIdeal.IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  exact h252FullComplexScheme.1

end
end Biunimodular.F11
