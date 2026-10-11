/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateSurjectivityFromDimension
import Biunimodular.F11.H252LocalizedTorusEliminationIdeal
import Biunimodular.F11.H252ComplexPhaseExhaustionCriterion

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
noncomputable section
open Polynomial

theorem h252RurComplexPolynomial_natDegree : h252RurComplexPolynomial.natDegree = 252 := by
  have hL : (h252RurOriginalLeading : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurOriginalLeading_pos
  have hD : (h252RurCommonDen : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h252RurCommonDen_pos
  have h := congrArg Polynomial.natDegree h252Rur_original_polynomial
  rw [natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hL),
    natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hD),
    natDegree_comp, natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr Complex.I_ne_zero),
    natDegree_X, mul_one, h252KComplex_degree] at h
  exact h

/-- A 252-dimensional spanning bound closes the localized coordinate map
without exporting the high-degree inverse RUR identities. -/
theorem h252LocalizedTorusCoordinate_surjective_of_dimension
    [FiniteDimensional ℂ H252LocalizedTorusAlgebra]
    (hbound : Module.finrank ℂ H252LocalizedTorusAlgebra ≤ 252) :
    Function.Surjective h252LocalizedTorusCoordinate :=
  coordinate_surjective_of_finrank_le h252LocalizedTorusCoordinate h252RurComplexPolynomial
    h252LocalizedTorusCoordinate_ker (by simpa only [h252RurComplexPolynomial_natDegree] using hbound)

theorem h252ComplexPhaseKCoordinate_surjective_of_dimension
    [FiniteDimensional ℂ H252LocalizedTorusAlgebra]
    (hbound : Module.finrank ℂ H252LocalizedTorusAlgebra ≤ 252) :
    Function.Surjective h252ComplexPhaseKCoordinate :=
  h252ComplexPhaseKCoordinate_surjective_of_torus
    (h252LocalizedTorusCoordinate_surjective_of_dimension hbound)

theorem h252ComplexPhase_scheme_of_dimension
    [FiniteDimensional ℂ H252LocalizedTorusAlgebra]
    (hbound : Module.finrank ℂ H252LocalizedTorusAlgebra ≤ 252) :
    IsReduced H252ComplexPhaseAlgebra ∧
      Module.finrank ℂ H252ComplexPhaseAlgebra = 252 ∧
      Nat.card (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ) = 252 := by
  have hs := h252ComplexPhaseKCoordinate_surjective_of_dimension hbound
  exact ⟨h252ComplexPhase_isReduced_of_surjective hs,
    h252ComplexPhase_finrank_of_surjective hs, h252ComplexPhase_point_count_of_surjective hs⟩

end
end Biunimodular.F11
