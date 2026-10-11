/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252ComplexPhaseExhaustionCriterion
import Biunimodular.F11.SplitPolynomialFunctionAlgebra
import Biunimodular.F11.EtaleSquarePresentation
import Mathlib.RingTheory.Etale.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section

/-- Evaluation identifies the coordinate algebra with functions on all
252 simple complex roots of the actual eliminant. -/
def h252UnivariateCoordinateEquivFunctions :
    H252UnivariateCoordinateAlgebra ≃ₐ[ℂ] (h252KComplex.rootSet ℂ → ℂ) :=
  splitPolynomialAlgebraEquivFunctions h252KComplex h252KComplex_separable

instance h252UnivariateCoordinateAlgebra_etale :
    Algebra.Etale ℂ H252UnivariateCoordinateAlgebra :=
  Algebra.Etale.of_equiv h252UnivariateCoordinateEquivFunctions.symm

theorem h252ComplexPhase_etale_of_surjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate) :
    Algebra.Etale ℂ H252ComplexPhaseAlgebra :=
  Algebra.Etale.of_equiv (h252ComplexPhaseEquivOfSurjective h)

theorem h252ComplexPhase_moduleFinite_of_surjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate) :
    Module.Finite ℂ H252ComplexPhaseAlgebra := by
  let _ : Module.Finite ℂ H252UnivariateCoordinateAlgebra :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis h252KComplex_separable.ne_zero).basis
  exact Module.Finite.equiv (h252ComplexPhaseEquivOfSurjective h).toLinearEquiv

/-- A square presentation using exactly the original five circles and five
phase equations, with the original ten variables. -/
def h252ComplexPhasePrePresentation :
    Algebra.PreSubmersivePresentation ℂ H252ComplexPhaseAlgebra (Fin 10) (Fin 10) :=
  Algebra.PreSubmersivePresentation.naive (v := h252ComplexPhaseGenerators)
    _root_.id Function.injective_id

/-- Exhaustion also proves simplicity for the original equations, rather
than only for their univariate coordinate presentation. -/
theorem h252ComplexPhaseJacobian_isUnit_of_surjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate) :
    IsUnit h252ComplexPhasePrePresentation.jacobian := by
  let _ := h252ComplexPhase_etale_of_surjective h
  let _ := h252ComplexPhase_moduleFinite_of_surjective h
  let _ : IsArtinianRing H252ComplexPhaseAlgebra := IsArtinianRing.of_finite ℂ _
  let _ : IsNoetherianRing H252ComplexPhaseAlgebra := inferInstance
  exact etaleSquarePresentation_jacobian_isUnit h252ComplexPhasePrePresentation rfl

end
end Biunimodular.F11
