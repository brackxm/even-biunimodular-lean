/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252SchemeDimensionCriterion
import Biunimodular.F11.SplitPolynomialFunctionAlgebra
import Mathlib.RingTheory.Etale.Pi

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

/-- The original localized algebra is identified with the actual RUR
coordinate algebra once its coordinate map is proved surjective. -/
def h252LocalizedTorusEquivOfSurjective
    (h : Function.Surjective h252LocalizedTorusCoordinate) :
    AdjoinRoot h252RurComplexPolynomial ≃ₐ[ℂ] H252LocalizedTorusAlgebra :=
  (Ideal.quotientEquivAlgOfEq ℂ h252LocalizedTorusCoordinate_ker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective h)

theorem h252LocalizedTorus_finrank_of_surjective
    (h : Function.Surjective h252LocalizedTorusCoordinate) :
    Module.finrank ℂ H252LocalizedTorusAlgebra = 252 := by
  rw [← (h252LocalizedTorusEquivOfSurjective h).toLinearEquiv.finrank_eq]
  exact finrank_quotient_span_eq_natDegree.trans h252RurComplexPolynomial_natDegree

theorem h252LocalizedTorus_isReduced_of_surjective
    (h : Function.Surjective h252LocalizedTorusCoordinate) :
    IsReduced H252LocalizedTorusAlgebra := by
  let _ : IsReduced (AdjoinRoot h252RurComplexPolynomial) := by
    change IsReduced (ℂ[X] ⧸ Ideal.span {h252RurComplexPolynomial})
    rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    exact (PerfectField.separable_iff_squarefree.mp
      h252RurComplexPolynomial_separable).isRadical
  exact isReduced_of_injective (h252LocalizedTorusEquivOfSurjective h).symm.toRingHom
    (h252LocalizedTorusEquivOfSurjective h).symm.injective

theorem h252LocalizedTorusIdeal_isRadical_of_surjective
    (h : Function.Surjective h252LocalizedTorusCoordinate) :
    h252LocalizedTorusIdeal.IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  exact h252LocalizedTorus_isReduced_of_surjective h

theorem h252LocalizedTorus_etale_of_surjective
    (h : Function.Surjective h252LocalizedTorusCoordinate) :
    Algebra.Etale ℂ H252LocalizedTorusAlgebra := by
  let _ : Algebra.Etale ℂ (AdjoinRoot h252RurComplexPolynomial) :=
    Algebra.Etale.of_equiv
      (splitPolynomialAlgebraEquivFunctions h252RurComplexPolynomial
        h252RurComplexPolynomial_separable).symm
  exact Algebra.Etale.of_equiv (h252LocalizedTorusEquivOfSurjective h)

theorem h252LocalizedTorus_moduleFinite_of_surjective
    (h : Function.Surjective h252LocalizedTorusCoordinate) :
    Module.Finite ℂ H252LocalizedTorusAlgebra := by
  let _ : Module.Finite ℂ (AdjoinRoot h252RurComplexPolynomial) :=
    Module.Finite.of_basis
      (AdjoinRoot.powerBasis h252RurComplexPolynomial_separable.ne_zero).basis
  exact Module.Finite.equiv (h252LocalizedTorusEquivOfSurjective h).toLinearEquiv

end
end Biunimodular.F11
