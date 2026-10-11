/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurParametrization

set_option autoImplicit false
namespace Biunimodular.F11.Results
noncomputable section

/-- Unconditional reverse RUR memberships in the original localized ideal. -/
theorem localizedTorus_reverse_rur_mem (i : Fin 6) :
    integerCoefficientEval (MvPolynomial.X (6 : Fin 7)) h252RurDCoeffs *
        MvPolynomial.X i.castSucc -
      integerCoefficientEval (MvPolynomial.X (6 : Fin 7))
        (h252RurNumeratorCoefficients i) ∈ h252LocalizedTorusIdeal :=
  h252LocalizedTorus_reverse_rur_mem i

/-- Every solution of the original localized system is given by one and only
one root of the displayed degree-252 eliminant. -/
theorem localizedTorus_solution_unique (z : Fin 7 → ℂ)
    (hz : ∀ i, MvPolynomial.aeval z (h252LocalizedTorusGenerators i) = 0) :
    ∃! x : ℂ, h252RurComplexPolynomial.IsRoot x ∧ z = h252RurTorusPoint x :=
  h252LocalizedTorus_solution_unique z hz

end
end Biunimodular.F11.Results
