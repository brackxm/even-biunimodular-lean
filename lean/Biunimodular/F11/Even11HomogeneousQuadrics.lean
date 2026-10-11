/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceHomogeneousQuadrics
import Biunimodular.F11.Even11PrincipalMinorCertificate

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

def even11FixedSliceHomogeneousGenerators : List (MvPolynomial (Fin 6) ℂ) :=
  fixedSliceHomogeneousGenerators even11FourierNormalized

theorem even11FixedSliceHomogeneousGenerators_length :
    even11FixedSliceHomogeneousGenerators.length = 5 :=
  fixedSliceHomogeneousGenerators_length _

theorem even11FixedSliceHomogeneousGenerators_quadratic :
    ∀ p ∈ even11FixedSliceHomogeneousGenerators, p.IsHomogeneous 2 :=
  fixedSliceHomogeneousGenerators_isHomogeneous _

theorem even11FixedSliceHomogeneousBoundary_zeroLocus :
    MvPolynomial.zeroLocus ℂ
      (fixedSliceHomogeneousBoundaryIdeal even11FourierNormalized) = {0} :=
  fixedSliceHomogeneousBoundary_zeroLocus _
    even11_normalized_noDisjointFourierSupport_certified

/-- The concrete normalized Fourier slice has no boundary prime in projective space. -/
theorem even11FixedSliceHomogeneous_prime_chart
    (P : Ideal (MvPolynomial (Fin 6) ℂ)) (hP : P.IsPrime)
    (heq : ∀ j : Fin 6, fixedSliceHomogeneousQuadric even11FourierNormalized j ∈ P)
    (hrelevant : ∃ j : Fin 6, (MvPolynomial.X j : MvPolynomial (Fin 6) ℂ) ∉ P) :
    (MvPolynomial.X 0 : MvPolynomial (Fin 6) ℂ) ∉ P :=
  fixedSliceHomogeneous_prime_chart _
    even11_normalized_noDisjointFourierSupport_certified P hP heq hrelevant

end
end Biunimodular.F11
