/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FullComplexScheme

set_option autoImplicit false
namespace Biunimodular.F11.Results
noncomputable section
/-- Unconditional exhaustion of the original complex ten-equation scheme,
assembled from all seven exact fiber certificates. -/
theorem complexPhaseAlgebra_geometry :
    IsReduced H252ComplexPhaseAlgebra ∧
      Module.finrank ℂ H252ComplexPhaseAlgebra = 252 ∧
      Nat.card (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ) = 252 ∧
      Algebra.Etale ℂ H252ComplexPhaseAlgebra ∧
      Module.Finite ℂ H252ComplexPhaseAlgebra ∧
      IsUnit h252ComplexPhasePrePresentation.jacobian :=
  h252FullComplexScheme

end
end Biunimodular.F11.Results
