/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FiberProjectionSemantics
import Biunimodular.F11.TorusFiberGeneratorSemantics
import Biunimodular.F11.TorusSpanningCertificate

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

theorem torusFiberProjection_mem_iff (i : Fin 7) (p : List RurInverseTerm7) :
    torusSparsePolynomial p ∈ h252FiberProjectionIdeal i ↔
      h252FiberProjection i * rurInverseSparseEval p (h252LocalizedTorusVar 0)
        (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
        (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0 := by
  change h252FiberProjection i * (Ideal.Quotient.mk h252LocalizedTorusIdeal)
    (torusSparsePolynomial p) = 0 ↔ _
  rw [torusSparsePolynomial, rurInverseSparseEval_map]
  rfl

end
end Biunimodular.F11
