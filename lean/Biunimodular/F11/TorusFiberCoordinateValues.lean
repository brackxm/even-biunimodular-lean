/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusFiberLinearCertificate
import Biunimodular.F11.H252Z5CoordinateGeneration

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

def h252FiberCoordinateValues : Fin 9 → H252LocalizedTorusAlgebra :=
  ![h252LocalizedPhaseVars 0, h252LocalizedPhaseVars 1,
    h252LocalizedPhaseVars 2, h252LocalizedPhaseVars 3,
    h252LocalizedInverseVars 0, h252LocalizedInverseVars 1,
    h252LocalizedInverseVars 2, h252LocalizedInverseVars 3, h252LocalizedInverseVars 4]

theorem torusFiberCoordinates_quotient_eval (i : Fin 9) :
    rurInverseSparseEval (torusFiberCoordinates i) (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) =
        h252FiberCoordinateValues i := by
  fin_cases i <;>
    simp [torusFiberCoordinates, h252FiberCoordinateValues, h252LocalizedPhaseVars,
      h252LocalizedInverseVars, h252TorusCofactor, rurInverseSparseEval,
      rurInverseSparseTermEval] <;> ring

end
end Biunimodular.F11
