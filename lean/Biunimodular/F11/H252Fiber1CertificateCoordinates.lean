/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber1CertificateCoordinateCheck
import Biunimodular.F11.H252Fiber1CertificateMembership
import Biunimodular.F11.TorusFiberCoordinateValues

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
noncomputable section
theorem h252Fiber1CertificateCoordinate_projected (i : Fin 9) :
    h252FiberProjection 0 *
      ((h252Fiber1CertificateCoordinateScales i : H252LocalizedTorusAlgebra) * h252FiberCoordinateValues i +
        integerCoefficientEval (h252LocalizedTorusVar 4) (h252Fiber1CertificateCoordinateRemainders i)) = 0 := by
  have hm := h252Fiber1Certificate_mem_projection (h252Fiber1CertificateCoordinateIndices i) (h252Fiber1CertificateCoordinate_bounds i)
  rw [torusFiberProjection_mem_iff] at hm
  rw [torusFiberLinearCheck_sound _ _ _ _ (h252Fiber1CertificateCoordinate_check i),
    torusFiberCoordinates_quotient_eval] at hm
  exact hm
end

end Biunimodular.F11
